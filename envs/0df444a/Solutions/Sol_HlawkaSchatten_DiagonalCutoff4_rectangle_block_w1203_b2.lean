-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1203_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:04:37.543657+00:00
-- url     : https://prove2.me/submissions/8fd6dde0-42e0-424e-b25c-74c0f10ab6e9

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
theorem support_rectangle_w1203_s6_0 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069014487/5000000000 : ℝ)*x 0 + (674020401/1250000000 : ℝ)*x 1 + (1316611157/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069014487/5000000000 : ℝ)^2099 ≤ (3249389019783/25000000000000 : ℝ)^1587 := by
    have hnat : (1069014487 : ℕ)^2099*25000000000000^1587 ≤ 3249389019783^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069014487 5000000000 3249389019783 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674020401/1250000000 : ℝ)^2099 ≤ (22089916451787/50000000000000 : ℝ)^1587 := by
    have hnat : (674020401 : ℕ)^2099*50000000000000^1587 ≤ 22089916451787^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674020401 1250000000 22089916451787 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316611157/2500000000 : ℝ)^2099 ≤ (83637912133/195312500000 : ℝ)^1587 := by
    have hnat : (1316611157 : ℕ)^2099*195312500000^1587 ≤ 83637912133^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316611157 2500000000 83637912133 195312500000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069014487/5000000000 : ℝ), (674020401/1250000000 : ℝ), (1316611157/2500000000 : ℝ)] ![(3249389019783/25000000000000 : ℝ), (22089916451787/50000000000000 : ℝ), (83637912133/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069014487/5000000000 : ℝ)|^2099 ≤ (3249389019783/25000000000000 : ℝ)^1587
        have hw : |(-1069014487/5000000000 : ℝ)|=(1069014487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674020401/1250000000 : ℝ)|^2099 ≤ (22089916451787/50000000000000 : ℝ)^1587
        have hw : |(674020401/1250000000 : ℝ)|=(674020401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316611157/2500000000 : ℝ)|^2099 ≤ (83637912133/195312500000 : ℝ)^1587
        have hw : |(1316611157/2500000000 : ℝ)|=(1316611157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s6_1 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (334035301/625000000 : ℝ)*x 0 + (-440356817/2000000000 : ℝ)*x 1 + (1053288923/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334035301/625000000 : ℝ)^2099 ≤ (43664759952567/100000000000000 : ℝ)^1587 := by
    have hnat : (334035301 : ℕ)^2099*100000000000000^1587 ≤ 43664759952567^1587*625000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334035301 625000000 43664759952567 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (440356817/2000000000 : ℝ)^2099 ≤ (270252583049/2000000000000 : ℝ)^1587 := by
    have hnat : (440356817 : ℕ)^2099*2000000000000^1587 ≤ 270252583049^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440356817 2000000000 270252583049 2000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053288923/2000000000 : ℝ)^2099 ≤ (1338206589759/3125000000000 : ℝ)^1587 := by
    have hnat : (1053288923 : ℕ)^2099*3125000000000^1587 ≤ 1338206589759^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053288923 2000000000 1338206589759 3125000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334035301/625000000 : ℝ), (-440356817/2000000000 : ℝ), (1053288923/2000000000 : ℝ)] ![(43664759952567/100000000000000 : ℝ), (270252583049/2000000000000 : ℝ), (1338206589759/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334035301/625000000 : ℝ)|^2099 ≤ (43664759952567/100000000000000 : ℝ)^1587
        have hw : |(334035301/625000000 : ℝ)|=(334035301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-440356817/2000000000 : ℝ)|^2099 ≤ (270252583049/2000000000000 : ℝ)^1587
        have hw : |(-440356817/2000000000 : ℝ)|=(440356817/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053288923/2000000000 : ℝ)|^2099 ≤ (1338206589759/3125000000000 : ℝ)^1587
        have hw : |(1053288923/2000000000 : ℝ)|=(1053288923/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s6_2 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5344564807/10000000000 : ℝ)*x 0 + (5266444621/10000000000 : ℝ)*x 1 + (-2201784089/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344564807/10000000000 : ℝ)^2099 ≤ (10916189963829/25000000000000 : ℝ)^1587 := by
    have hnat : (5344564807 : ℕ)^2099*25000000000000^1587 ≤ 10916189963829^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344564807 10000000000 10916189963829 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266444621/10000000000 : ℝ)^2099 ≤ (8564522187363/20000000000000 : ℝ)^1587 := by
    have hnat : (5266444621 : ℕ)^2099*20000000000000^1587 ≤ 8564522187363^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266444621 10000000000 8564522187363 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2201784089/10000000000 : ℝ)^2099 ≤ (6756314592459/50000000000000 : ℝ)^1587 := by
    have hnat : (2201784089 : ℕ)^2099*50000000000000^1587 ≤ 6756314592459^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201784089 10000000000 6756314592459 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344564807/10000000000 : ℝ), (5266444621/10000000000 : ℝ), (-2201784089/10000000000 : ℝ)] ![(10916189963829/25000000000000 : ℝ), (8564522187363/20000000000000 : ℝ), (6756314592459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344564807/10000000000 : ℝ)|^2099 ≤ (10916189963829/25000000000000 : ℝ)^1587
        have hw : |(5344564807/10000000000 : ℝ)|=(5344564807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266444621/10000000000 : ℝ)|^2099 ≤ (8564522187363/20000000000000 : ℝ)^1587
        have hw : |(5266444621/10000000000 : ℝ)|=(5266444621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2201784089/10000000000 : ℝ)|^2099 ≤ (6756314592459/50000000000000 : ℝ)^1587
        have hw : |(-2201784089/10000000000 : ℝ)|=(2201784089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s6_3 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4356137871/10000000000 : ℝ)*x 0 + (4231386461/10000000000 : ℝ)*x 1 + (1121124103/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356137871/10000000000 : ℝ)^2099 ≤ (33317170531837/100000000000000 : ℝ)^1587 := by
    have hnat : (4356137871 : ℕ)^2099*100000000000000^1587 ≤ 33317170531837^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356137871 10000000000 33317170531837 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4231386461/10000000000 : ℝ)^2099 ≤ (6412214606801/20000000000000 : ℝ)^1587 := by
    have hnat : (4231386461 : ℕ)^2099*20000000000000^1587 ≤ 6412214606801^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231386461 10000000000 6412214606801 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121124103/2500000000 : ℝ)^2099 ≤ (34621756413649/100000000000000 : ℝ)^1587 := by
    have hnat : (1121124103 : ℕ)^2099*100000000000000^1587 ≤ 34621756413649^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121124103 2500000000 34621756413649 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356137871/10000000000 : ℝ), (4231386461/10000000000 : ℝ), (1121124103/2500000000 : ℝ)] ![(33317170531837/100000000000000 : ℝ), (6412214606801/20000000000000 : ℝ), (34621756413649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356137871/10000000000 : ℝ)|^2099 ≤ (33317170531837/100000000000000 : ℝ)^1587
        have hw : |(4356137871/10000000000 : ℝ)|=(4356137871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4231386461/10000000000 : ℝ)|^2099 ≤ (6412214606801/20000000000000 : ℝ)^1587
        have hw : |(4231386461/10000000000 : ℝ)|=(4231386461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121124103/2500000000 : ℝ)|^2099 ≤ (34621756413649/100000000000000 : ℝ)^1587
        have hw : |(1121124103/2500000000 : ℝ)|=(1121124103/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s6_4 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138033791/10000000000 : ℝ)*x 0 + (1316690593/2500000000 : ℝ)*x 1 + (1347961073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138033791/10000000000 : ℝ)^2099 ≤ (6498797405143/50000000000000 : ℝ)^1587 := by
    have hnat : (2138033791 : ℕ)^2099*50000000000000^1587 ≤ 6498797405143^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138033791 10000000000 6498797405143 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316690593/2500000000 : ℝ)^2099 ≤ (21413014115179/50000000000000 : ℝ)^1587 := by
    have hnat : (1316690593 : ℕ)^2099*50000000000000^1587 ≤ 21413014115179^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316690593 2500000000 21413014115179 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347961073/2500000000 : ℝ)^2099 ≤ (22088188471749/50000000000000 : ℝ)^1587 := by
    have hnat : (1347961073 : ℕ)^2099*50000000000000^1587 ≤ 22088188471749^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347961073 2500000000 22088188471749 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138033791/10000000000 : ℝ), (1316690593/2500000000 : ℝ), (1347961073/2500000000 : ℝ)] ![(6498797405143/50000000000000 : ℝ), (21413014115179/50000000000000 : ℝ), (22088188471749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138033791/10000000000 : ℝ)|^2099 ≤ (6498797405143/50000000000000 : ℝ)^1587
        have hw : |(-2138033791/10000000000 : ℝ)|=(2138033791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316690593/2500000000 : ℝ)|^2099 ≤ (21413014115179/50000000000000 : ℝ)^1587
        have hw : |(1316690593/2500000000 : ℝ)|=(1316690593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1347961073/2500000000 : ℝ)|^2099 ≤ (22088188471749/50000000000000 : ℝ)^1587
        have hw : |(1347961073/2500000000 : ℝ)|=(1347961073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s6_5 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312573087/10000000000 : ℝ)*x 0 + (-2076384383/10000000000 : ℝ)*x 1 + (2695922163/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312573087/10000000000 : ℝ)^2099 ≤ (2165970005599/5000000000000 : ℝ)^1587 := by
    have hnat : (5312573087 : ℕ)^2099*5000000000000^1587 ≤ 2165970005599^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312573087 10000000000 2165970005599 5000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2076384383/10000000000 : ℝ)^2099 ≤ (1563027820529/12500000000000 : ℝ)^1587 := by
    have hnat : (2076384383 : ℕ)^2099*12500000000000^1587 ≤ 1563027820529^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076384383 10000000000 1563027820529 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695922163/5000000000 : ℝ)^2099 ≤ (22088188655969/50000000000000 : ℝ)^1587 := by
    have hnat : (2695922163 : ℕ)^2099*50000000000000^1587 ≤ 22088188655969^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695922163 5000000000 22088188655969 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312573087/10000000000 : ℝ), (-2076384383/10000000000 : ℝ), (2695922163/5000000000 : ℝ)] ![(2165970005599/5000000000000 : ℝ), (1563027820529/12500000000000 : ℝ), (22088188655969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312573087/10000000000 : ℝ)|^2099 ≤ (2165970005599/5000000000000 : ℝ)^1587
        have hw : |(5312573087/10000000000 : ℝ)|=(5312573087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2076384383/10000000000 : ℝ)|^2099 ≤ (1563027820529/12500000000000 : ℝ)^1587
        have hw : |(-2076384383/10000000000 : ℝ)|=(2076384383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695922163/5000000000 : ℝ)|^2099 ≤ (22088188655969/50000000000000 : ℝ)^1587
        have hw : |(2695922163/5000000000 : ℝ)|=(2695922163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s6_6 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1062514623/2000000000 : ℝ)*x 0 + (5391844303/10000000000 : ℝ)*x 1 + (-259548047/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062514623/2000000000 : ℝ)^2099 ≤ (8663880082791/20000000000000 : ℝ)^1587 := by
    have hnat : (1062514623 : ℕ)^2099*20000000000000^1587 ≤ 8663880082791^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062514623 2000000000 8663880082791 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391844303/10000000000 : ℝ)^2099 ≤ (44176377062699/100000000000000 : ℝ)^1587 := by
    have hnat : (5391844303 : ℕ)^2099*100000000000000^1587 ≤ 44176377062699^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391844303 10000000000 44176377062699 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (259548047/1250000000 : ℝ)^2099 ≤ (12504222508477/100000000000000 : ℝ)^1587 := by
    have hnat : (259548047 : ℕ)^2099*100000000000000^1587 ≤ 12504222508477^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259548047 1250000000 12504222508477 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062514623/2000000000 : ℝ), (5391844303/10000000000 : ℝ), (-259548047/1250000000 : ℝ)] ![(8663880082791/20000000000000 : ℝ), (44176377062699/100000000000000 : ℝ), (12504222508477/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062514623/2000000000 : ℝ)|^2099 ≤ (8663880082791/20000000000000 : ℝ)^1587
        have hw : |(1062514623/2000000000 : ℝ)|=(1062514623/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391844303/10000000000 : ℝ)|^2099 ≤ (44176377062699/100000000000000 : ℝ)^1587
        have hw : |(5391844303/10000000000 : ℝ)|=(5391844303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-259548047/1250000000 : ℝ)|^2099 ≤ (12504222508477/100000000000000 : ℝ)^1587
        have hw : |(-259548047/1250000000 : ℝ)|=(259548047/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s6_7 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4356147551/10000000000 : ℝ)*x 0 + (2241928333/5000000000 : ℝ)*x 1 + (4232028509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356147551/10000000000 : ℝ)^2099 ≤ (6663453690643/20000000000000 : ℝ)^1587 := by
    have hnat : (4356147551 : ℕ)^2099*20000000000000^1587 ≤ 6663453690643^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356147551 10000000000 6663453690643 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241928333/5000000000 : ℝ)^2099 ≤ (6923044815539/20000000000000 : ℝ)^1587 := by
    have hnat : (2241928333 : ℕ)^2099*20000000000000^1587 ≤ 6923044815539^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241928333 5000000000 6923044815539 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232028509/10000000000 : ℝ)^2099 ≤ (8016876861999/25000000000000 : ℝ)^1587 := by
    have hnat : (4232028509 : ℕ)^2099*25000000000000^1587 ≤ 8016876861999^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232028509 10000000000 8016876861999 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356147551/10000000000 : ℝ), (2241928333/5000000000 : ℝ), (4232028509/10000000000 : ℝ)] ![(6663453690643/20000000000000 : ℝ), (6923044815539/20000000000000 : ℝ), (8016876861999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356147551/10000000000 : ℝ)|^2099 ≤ (6663453690643/20000000000000 : ℝ)^1587
        have hw : |(4356147551/10000000000 : ℝ)|=(4356147551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241928333/5000000000 : ℝ)|^2099 ≤ (6923044815539/20000000000000 : ℝ)^1587
        have hw : |(2241928333/5000000000 : ℝ)|=(2241928333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232028509/10000000000 : ℝ)|^2099 ≤ (8016876861999/25000000000000 : ℝ)^1587
        have hw : |(4232028509/10000000000 : ℝ)|=(4232028509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1203_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5701/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5713/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14089/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5701/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5701/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5701/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7057/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5701/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5701/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7057/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5701/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5701/50000 : ℝ) ^ (8395/2048 : ℝ) ≤ (851787167440797/6250000000000000000 : ℝ) := by
    have hpowers : (5701/50000 : ℝ)^8395 ≤ (851787167440797/6250000000000000000 : ℝ)^2048 := by
      have hnat : (5701 : ℕ)^8395*6250000000000000000^2048 ≤ 851787167440797^2048*50000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5701 50000 851787167440797 6250000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5701/50000 : ℝ)) (X := (851787167440797/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7057/50000 : ℝ) ^ (8395/2048 : ℝ) ≤ (16341158629601319/50000000000000000000 : ℝ) := by
    have hpowers : (7057/50000 : ℝ)^8395 ≤ (16341158629601319/50000000000000000000 : ℝ)^2048 := by
      have hnat : (7057 : ℕ)^8395*50000000000000000000^2048 ≤ 16341158629601319^2048*50000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7057 50000 16341158629601319 50000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7057/50000 : ℝ)) (X := (16341158629601319/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125851787167440797/3125000000000000000 : ℝ) ≤ (10000664883535937/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (3125851787167440797/3125000000000000000 : ℝ)^2048 ≤ (10000664883535937/10000000000000000 : ℝ)^8395 := by
      have hnat : (3125851787167440797 : ℕ)^2048*10000000000000000^8395 ≤ 10000664883535937^8395*3125000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125851787167440797 3125000000000000000 10000664883535937 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000664883535937/10000000000000000 : ℝ)) (X := (3125851787167440797/3125000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004631091193825539/10000000000000000000 : ℝ) ≤ (5000564789446601/5000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (10004631091193825539/10000000000000000000 : ℝ)^2048 ≤ (5000564789446601/5000000000000000 : ℝ)^8395 := by
      have hnat : (10004631091193825539 : ℕ)^2048*5000000000000000^8395 ≤ 5000564789446601^8395*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004631091193825539 10000000000000000000 5000564789446601 5000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000564789446601/5000000000000000 : ℝ)) (X := (10004631091193825539/10000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016341158629601319/25000000000000000000 : ℝ) ≤ (10001594274250467/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (25016341158629601319/25000000000000000000 : ℝ)^2048 ≤ (10001594274250467/10000000000000000 : ℝ)^8395 := by
      have hnat : (25016341158629601319 : ℕ)^2048*10000000000000000^8395 ≤ 10001594274250467^8395*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016341158629601319 25000000000000000000 10001594274250467 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001594274250467/10000000000000000 : ℝ)) (X := (25016341158629601319/25000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(851787167440797/6250000000000000000 : ℝ) ≤ ((6777801562805597521/6780000000000000000 : ℝ)+2*(92939071453/54240000000000 : ℝ)*(5701/50000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (6777801562805597521/6780000000000000000 : ℝ)+2*(92939071453/54240000000000 : ℝ)*(5701/50000 : ℝ)=(10000664883535937/10000000000000000 : ℝ) by norm_num, show 1+2*(851787167440797/6250000000000000000 : ℝ)=(3125851787167440797/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16341158629601319/50000000000000000000 : ℝ)+(851787167440797/6250000000000000000 : ℝ) ≤ ((6777801562805597521/6780000000000000000 : ℝ)+(92939071453/54240000000000 : ℝ)*((7057/50000 : ℝ)+(5701/50000 : ℝ)))^(8395/2048 : ℝ) := by
    rw [show (6777801562805597521/6780000000000000000 : ℝ)+(92939071453/54240000000000 : ℝ)*((7057/50000 : ℝ)+(5701/50000 : ℝ))=(5000564789446601/5000000000000000 : ℝ) by norm_num, show 1+(16341158629601319/50000000000000000000 : ℝ)+(851787167440797/6250000000000000000 : ℝ)=(10004631091193825539/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16341158629601319/50000000000000000000 : ℝ) ≤ ((6777801562805597521/6780000000000000000 : ℝ)+2*(92939071453/54240000000000 : ℝ)*(7057/50000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (6777801562805597521/6780000000000000000 : ℝ)+2*(92939071453/54240000000000 : ℝ)*(7057/50000 : ℝ)=(10001594274250467/10000000000000000 : ℝ) by norm_num, show 1+2*(16341158629601319/50000000000000000000 : ℝ)=(25016341158629601319/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6777801562805597521/6780000000000000000 : ℝ)*(X 1 0+X 2 0)+(92939071453/54240000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (5701/50000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (6777801562805597521/6780000000000000000 : ℝ)) (alpha := (92939071453/54240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6777801562805597521/6780000000000000000 : ℝ)*(X 0 1+X 2 1)+(92939071453/54240000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (5701/50000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (6777801562805597521/6780000000000000000 : ℝ)) (alpha := (92939071453/54240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6777801562805597521/6780000000000000000 : ℝ)*(X 0 2+X 1 2)+(92939071453/54240000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (5701/50000 : ℝ)) (hi := (7057/50000 : ℝ)) (c := (6777801562805597521/6780000000000000000 : ℝ)) (alpha := (92939071453/54240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1069014487/5000000000 : ℝ)*X 0 0+(674020401/1250000000 : ℝ)*X 0 1+(1316611157/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334035301/625000000 : ℝ)*X 1 0+(-440356817/2000000000 : ℝ)*X 1 1+(1053288923/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344564807/10000000000 : ℝ)*X 2 0+(5266444621/10000000000 : ℝ)*X 2 1+(-2201784089/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356137871/10000000000 : ℝ)*X 0 0+(4231386461/10000000000 : ℝ)*X 0 1+(1121124103/2500000000 : ℝ)*X 0 2+(4356137871/10000000000 : ℝ)*X 1 0+(4231386461/10000000000 : ℝ)*X 1 1+(1121124103/2500000000 : ℝ)*X 1 2+(4356137871/10000000000 : ℝ)*X 2 0+(4231386461/10000000000 : ℝ)*X 2 1+(1121124103/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2138033791/10000000000 : ℝ)*X 0 0+(1316690593/2500000000 : ℝ)*X 0 1+(1347961073/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312573087/10000000000 : ℝ)*X 1 0+(-2076384383/10000000000 : ℝ)*X 1 1+(2695922163/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062514623/2000000000 : ℝ)*X 2 0+(5391844303/10000000000 : ℝ)*X 2 1+(-259548047/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356147551/10000000000 : ℝ)*X 0 0+(2241928333/5000000000 : ℝ)*X 0 1+(4232028509/10000000000 : ℝ)*X 0 2+(4356147551/10000000000 : ℝ)*X 1 0+(2241928333/5000000000 : ℝ)*X 1 1+(4232028509/10000000000 : ℝ)*X 1 2+(4356147551/10000000000 : ℝ)*X 2 0+(2241928333/5000000000 : ℝ)*X 2 1+(4232028509/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (454305397591697020556495903/113000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (346019401/50000000000000 : ℝ)*(base19) + (314427509/50000000000000 : ℝ)*(base23) + (3326263/12500000000000 : ℝ)*(lower2) + (44556973/50000000000000 : ℝ)*(upper3) + (4347769/10000000000000 : ℝ)*(upper5) + (2976295874751271/50000000000000 : ℝ)*(major0) + (2976295874751271/50000000000000 : ℝ)*(major1) + (5952591749502543/100000000000000 : ℝ)*(major2) + (795429347422287/10000000000000 : ℝ)*(sp0) + (7954310974086751/100000000000000 : ℝ)*(sp1) + (3977155518635267/50000000000000 : ℝ)*(sp2) + (3950861346041757/100000000000000 : ℝ)*(sp3) + (18191902683/100000000000000 : ℝ)*(sp4) + (10352824373/100000000000000 : ℝ)*(sp7) + (395087169886613/10000000000000 : ℝ)*(f.failure) + (497144479132847/6250000000000 : ℝ)*(f.sum) + (8760015578983/5424000000000000000000000000 : ℝ)*base66 + (1696203307111386691/339000000000000000000000000000000 : ℝ)*base67 + (5382132038771254097/678000000000000000000000000000000 : ℝ)*base70 + (572353930333613309/339000000000000000000000000000000 : ℝ)*base72 + (6284768793013/1084800000000000000000000000 : ℝ)*base73 + (6878829289553254097/678000000000000000000000000000000 : ℝ)*base76 + (1589498840114191397/113000000000000000000000000000000 : ℝ)*base77 + (3096569711598808603/113000000000000000000000000000000 : ℝ)*base80 + (5147417876777/1356000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (4087547/250000000000000000000 : ℝ)*base89 + (4087547/250000000000000000000 : ℝ)*base91 + (1587547/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (855313926346437768357607899/113000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1350965397/100000000000000 : ℝ)*(base19) + (749512431/50000000000000 : ℝ)*(base23) + (78661271/50000000000000 : ℝ)*(upper3) + (357641/800000000000 : ℝ)*(lower4) + (146144381/100000000000000 : ℝ)*(upper5) + (5982860736198327/100000000000000 : ℝ)*(major0) + (5982860736198327/100000000000000 : ℝ)*(major1) + (5982860736198327/100000000000000 : ℝ)*(major2) + (3926687911/10000000000000 : ℝ)*(sp1) + (5360327647/12500000000000 : ℝ)*(sp2) + (1598951860074689/20000000000000 : ℝ)*(sp4) + (3997359341264469/50000000000000 : ℝ)*(sp5) + (499669682420463/6250000000000 : ℝ)*(sp6) + (1985480959859101/50000000000000 : ℝ)*(sp7) + (1985480959859101/50000000000000 : ℝ)*(f.failure) + (1598951860074689/20000000000000 : ℝ)*(f.sum) + (1861508336849/904000000000000000000000000 : ℝ)*base65 + (4602986983923640789/226000000000000000000000000000000 : ℝ)*base67 + (4510552828887640789/226000000000000000000000000000000 : ℝ)*base69 + (980916037227640789/226000000000000000000000000000000 : ℝ)*base71 + (193629745707/180800000000000000000000000 : ℝ)*base74 + (12757299044339640789/226000000000000000000000000000000 : ℝ)*base75 + (1349724626791640789/226000000000000000000000000000000 : ℝ)*base77 + (1464606484043640789/226000000000000000000000000000000 : ℝ)*base79 + (7613705684007/904000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (5819219/1250000000000000000000 : ℝ)*base89 + (5819219/1250000000000000000000 : ℝ)*base91 + (5819219/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1203_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5701/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1203_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1203_s7_0 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138049031/10000000000 : ℝ)*x 0 + (269596279/500000000 : ℝ)*x 1 + (329166817/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138049031/10000000000 : ℝ)^2099 ≤ (1624714668487/12500000000000 : ℝ)^1587 := by
    have hnat : (2138049031 : ℕ)^2099*12500000000000^1587 ≤ 1624714668487^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138049031 10000000000 1624714668487 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269596279/500000000 : ℝ)^2099 ≤ (4417725782149/10000000000000 : ℝ)^1587 := by
    have hnat : (269596279 : ℕ)^2099*10000000000000^1587 ≤ 4417725782149^1587*500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269596279 500000000 4417725782149 10000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329166817/625000000 : ℝ)^2099 ≤ (42825024816743/100000000000000 : ℝ)^1587 := by
    have hnat : (329166817 : ℕ)^2099*100000000000000^1587 ≤ 42825024816743^1587*625000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329166817 625000000 42825024816743 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138049031/10000000000 : ℝ), (269596279/500000000 : ℝ), (329166817/625000000 : ℝ)] ![(1624714668487/12500000000000 : ℝ), (4417725782149/10000000000000 : ℝ), (42825024816743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138049031/10000000000 : ℝ)|^2099 ≤ (1624714668487/12500000000000 : ℝ)^1587
        have hw : |(-2138049031/10000000000 : ℝ)|=(2138049031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269596279/500000000 : ℝ)|^2099 ≤ (4417725782149/10000000000000 : ℝ)^1587
        have hw : |(269596279/500000000 : ℝ)|=(269596279/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329166817/625000000 : ℝ)|^2099 ≤ (42825024816743/100000000000000 : ℝ)^1587
        have hw : |(329166817/625000000 : ℝ)|=(329166817/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s7_1 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (133612621/250000000 : ℝ)*x 0 + (-1100783189/5000000000 : ℝ)*x 1 + (526666919/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133612621/250000000 : ℝ)^2099 ≤ (21832055934543/50000000000000 : ℝ)^1587 := by
    have hnat : (133612621 : ℕ)^2099*50000000000000^1587 ≤ 21832055934543^1587*250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133612621 250000000 21832055934543 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1100783189/5000000000 : ℝ)^2099 ≤ (1688857754023/12500000000000 : ℝ)^1587 := by
    have hnat : (1100783189 : ℕ)^2099*12500000000000^1587 ≤ 1688857754023^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1100783189 5000000000 1688857754023 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526666919/1000000000 : ℝ)^2099 ≤ (21412513042897/50000000000000 : ℝ)^1587 := by
    have hnat : (526666919 : ℕ)^2099*50000000000000^1587 ≤ 21412513042897^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526666919 1000000000 21412513042897 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133612621/250000000 : ℝ), (-1100783189/5000000000 : ℝ), (526666919/1000000000 : ℝ)] ![(21832055934543/50000000000000 : ℝ), (1688857754023/12500000000000 : ℝ), (21412513042897/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133612621/250000000 : ℝ)|^2099 ≤ (21832055934543/50000000000000 : ℝ)^1587
        have hw : |(133612621/250000000 : ℝ)|=(133612621/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1100783189/5000000000 : ℝ)|^2099 ≤ (1688857754023/12500000000000 : ℝ)^1587
        have hw : |(-1100783189/5000000000 : ℝ)|=(1100783189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526666919/1000000000 : ℝ)|^2099 ≤ (21412513042897/50000000000000 : ℝ)^1587
        have hw : |(526666919/1000000000 : ℝ)|=(526666919/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s7_2 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (42756039/80000000 : ℝ)*x 0 + (5266669099/10000000000 : ℝ)*x 1 + (-550391613/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42756039/80000000 : ℝ)^2099 ≤ (8732822449457/20000000000000 : ℝ)^1587 := by
    have hnat : (42756039 : ℕ)^2099*20000000000000^1587 ≤ 8732822449457^1587*80000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42756039 80000000 8732822449457 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266669099/10000000000 : ℝ)^2099 ≤ (42825025107119/100000000000000 : ℝ)^1587 := by
    have hnat : (5266669099 : ℕ)^2099*100000000000000^1587 ≤ 42825025107119^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266669099 10000000000 42825025107119 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (550391613/2500000000 : ℝ)^2099 ≤ (13510862632829/100000000000000 : ℝ)^1587 := by
    have hnat : (550391613 : ℕ)^2099*100000000000000^1587 ≤ 13510862632829^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      550391613 2500000000 13510862632829 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42756039/80000000 : ℝ), (5266669099/10000000000 : ℝ), (-550391613/2500000000 : ℝ)] ![(8732822449457/20000000000000 : ℝ), (42825025107119/100000000000000 : ℝ), (13510862632829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42756039/80000000 : ℝ)|^2099 ≤ (8732822449457/20000000000000 : ℝ)^1587
        have hw : |(42756039/80000000 : ℝ)|=(42756039/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266669099/10000000000 : ℝ)|^2099 ≤ (42825025107119/100000000000000 : ℝ)^1587
        have hw : |(5266669099/10000000000 : ℝ)|=(5266669099/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-550391613/2500000000 : ℝ)|^2099 ≤ (13510862632829/100000000000000 : ℝ)^1587
        have hw : |(-550391613/2500000000 : ℝ)|=(550391613/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s7_3 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (17424599/40000000 : ℝ)*x 0 + (528981261/1250000000 : ℝ)*x 1 + (4484029611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17424599/40000000 : ℝ)^2099 ≤ (2082330668623/6250000000000 : ℝ)^1587 := by
    have hnat : (17424599 : ℕ)^2099*6250000000000^1587 ≤ 2082330668623^1587*40000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17424599 40000000 2082330668623 6250000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (528981261/1250000000 : ℝ)^2099 ≤ (32065719334229/100000000000000 : ℝ)^1587 := by
    have hnat : (528981261 : ℕ)^2099*100000000000000^1587 ≤ 32065719334229^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528981261 1250000000 32065719334229 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484029611/10000000000 : ℝ)^2099 ≤ (34616989959577/100000000000000 : ℝ)^1587 := by
    have hnat : (4484029611 : ℕ)^2099*100000000000000^1587 ≤ 34616989959577^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484029611 10000000000 34616989959577 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17424599/40000000 : ℝ), (528981261/1250000000 : ℝ), (4484029611/10000000000 : ℝ)] ![(2082330668623/6250000000000 : ℝ), (32065719334229/100000000000000 : ℝ), (34616989959577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17424599/40000000 : ℝ)|^2099 ≤ (2082330668623/6250000000000 : ℝ)^1587
        have hw : |(17424599/40000000 : ℝ)|=(17424599/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(528981261/1250000000 : ℝ)|^2099 ≤ (32065719334229/100000000000000 : ℝ)^1587
        have hw : |(528981261/1250000000 : ℝ)|=(528981261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484029611/10000000000 : ℝ)|^2099 ≤ (34616989959577/100000000000000 : ℝ)^1587
        have hw : |(4484029611/10000000000 : ℝ)|=(4484029611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s7_4 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2138053769/10000000000 : ℝ)*x 0 + (5266984539/10000000000 : ℝ)*x 1 + (215664359/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2138053769/10000000000 : ℝ)^2099 ≤ (3249438860991/25000000000000 : ℝ)^1587 := by
    have hnat : (2138053769 : ℕ)^2099*25000000000000^1587 ≤ 3249438860991^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138053769 10000000000 3249438860991 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266984539/10000000000 : ℝ)^2099 ≤ (5353552199141/12500000000000 : ℝ)^1587 := by
    have hnat : (5266984539 : ℕ)^2099*12500000000000^1587 ≤ 5353552199141^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266984539 10000000000 5353552199141 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215664359/400000000 : ℝ)^2099 ≤ (5521728369163/12500000000000 : ℝ)^1587 := by
    have hnat : (215664359 : ℕ)^2099*12500000000000^1587 ≤ 5521728369163^1587*400000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215664359 400000000 5521728369163 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2138053769/10000000000 : ℝ), (5266984539/10000000000 : ℝ), (215664359/400000000 : ℝ)] ![(3249438860991/25000000000000 : ℝ), (5353552199141/12500000000000 : ℝ), (5521728369163/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2138053769/10000000000 : ℝ)|^2099 ≤ (3249438860991/25000000000000 : ℝ)^1587
        have hw : |(-2138053769/10000000000 : ℝ)|=(2138053769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266984539/10000000000 : ℝ)|^2099 ≤ (5353552199141/12500000000000 : ℝ)^1587
        have hw : |(5266984539/10000000000 : ℝ)|=(5266984539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215664359/400000000 : ℝ)|^2099 ≤ (5521728369163/12500000000000 : ℝ)^1587
        have hw : |(215664359/400000000 : ℝ)|=(215664359/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s7_5 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (332039417/625000000 : ℝ)*x 0 + (-415325321/2000000000 : ℝ)*x 1 + (2695804487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332039417/625000000 : ℝ)^2099 ≤ (43320021157107/100000000000000 : ℝ)^1587 := by
    have hnat : (332039417 : ℕ)^2099*100000000000000^1587 ≤ 43320021157107^1587*625000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332039417 625000000 43320021157107 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (415325321/2000000000 : ℝ)^2099 ≤ (12506151892871/100000000000000 : ℝ)^1587 := by
    have hnat : (415325321 : ℕ)^2099*100000000000000^1587 ≤ 12506151892871^1587*2000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      415325321 2000000000 12506151892871 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695804487/5000000000 : ℝ)^2099 ≤ (44173826942467/100000000000000 : ℝ)^1587 := by
    have hnat : (2695804487 : ℕ)^2099*100000000000000^1587 ≤ 44173826942467^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695804487 5000000000 44173826942467 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332039417/625000000 : ℝ), (-415325321/2000000000 : ℝ), (2695804487/5000000000 : ℝ)] ![(43320021157107/100000000000000 : ℝ), (12506151892871/100000000000000 : ℝ), (44173826942467/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332039417/625000000 : ℝ)|^2099 ≤ (43320021157107/100000000000000 : ℝ)^1587
        have hw : |(332039417/625000000 : ℝ)|=(332039417/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-415325321/2000000000 : ℝ)|^2099 ≤ (12506151892871/100000000000000 : ℝ)^1587
        have hw : |(-415325321/2000000000 : ℝ)|=(415325321/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695804487/5000000000 : ℝ)|^2099 ≤ (44173826942467/100000000000000 : ℝ)^1587
        have hw : |(2695804487/5000000000 : ℝ)|=(2695804487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s7_6 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (332039417/625000000 : ℝ)*x 0 + (5391608973/10000000000 : ℝ)*x 1 + (-519156651/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332039417/625000000 : ℝ)^2099 ≤ (43320021157107/100000000000000 : ℝ)^1587 := by
    have hnat : (332039417 : ℕ)^2099*100000000000000^1587 ≤ 43320021157107^1587*625000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332039417 625000000 43320021157107 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5391608973/10000000000 : ℝ)^2099 ≤ (44173826931631/100000000000000 : ℝ)^1587 := by
    have hnat : (5391608973 : ℕ)^2099*100000000000000^1587 ≤ 44173826931631^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391608973 10000000000 44173826931631 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519156651/2500000000 : ℝ)^2099 ≤ (6253075942453/50000000000000 : ℝ)^1587 := by
    have hnat : (519156651 : ℕ)^2099*50000000000000^1587 ≤ 6253075942453^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519156651 2500000000 6253075942453 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332039417/625000000 : ℝ), (5391608973/10000000000 : ℝ), (-519156651/2500000000 : ℝ)] ![(43320021157107/100000000000000 : ℝ), (44173826931631/100000000000000 : ℝ), (6253075942453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332039417/625000000 : ℝ)|^2099 ≤ (43320021157107/100000000000000 : ℝ)^1587
        have hw : |(332039417/625000000 : ℝ)|=(332039417/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5391608973/10000000000 : ℝ)|^2099 ≤ (44173826931631/100000000000000 : ℝ)^1587
        have hw : |(5391608973/10000000000 : ℝ)|=(5391608973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-519156651/2500000000 : ℝ)|^2099 ≤ (6253075942453/50000000000000 : ℝ)^1587
        have hw : |(-519156651/2500000000 : ℝ)|=(519156651/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s7_7 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4356159179/10000000000 : ℝ)*x 0 + (140106081/312500000 : ℝ)*x 1 + (4232487529/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356159179/10000000000 : ℝ)^2099 ≤ (33317386080353/100000000000000 : ℝ)^1587 := by
    have hnat : (4356159179 : ℕ)^2099*100000000000000^1587 ≤ 33317386080353^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356159179 10000000000 33317386080353 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140106081/312500000 : ℝ)^2099 ≤ (55376809771/160000000000 : ℝ)^1587 := by
    have hnat : (140106081 : ℕ)^2099*160000000000^1587 ≤ 55376809771^1587*312500000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140106081 312500000 55376809771 160000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4232487529/10000000000 : ℝ)^2099 ≤ (32072107802909/100000000000000 : ℝ)^1587 := by
    have hnat : (4232487529 : ℕ)^2099*100000000000000^1587 ≤ 32072107802909^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4232487529 10000000000 32072107802909 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356159179/10000000000 : ℝ), (140106081/312500000 : ℝ), (4232487529/10000000000 : ℝ)] ![(33317386080353/100000000000000 : ℝ), (55376809771/160000000000 : ℝ), (32072107802909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356159179/10000000000 : ℝ)|^2099 ≤ (33317386080353/100000000000000 : ℝ)^1587
        have hw : |(4356159179/10000000000 : ℝ)|=(4356159179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140106081/312500000 : ℝ)|^2099 ≤ (55376809771/160000000000 : ℝ)^1587
        have hw : |(140106081/312500000 : ℝ)|=(140106081/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4232487529/10000000000 : ℝ)|^2099 ≤ (32072107802909/100000000000000 : ℝ)^1587
        have hw : |(4232487529/10000000000 : ℝ)|=(4232487529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1203_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1143/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3521/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5713/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5713/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5713/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5713/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5713/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5713/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5713/50000 : ℝ) ^ (8395/2048 : ℝ) ≤ (2749313845599069/20000000000000000000 : ℝ) := by
    have hpowers : (5713/50000 : ℝ)^8395 ≤ (2749313845599069/20000000000000000000 : ℝ)^2048 := by
      have hnat : (5713 : ℕ)^8395*20000000000000000000^2048 ≤ 2749313845599069^2048*50000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5713 50000 2749313845599069 20000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5713/50000 : ℝ)) (X := (2749313845599069/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14089/100000 : ℝ) ^ (8395/2048 : ℝ) ≤ (32445670092450277/100000000000000000000 : ℝ) := by
    have hpowers : (14089/100000 : ℝ)^8395 ≤ (32445670092450277/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14089 : ℕ)^8395*100000000000000000000^2048 ≤ 32445670092450277^2048*100000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14089 100000 32445670092450277 100000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14089/100000 : ℝ)) (X := (32445670092450277/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002749313845599069/10000000000000000000 : ℝ) ≤ (10000670638434857/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (10002749313845599069/10000000000000000000 : ℝ)^2048 ≤ (10000670638434857/10000000000000000 : ℝ)^8395 := by
      have hnat : (10002749313845599069 : ℕ)^2048*10000000000000000^8395 ≤ 10000670638434857^8395*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002749313845599069 10000000000000000000 10000670638434857 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000670638434857/10000000000000000 : ℝ)) (X := (10002749313845599069/10000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023096119660222811/50000000000000000000 : ℝ) ≤ (10001126684830447/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (50023096119660222811/50000000000000000000 : ℝ)^2048 ≤ (10001126684830447/10000000000000000 : ℝ)^8395 := by
      have hnat : (50023096119660222811 : ℕ)^2048*10000000000000000^8395 ≤ 10001126684830447^8395*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023096119660222811 50000000000000000000 10001126684830447 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001126684830447/10000000000000000 : ℝ)) (X := (50023096119660222811/50000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032445670092450277/50000000000000000000 : ℝ) ≤ (10001582731226037/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (50032445670092450277/50000000000000000000 : ℝ)^2048 ≤ (10001582731226037/10000000000000000 : ℝ)^8395 := by
      have hnat : (50032445670092450277 : ℕ)^2048*10000000000000000^8395 ≤ 10001582731226037^8395*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032445670092450277 50000000000000000000 10001582731226037 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001582731226037/10000000000000000 : ℝ)) (X := (50032445670092450277/50000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2749313845599069/20000000000000000000 : ℝ) ≤ ((26621364337920001511/26630000000000000000 : ℝ)+2*(45604639559/26630000000000 : ℝ)*(5713/50000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (26621364337920001511/26630000000000000000 : ℝ)+2*(45604639559/26630000000000 : ℝ)*(5713/50000 : ℝ)=(10000670638434857/10000000000000000 : ℝ) by norm_num, show 1+2*(2749313845599069/20000000000000000000 : ℝ)=(10002749313845599069/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32445670092450277/100000000000000000000 : ℝ)+(2749313845599069/20000000000000000000 : ℝ) ≤ ((26621364337920001511/26630000000000000000 : ℝ)+(45604639559/26630000000000 : ℝ)*((14089/100000 : ℝ)+(5713/50000 : ℝ)))^(8395/2048 : ℝ) := by
    rw [show (26621364337920001511/26630000000000000000 : ℝ)+(45604639559/26630000000000 : ℝ)*((14089/100000 : ℝ)+(5713/50000 : ℝ))=(10001126684830447/10000000000000000 : ℝ) by norm_num, show 1+(32445670092450277/100000000000000000000 : ℝ)+(2749313845599069/20000000000000000000 : ℝ)=(50023096119660222811/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32445670092450277/100000000000000000000 : ℝ) ≤ ((26621364337920001511/26630000000000000000 : ℝ)+2*(45604639559/26630000000000 : ℝ)*(14089/100000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (26621364337920001511/26630000000000000000 : ℝ)+2*(45604639559/26630000000000 : ℝ)*(14089/100000 : ℝ)=(10001582731226037/10000000000000000 : ℝ) by norm_num, show 1+2*(32445670092450277/100000000000000000000 : ℝ)=(50032445670092450277/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26621364337920001511/26630000000000000000 : ℝ)*(X 1 0+X 2 0)+(45604639559/26630000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (5713/50000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (26621364337920001511/26630000000000000000 : ℝ)) (alpha := (45604639559/26630000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26621364337920001511/26630000000000000000 : ℝ)*(X 0 1+X 2 1)+(45604639559/26630000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (5713/50000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (26621364337920001511/26630000000000000000 : ℝ)) (alpha := (45604639559/26630000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26621364337920001511/26630000000000000000 : ℝ)*(X 0 2+X 1 2)+(45604639559/26630000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (5713/50000 : ℝ)) (hi := (14089/100000 : ℝ)) (c := (26621364337920001511/26630000000000000000 : ℝ)) (alpha := (45604639559/26630000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2138049031/10000000000 : ℝ)*X 0 0+(269596279/500000000 : ℝ)*X 0 1+(329166817/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((133612621/250000000 : ℝ)*X 1 0+(-1100783189/5000000000 : ℝ)*X 1 1+(526666919/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((42756039/80000000 : ℝ)*X 2 0+(5266669099/10000000000 : ℝ)*X 2 1+(-550391613/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((17424599/40000000 : ℝ)*X 0 0+(528981261/1250000000 : ℝ)*X 0 1+(4484029611/10000000000 : ℝ)*X 0 2+(17424599/40000000 : ℝ)*X 1 0+(528981261/1250000000 : ℝ)*X 1 1+(4484029611/10000000000 : ℝ)*X 1 2+(17424599/40000000 : ℝ)*X 2 0+(528981261/1250000000 : ℝ)*X 2 1+(4484029611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2138053769/10000000000 : ℝ)*X 0 0+(5266984539/10000000000 : ℝ)*X 0 1+(215664359/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((332039417/625000000 : ℝ)*X 1 0+(-415325321/2000000000 : ℝ)*X 1 1+(2695804487/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332039417/625000000 : ℝ)*X 2 0+(5391608973/10000000000 : ℝ)*X 2 1+(-519156651/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356159179/10000000000 : ℝ)*X 0 0+(140106081/312500000 : ℝ)*X 0 1+(4232487529/10000000000 : ℝ)*X 0 2+(4356159179/10000000000 : ℝ)*X 1 0+(140106081/312500000 : ℝ)*X 1 1+(4232487529/10000000000 : ℝ)*X 1 2+(4356159179/10000000000 : ℝ)*X 2 0+(140106081/312500000 : ℝ)*X 2 1+(4232487529/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28743556640057156095497/2663000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2289708969/100000000000000 : ℝ)*(base19) + (528794391/25000000000000 : ℝ)*(base23) + (4848861/4000000000000 : ℝ)*(lower2) + (192175957/50000000000000 : ℝ)*(upper3) + (106253811/100000000000000 : ℝ)*(upper5) + (5974624753489309/100000000000000 : ℝ)*(major0) + (5974624753489309/100000000000000 : ℝ)*(major1) + (597462475348931/10000000000000 : ℝ)*(major2) + (1995922528870281/25000000000000 : ℝ)*(sp0) + (7983751348422827/100000000000000 : ℝ)*(sp1) + (997968940369279/12500000000000 : ℝ)*(sp2) + (991364648299527/25000000000000 : ℝ)*(sp3) + (63522650671/100000000000000 : ℝ)*(sp4) + (1845792977/5000000000000 : ℝ)*(sp7) + (247843469316103/6250000000000 : ℝ)*(f.failure) + (1995938409532949/25000000000000 : ℝ)*(f.sum) + (245980443933/53260000000000000000000000 : ℝ)*base66 + (2572423071593345899/2663000000000000000000000000000000 : ℝ)*base67 + (1941416014360965259/266300000000000000000000000000000 : ℝ)*base70 + (26671057290327654101/2663000000000000000000000000000000 : ℝ)*base72 + (2303645459807/2663000000000000000000000000 : ℝ)*base73 + (633803256463934741/266300000000000000000000000000000 : ℝ)*base75 + (5566845156046654101/2663000000000000000000000000000000 : ℝ)*base78 + (40053949235757345899/2663000000000000000000000000000000 : ℝ)*base79 + (554339136067/266300000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (2122357/156250000000000000000 : ℝ)*base89 + (2122357/156250000000000000000 : ℝ)*base91 + (559857/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9899689936305749624941529781/1331500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (167683719/12500000000000 : ℝ)*(base19) + (1459182837/100000000000000 : ℝ)*(base23) + (148477879/100000000000000 : ℝ)*(upper3) + (53646541/100000000000000 : ℝ)*(lower4) + (30363219/20000000000000 : ℝ)*(upper5) + (6004823248311381/100000000000000 : ℝ)*(major0) + (6004823248311381/100000000000000 : ℝ)*(major1) + (6004823248311381/100000000000000 : ℝ)*(major2) + (37531794397/100000000000000 : ℝ)*(sp1) + (10080216443/25000000000000 : ℝ)*(sp2) + (8024107305953707/100000000000000 : ℝ)*(sp4) + (8024068432689559/100000000000000 : ℝ)*(sp5) + (4012032762952549/50000000000000 : ℝ)*(sp6) + (1992769471418013/50000000000000 : ℝ)*(sp7) + (1992769471418013/50000000000000 : ℝ)*(f.failure) + (8024107305953707/100000000000000 : ℝ)*(f.sum) + (1440980174763/532600000000000000000000000 : ℝ)*base66 + (45426728037402496691/2663000000000000000000000000000000 : ℝ)*base67 + (10203406486320496691/2663000000000000000000000000000000 : ℝ)*base69 + (23073744863231496691/2663000000000000000000000000000000 : ℝ)*base71 + (3667865543379/532600000000000000000000000 : ℝ)*base74 + (37474362435747496691/2663000000000000000000000000000000 : ℝ)*base75 + (24081239709067496691/2663000000000000000000000000000000 : ℝ)*base77 + (47494047668335496691/2663000000000000000000000000000000 : ℝ)*base79 + (610739537903/332875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2495853/1250000000000000000000 : ℝ)*base90 + (2495853/1250000000000000000000 : ℝ)*base92 + (2495853/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1203_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5713/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1203_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1203_s8_0 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1069027637/5000000000 : ℝ)*x 0 + (2695940599/5000000000 : ℝ)*x 1 + (42133673/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069027637/5000000000 : ℝ)^2099 ≤ (12997767544979/100000000000000 : ℝ)^1587 := by
    have hnat : (1069027637 : ℕ)^2099*100000000000000^1587 ≤ 12997767544979^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069027637 5000000000 12997767544979 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695940599/5000000000 : ℝ)^2099 ≤ (44176776875099/100000000000000 : ℝ)^1587 := by
    have hnat : (2695940599 : ℕ)^2099*100000000000000^1587 ≤ 44176776875099^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695940599 5000000000 44176776875099 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42133673/80000000 : ℝ)^2099 ≤ (8565091114817/20000000000000 : ℝ)^1587 := by
    have hnat : (42133673 : ℕ)^2099*20000000000000^1587 ≤ 8565091114817^1587*80000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42133673 80000000 8565091114817 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1069027637/5000000000 : ℝ), (2695940599/5000000000 : ℝ), (42133673/80000000 : ℝ)] ![(12997767544979/100000000000000 : ℝ), (44176776875099/100000000000000 : ℝ), (8565091114817/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1069027637/5000000000 : ℝ)|^2099 ≤ (12997767544979/100000000000000 : ℝ)^1587
        have hw : |(-1069027637/5000000000 : ℝ)|=(1069027637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695940599/5000000000 : ℝ)|^2099 ≤ (44176776875099/100000000000000 : ℝ)^1587
        have hw : |(2695940599/5000000000 : ℝ)|=(2695940599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42133673/80000000 : ℝ)|^2099 ≤ (8565091114817/20000000000000 : ℝ)^1587
        have hw : |(42133673/80000000 : ℝ)|=(42133673/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s8_1 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1336123189/2500000000 : ℝ)*x 0 + (-44030581/200000000 : ℝ)*x 1 + (5143271/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336123189/2500000000 : ℝ)^2099 ≤ (21831990646563/50000000000000 : ℝ)^1587 := by
    have hnat : (1336123189 : ℕ)^2099*50000000000000^1587 ≤ 21831990646563^1587*2500000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336123189 2500000000 21831990646563 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44030581/200000000 : ℝ)^2099 ≤ (13510559047747/100000000000000 : ℝ)^1587 := by
    have hnat : (44030581 : ℕ)^2099*100000000000000^1587 ≤ 13510559047747^1587*200000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44030581 200000000 13510559047747 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5143271/9765625 : ℝ)^2099 ≤ (8565091930023/20000000000000 : ℝ)^1587 := by
    have hnat : (5143271 : ℕ)^2099*20000000000000^1587 ≤ 8565091930023^1587*9765625^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5143271 9765625 8565091930023 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336123189/2500000000 : ℝ), (-44030581/200000000 : ℝ), (5143271/9765625 : ℝ)] ![(21831990646563/50000000000000 : ℝ), (13510559047747/100000000000000 : ℝ), (8565091930023/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336123189/2500000000 : ℝ)|^2099 ≤ (21831990646563/50000000000000 : ℝ)^1587
        have hw : |(1336123189/2500000000 : ℝ)|=(1336123189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44030581/200000000 : ℝ)|^2099 ≤ (13510559047747/100000000000000 : ℝ)^1587
        have hw : |(-44030581/200000000 : ℝ)|=(44030581/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5143271/9765625 : ℝ)|^2099 ≤ (8565091930023/20000000000000 : ℝ)^1587
        have hw : |(5143271/9765625 : ℝ)|=(5143271/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s8_2 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (10438463/19531250 : ℝ)*x 0 + (5266709233/10000000000 : ℝ)*x 1 + (-2201529009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10438463/19531250 : ℝ)^2099 ≤ (2728999033427/6250000000000 : ℝ)^1587 := by
    have hnat : (10438463 : ℕ)^2099*6250000000000^1587 ≤ 2728999033427^1587*19531250^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10438463 19531250 2728999033427 6250000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266709233/10000000000 : ℝ)^2099 ≤ (5353182091949/12500000000000 : ℝ)^1587 := by
    have hnat : (5266709233 : ℕ)^2099*12500000000000^1587 ≤ 5353182091949^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266709233 10000000000 5353182091949 12500000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2201529009/10000000000 : ℝ)^2099 ≤ (13510558714959/100000000000000 : ℝ)^1587 := by
    have hnat : (2201529009 : ℕ)^2099*100000000000000^1587 ≤ 13510558714959^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2201529009 10000000000 13510558714959 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10438463/19531250 : ℝ), (5266709233/10000000000 : ℝ), (-2201529009/10000000000 : ℝ)] ![(2728999033427/6250000000000 : ℝ), (5353182091949/12500000000000 : ℝ), (13510558714959/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10438463/19531250 : ℝ)|^2099 ≤ (2728999033427/6250000000000 : ℝ)^1587
        have hw : |(10438463/19531250 : ℝ)|=(10438463/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266709233/10000000000 : ℝ)|^2099 ≤ (5353182091949/12500000000000 : ℝ)^1587
        have hw : |(5266709233/10000000000 : ℝ)|=(5266709233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2201529009/10000000000 : ℝ)|^2099 ≤ (13510558714959/100000000000000 : ℝ)^1587
        have hw : |(-2201529009/10000000000 : ℝ)|=(2201529009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s8_3 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4356152161/10000000000 : ℝ)*x 0 + (2115967461/5000000000 : ℝ)*x 1 + (4483943957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356152161/10000000000 : ℝ)^2099 ≤ (6663463017457/20000000000000 : ℝ)^1587 := by
    have hnat : (4356152161 : ℕ)^2099*20000000000000^1587 ≤ 6663463017457^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356152161 10000000000 6663463017457 20000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2115967461/5000000000 : ℝ)^2099 ≤ (8016642381831/25000000000000 : ℝ)^1587 := by
    have hnat : (2115967461 : ℕ)^2099*25000000000000^1587 ≤ 8016642381831^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2115967461 5000000000 8016642381831 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4483943957/10000000000 : ℝ)^2099 ≤ (135219200677/390625000000 : ℝ)^1587 := by
    have hnat : (4483943957 : ℕ)^2099*390625000000^1587 ≤ 135219200677^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4483943957 10000000000 135219200677 390625000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356152161/10000000000 : ℝ), (2115967461/5000000000 : ℝ), (4483943957/10000000000 : ℝ)] ![(6663463017457/20000000000000 : ℝ), (8016642381831/25000000000000 : ℝ), (135219200677/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356152161/10000000000 : ℝ)|^2099 ≤ (6663463017457/20000000000000 : ℝ)^1587
        have hw : |(4356152161/10000000000 : ℝ)|=(4356152161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2115967461/5000000000 : ℝ)|^2099 ≤ (8016642381831/25000000000000 : ℝ)^1587
        have hw : |(2115967461/5000000000 : ℝ)|=(2115967461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4483943957/10000000000 : ℝ)|^2099 ≤ (135219200677/390625000000 : ℝ)^1587
        have hw : |(4483943957/10000000000 : ℝ)|=(4483943957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s8_4 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-267257519/1250000000 : ℝ)*x 0 + (5267024669/10000000000 : ℝ)*x 1 + (539156441/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267257519/1250000000 : ℝ)^2099 ≤ (12997806766759/100000000000000 : ℝ)^1587 := by
    have hnat : (267257519 : ℕ)^2099*100000000000000^1587 ≤ 12997806766759^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267257519 1250000000 12997806766759 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5267024669/10000000000 : ℝ)^2099 ≤ (42828849186921/100000000000000 : ℝ)^1587 := by
    have hnat : (5267024669 : ℕ)^2099*100000000000000^1587 ≤ 42828849186921^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5267024669 10000000000 42828849186921 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539156441/1000000000 : ℝ)^2099 ≤ (22086672016491/50000000000000 : ℝ)^1587 := by
    have hnat : (539156441 : ℕ)^2099*50000000000000^1587 ≤ 22086672016491^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539156441 1000000000 22086672016491 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267257519/1250000000 : ℝ), (5267024669/10000000000 : ℝ), (539156441/1000000000 : ℝ)] ![(12997806766759/100000000000000 : ℝ), (42828849186921/100000000000000 : ℝ), (22086672016491/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267257519/1250000000 : ℝ)|^2099 ≤ (12997806766759/100000000000000 : ℝ)^1587
        have hw : |(-267257519/1250000000 : ℝ)|=(267257519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5267024669/10000000000 : ℝ)|^2099 ≤ (42828849186921/100000000000000 : ℝ)^1587
        have hw : |(5267024669/10000000000 : ℝ)|=(5267024669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539156441/1000000000 : ℝ)|^2099 ≤ (22086672016491/50000000000000 : ℝ)^1587
        have hw : |(539156441/1000000000 : ℝ)|=(539156441/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s8_5 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (531263997/1000000000 : ℝ)*x 0 + (-259584171/1250000000 : ℝ)*x 1 + (2695782673/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531263997/1000000000 : ℝ)^2099 ≤ (10830030358693/25000000000000 : ℝ)^1587 := by
    have hnat : (531263997 : ℕ)^2099*25000000000000^1587 ≤ 10830030358693^1587*1000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531263997 1000000000 10830030358693 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259584171/1250000000 : ℝ)^2099 ≤ (12506524374399/100000000000000 : ℝ)^1587 := by
    have hnat : (259584171 : ℕ)^2099*100000000000000^1587 ≤ 12506524374399^1587*1250000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259584171 1250000000 12506524374399 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695782673/5000000000 : ℝ)^2099 ≤ (22086677087879/50000000000000 : ℝ)^1587 := by
    have hnat : (2695782673 : ℕ)^2099*50000000000000^1587 ≤ 22086677087879^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695782673 5000000000 22086677087879 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(531263997/1000000000 : ℝ), (-259584171/1250000000 : ℝ), (2695782673/5000000000 : ℝ)] ![(10830030358693/25000000000000 : ℝ), (12506524374399/100000000000000 : ℝ), (22086677087879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(531263997/1000000000 : ℝ)|^2099 ≤ (10830030358693/25000000000000 : ℝ)^1587
        have hw : |(531263997/1000000000 : ℝ)|=(531263997/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-259584171/1250000000 : ℝ)|^2099 ≤ (12506524374399/100000000000000 : ℝ)^1587
        have hw : |(-259584171/1250000000 : ℝ)|=(259584171/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695782673/5000000000 : ℝ)|^2099 ≤ (22086677087879/50000000000000 : ℝ)^1587
        have hw : |(2695782673/5000000000 : ℝ)|=(2695782673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s8_6 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5312640603/10000000000 : ℝ)*x 0 + (2695782279/5000000000 : ℝ)*x 1 + (-2076673583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312640603/10000000000 : ℝ)^2099 ≤ (43320128261593/100000000000000 : ℝ)^1587 := by
    have hnat : (5312640603 : ℕ)^2099*100000000000000^1587 ≤ 43320128261593^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312640603 10000000000 43320128261593 100000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695782279/5000000000 : ℝ)^2099 ≤ (22086672818377/50000000000000 : ℝ)^1587 := by
    have hnat : (2695782279 : ℕ)^2099*50000000000000^1587 ≤ 22086672818377^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695782279 5000000000 22086672818377 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2076673583/10000000000 : ℝ)^2099 ≤ (6253263043473/50000000000000 : ℝ)^1587 := by
    have hnat : (2076673583 : ℕ)^2099*50000000000000^1587 ≤ 6253263043473^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2076673583 10000000000 6253263043473 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312640603/10000000000 : ℝ), (2695782279/5000000000 : ℝ), (-2076673583/10000000000 : ℝ)] ![(43320128261593/100000000000000 : ℝ), (22086672818377/50000000000000 : ℝ), (6253263043473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312640603/10000000000 : ℝ)|^2099 ≤ (43320128261593/100000000000000 : ℝ)^1587
        have hw : |(5312640603/10000000000 : ℝ)|=(5312640603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695782279/5000000000 : ℝ)|^2099 ≤ (22086672818377/50000000000000 : ℝ)^1587
        have hw : |(2695782279/5000000000 : ℝ)|=(2695782279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2076673583/10000000000 : ℝ)|^2099 ≤ (6253263043473/50000000000000 : ℝ)^1587
        have hw : |(-2076673583/10000000000 : ℝ)|=(2076673583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1203_s8_7 (p : ℝ) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4356161183/10000000000 : ℝ)*x 0 + (2241655139/5000000000 : ℝ)*x 1 + (21162857/50000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4356161183/10000000000 : ℝ)^2099 ≤ (8329351588133/25000000000000 : ℝ)^1587 := by
    have hnat : (4356161183 : ℕ)^2099*25000000000000^1587 ≤ 8329351588133^1587*10000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4356161183 10000000000 8329351588133 25000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2241655139/5000000000 : ℝ)^2099 ≤ (17304822621113/50000000000000 : ℝ)^1587 := by
    have hnat : (2241655139 : ℕ)^2099*50000000000000^1587 ≤ 17304822621113^1587*5000000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241655139 5000000000 17304822621113 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (21162857/50000000 : ℝ)^2099 ≤ (16036474192891/50000000000000 : ℝ)^1587 := by
    have hnat : (21162857 : ℕ)^2099*50000000000000^1587 ≤ 16036474192891^1587*50000000^2099 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21162857 50000000 16036474192891 50000000000000 2099 1587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2099/512 : ℝ)) 2099 1587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4356161183/10000000000 : ℝ), (2241655139/5000000000 : ℝ), (21162857/50000000 : ℝ)] ![(8329351588133/25000000000000 : ℝ), (17304822621113/50000000000000 : ℝ), (16036474192891/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4356161183/10000000000 : ℝ)|^2099 ≤ (8329351588133/25000000000000 : ℝ)^1587
        have hw : |(4356161183/10000000000 : ℝ)|=(4356161183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2241655139/5000000000 : ℝ)|^2099 ≤ (17304822621113/50000000000000 : ℝ)^1587
        have hw : |(2241655139/5000000000 : ℝ)|=(2241655139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(21162857/50000000 : ℝ)|^2099 ≤ (16036474192891/50000000000000 : ℝ)^1587
        have hw : |(21162857/50000000 : ℝ)|=(21162857/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1203_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11431/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14083/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1143/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1143/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1143/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3521/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1143/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1143/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3521/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1143/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1143/10000 : ℝ) ^ (8395/2048 : ℝ) ≤ (13766306468268533/100000000000000000000 : ℝ) := by
    have hpowers : (1143/10000 : ℝ)^8395 ≤ (13766306468268533/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1143 : ℕ)^8395*100000000000000000000^2048 ≤ 13766306468268533^2048*10000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1143 10000 13766306468268533 100000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1143/10000 : ℝ)) (X := (13766306468268533/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3521/25000 : ℝ) ^ (8395/2048 : ℝ) ≤ (8099624137282777/25000000000000000000 : ℝ) := by
    have hpowers : (3521/25000 : ℝ)^8395 ≤ (8099624137282777/25000000000000000000 : ℝ)^2048 := by
      have hnat : (3521 : ℕ)^8395*25000000000000000000^2048 ≤ 8099624137282777^2048*25000^8395 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3521 25000 8099624137282777 25000000000000000000 8395 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3521/25000 : ℝ)) (X := (8099624137282777/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013766306468268533/50000000000000000000 : ℝ) ≤ (2500167900308309/2500000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (50013766306468268533/50000000000000000000 : ℝ)^2048 ≤ (2500167900308309/2500000000000000 : ℝ)^8395 := by
      have hnat : (50013766306468268533 : ℕ)^2048*2500000000000000^8395 ≤ 2500167900308309^8395*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013766306468268533 50000000000000000000 2500167900308309 2500000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500167900308309/2500000000000000 : ℝ)) (X := (50013766306468268533/50000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046164803017399641/100000000000000000000 : ℝ) ≤ (10001126015742429/10000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (100046164803017399641/100000000000000000000 : ℝ)^2048 ≤ (10001126015742429/10000000000000000 : ℝ)^8395 := by
      have hnat : (100046164803017399641 : ℕ)^2048*10000000000000000^8395 ≤ 10001126015742429^8395*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046164803017399641 100000000000000000000 10001126015742429 10000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001126015742429/10000000000000000 : ℝ)) (X := (100046164803017399641/100000000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508099624137282777/12500000000000000000 : ℝ) ≤ (5000790215125811/5000000000000000 : ℝ) ^ (8395/2048 : ℝ) := by
    have hpowers : (12508099624137282777/12500000000000000000 : ℝ)^2048 ≤ (5000790215125811/5000000000000000 : ℝ)^8395 := by
      have hnat : (12508099624137282777 : ℕ)^2048*5000000000000000^8395 ≤ 5000790215125811^8395*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508099624137282777 12500000000000000000 5000790215125811 5000000000000000 2048 8395 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000790215125811/5000000000000000 : ℝ)) (X := (12508099624137282777/12500000000000000000 : ℝ)) (by norm_num) 8395 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13766306468268533/100000000000000000000 : ℝ) ≤ ((6632848628498214091/6635000000000000000 : ℝ)+2*(454414509193/265400000000000 : ℝ)*(1143/10000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (6632848628498214091/6635000000000000000 : ℝ)+2*(454414509193/265400000000000 : ℝ)*(1143/10000 : ℝ)=(2500167900308309/2500000000000000 : ℝ) by norm_num, show 1+2*(13766306468268533/100000000000000000000 : ℝ)=(50013766306468268533/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8099624137282777/25000000000000000000 : ℝ)+(13766306468268533/100000000000000000000 : ℝ) ≤ ((6632848628498214091/6635000000000000000 : ℝ)+(454414509193/265400000000000 : ℝ)*((3521/25000 : ℝ)+(1143/10000 : ℝ)))^(8395/2048 : ℝ) := by
    rw [show (6632848628498214091/6635000000000000000 : ℝ)+(454414509193/265400000000000 : ℝ)*((3521/25000 : ℝ)+(1143/10000 : ℝ))=(10001126015742429/10000000000000000 : ℝ) by norm_num, show 1+(8099624137282777/25000000000000000000 : ℝ)+(13766306468268533/100000000000000000000 : ℝ)=(100046164803017399641/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8099624137282777/25000000000000000000 : ℝ) ≤ ((6632848628498214091/6635000000000000000 : ℝ)+2*(454414509193/265400000000000 : ℝ)*(3521/25000 : ℝ))^(8395/2048 : ℝ) := by
    rw [show (6632848628498214091/6635000000000000000 : ℝ)+2*(454414509193/265400000000000 : ℝ)*(3521/25000 : ℝ)=(5000790215125811/5000000000000000 : ℝ) by norm_num, show 1+2*(8099624137282777/25000000000000000000 : ℝ)=(12508099624137282777/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6632848628498214091/6635000000000000000 : ℝ)*(X 1 0+X 2 0)+(454414509193/265400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (1143/10000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (6632848628498214091/6635000000000000000 : ℝ)) (alpha := (454414509193/265400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6632848628498214091/6635000000000000000 : ℝ)*(X 0 1+X 2 1)+(454414509193/265400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (1143/10000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (6632848628498214091/6635000000000000000 : ℝ)) (alpha := (454414509193/265400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6632848628498214091/6635000000000000000 : ℝ)*(X 0 2+X 1 2)+(454414509193/265400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8395/2048 : ℝ)) (lo := (1143/10000 : ℝ)) (hi := (3521/25000 : ℝ)) (c := (6632848628498214091/6635000000000000000 : ℝ)) (alpha := (454414509193/265400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1069027637/5000000000 : ℝ)*X 0 0+(2695940599/5000000000 : ℝ)*X 0 1+(42133673/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336123189/2500000000 : ℝ)*X 1 0+(-44030581/200000000 : ℝ)*X 1 1+(5143271/9765625 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((10438463/19531250 : ℝ)*X 2 0+(5266709233/10000000000 : ℝ)*X 2 1+(-2201529009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4356152161/10000000000 : ℝ)*X 0 0+(2115967461/5000000000 : ℝ)*X 0 1+(4483943957/10000000000 : ℝ)*X 0 2+(4356152161/10000000000 : ℝ)*X 1 0+(2115967461/5000000000 : ℝ)*X 1 1+(4483943957/10000000000 : ℝ)*X 1 2+(4356152161/10000000000 : ℝ)*X 2 0+(2115967461/5000000000 : ℝ)*X 2 1+(4483943957/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-267257519/1250000000 : ℝ)*X 0 0+(5267024669/10000000000 : ℝ)*X 0 1+(539156441/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((531263997/1000000000 : ℝ)*X 1 0+(-259584171/1250000000 : ℝ)*X 1 1+(2695782673/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312640603/10000000000 : ℝ)*X 2 0+(2695782279/5000000000 : ℝ)*X 2 1+(-2076673583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4356161183/10000000000 : ℝ)*X 0 0+(2241655139/5000000000 : ℝ)*X 0 1+(21162857/50000000 : ℝ)*X 0 2+(4356161183/10000000000 : ℝ)*X 1 0+(2241655139/5000000000 : ℝ)*X 1 1+(21162857/50000000 : ℝ)*X 1 2+(4356161183/10000000000 : ℝ)*X 2 0+(2241655139/5000000000 : ℝ)*X 2 1+(21162857/50000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1203_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2880337065614992697826269397/331750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2076511687/100000000000000 : ℝ)*(base19) + (2229967849/100000000000000 : ℝ)*(base23) + (157659923/100000000000000 : ℝ)*(lower2) + (63954371/20000000000000 : ℝ)*(upper3) + (62684593/25000000000000 : ℝ)*(upper5) + (5978663669292789/100000000000000 : ℝ)*(major0) + (5978663669292789/100000000000000 : ℝ)*(major1) + (5978663669292789/100000000000000 : ℝ)*(major2) + (399453672913157/5000000000000 : ℝ)*(sp0) + (3994574371267401/50000000000000 : ℝ)*(sp1) + (99864357363483/1250000000000 : ℝ)*(sp2) + (99203529658467/2500000000000 : ℝ)*(sp3) + (77360783349/100000000000000 : ℝ)*(sp4) + (8760948001/25000000000000 : ℝ)*(sp7) + (992044057532671/25000000000000 : ℝ)*(f.failure) + (7989150819046489/100000000000000 : ℝ)*(f.sum) + (20846336780197/13270000000000000000000000000 : ℝ)*base65 + (6551476382919085201/663500000000000000000000000000000 : ℝ)*base68 + (19209812769608585201/663500000000000000000000000000000 : ℝ)*base70 + (759176116542414799/663500000000000000000000000000000 : ℝ)*base71 + (77990523059163/13270000000000000000000000000 : ℝ)*base74 + (12884001525651585201/663500000000000000000000000000000 : ℝ)*base76 + (393568024714414799/663500000000000000000000000000000 : ℝ)*base77 + (978875846675585201/663500000000000000000000000000000 : ℝ)*base80 + (60452527832723/13270000000000000000000000000 : ℝ)*base82 + (7558049/625000000000000000000 : ℝ)*base89 + (7558049/625000000000000000000 : ℝ)*base91 + (7558049/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1986083213533124860624202373/331750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (147840419/20000000000000 : ℝ)*(base19) + (1068027287/50000000000000 : ℝ)*(base23) + (718250633/100000000000000 : ℝ)*(lower1) + (179689831/100000000000000 : ℝ)*(upper2) + (373966451/100000000000000 : ℝ)*(upper3) + (6008854253848149/100000000000000 : ℝ)*(major0) + (6008854253848149/100000000000000 : ℝ)*(major1) + (120177085076963/2000000000000 : ℝ)*(major2) + (8498681889/50000000000000 : ℝ)*(sp2) + (95433509/1000000000000 : ℝ)*(sp3) + (501843368403531/6250000000000 : ℝ)*(sp4) + (8029493155254401/100000000000000 : ℝ)*(sp5) + (125460543141221/1562500000000 : ℝ)*(sp6) + (1994102435166341/50000000000000 : ℝ)*(sp7) + (3988214413683581/100000000000000 : ℝ)*(f.failure) + (501843368403531/6250000000000 : ℝ)*(f.sum) + (13716851043147/26540000000000000000000000000 : ℝ)*base65 + (1945826918409817559/663500000000000000000000000000000 : ℝ)*base67 + (42356884438764133/13270000000000000000000000000000 : ℝ)*base69 + (10358708040853817559/663500000000000000000000000000000 : ℝ)*base71 + (178239339078413/26540000000000000000000000000 : ℝ)*base74 + (93861995716544133/13270000000000000000000000000000 : ℝ)*base75 + (2516668639818992559/663500000000000000000000000000000 : ℝ)*base77 + (8648068363447007441/663500000000000000000000000000000 : ℝ)*base80 + (56602850803663/13270000000000000000000000000 : ℝ)*base82 + (2008339/2500000000000000000000 : ℝ)*base89 + (2008339/2500000000000000000000 : ℝ)*base91 + (22991661/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1203_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3521/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1143/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1203_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1203_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5701/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1203_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1203_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1203_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8395/2048 : ℝ) ≤ p) (hpb : p ≤ (2099/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37666319/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7057/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5701/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11431/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14083/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1203_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
