-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1253_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:24:36.400955+00:00
-- url     : https://prove2.me/submissions/b4e9889d-f406-4127-9cc3-b42005898641

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
theorem support_rectangle_w1253_s0_0 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-464292673/2500000000 : ℝ)*x 0 + (6029029447/10000000000 : ℝ)*x 1 + (1198587071/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (464292673/2500000000 : ℝ)^4223 ≤ (10834559692307/100000000000000 : ℝ)^3199 := by
    have hnat : (464292673 : ℕ)^4223*100000000000000^3199 ≤ 10834559692307^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      464292673 2500000000 10834559692307 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6029029447/10000000000 : ℝ)^4223 ≤ (51274872903157/100000000000000 : ℝ)^3199 := by
    have hnat : (6029029447 : ℕ)^4223*100000000000000^3199 ≤ 51274872903157^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6029029447 10000000000 51274872903157 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198587071/2500000000 : ℝ)^4223 ≤ (1894528369439/5000000000000 : ℝ)^3199 := by
    have hnat : (1198587071 : ℕ)^4223*5000000000000^3199 ≤ 1894528369439^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198587071 2500000000 1894528369439 5000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-464292673/2500000000 : ℝ), (6029029447/10000000000 : ℝ), (1198587071/2500000000 : ℝ)] ![(10834559692307/100000000000000 : ℝ), (51274872903157/100000000000000 : ℝ), (1894528369439/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-464292673/2500000000 : ℝ)|^4223 ≤ (10834559692307/100000000000000 : ℝ)^3199
        have hw : |(-464292673/2500000000 : ℝ)|=(464292673/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6029029447/10000000000 : ℝ)|^4223 ≤ (51274872903157/100000000000000 : ℝ)^3199
        have hw : |(6029029447/10000000000 : ℝ)|=(6029029447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1198587071/2500000000 : ℝ)|^4223 ≤ (1894528369439/5000000000000 : ℝ)^3199
        have hw : |(1198587071/2500000000 : ℝ)|=(1198587071/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s0_1 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1377634951/2500000000 : ℝ)*x 0 + (-2562713111/10000000000 : ℝ)*x 1 + (4794348223/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377634951/2500000000 : ℝ)^4223 ≤ (45535528455741/100000000000000 : ℝ)^3199 := by
    have hnat : (1377634951 : ℕ)^4223*100000000000000^3199 ≤ 45535528455741^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377634951 2500000000 45535528455741 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2562713111/10000000000 : ℝ)^4223 ≤ (8286952388607/50000000000000 : ℝ)^3199 := by
    have hnat : (2562713111 : ℕ)^4223*50000000000000^3199 ≤ 8286952388607^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2562713111 10000000000 8286952388607 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4794348223/10000000000 : ℝ)^4223 ≤ (37890566752369/100000000000000 : ℝ)^3199 := by
    have hnat : (4794348223 : ℕ)^4223*100000000000000^3199 ≤ 37890566752369^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4794348223 10000000000 37890566752369 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377634951/2500000000 : ℝ), (-2562713111/10000000000 : ℝ), (4794348223/10000000000 : ℝ)] ![(45535528455741/100000000000000 : ℝ), (8286952388607/50000000000000 : ℝ), (37890566752369/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377634951/2500000000 : ℝ)|^4223 ≤ (45535528455741/100000000000000 : ℝ)^3199
        have hw : |(1377634951/2500000000 : ℝ)|=(1377634951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2562713111/10000000000 : ℝ)|^4223 ≤ (8286952388607/50000000000000 : ℝ)^3199
        have hw : |(-2562713111/10000000000 : ℝ)|=(2562713111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4794348223/10000000000 : ℝ)|^4223 ≤ (37890566752369/100000000000000 : ℝ)^3199
        have hw : |(4794348223/10000000000 : ℝ)|=(4794348223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s0_2 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2755269871/5000000000 : ℝ)*x 0 + (2397174153/5000000000 : ℝ)*x 1 + (-256271309/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755269871/5000000000 : ℝ)^4223 ≤ (45535527779417/100000000000000 : ℝ)^3199 := by
    have hnat : (2755269871 : ℕ)^4223*100000000000000^3199 ≤ 45535527779417^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755269871 5000000000 45535527779417 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2397174153/5000000000 : ℝ)^4223 ≤ (18945283809153/50000000000000 : ℝ)^3199 := by
    have hnat : (2397174153 : ℕ)^4223*50000000000000^3199 ≤ 18945283809153^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397174153 5000000000 18945283809153 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (256271309/1000000000 : ℝ)^4223 ≤ (8286952298963/50000000000000 : ℝ)^3199 := by
    have hnat : (256271309 : ℕ)^4223*50000000000000^3199 ≤ 8286952298963^3199*1000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256271309 1000000000 8286952298963 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755269871/5000000000 : ℝ), (2397174153/5000000000 : ℝ), (-256271309/1000000000 : ℝ)] ![(45535527779417/100000000000000 : ℝ), (18945283809153/50000000000000 : ℝ), (8286952298963/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755269871/5000000000 : ℝ)|^4223 ≤ (45535527779417/100000000000000 : ℝ)^3199
        have hw : |(2755269871/5000000000 : ℝ)|=(2755269871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2397174153/5000000000 : ℝ)|^4223 ≤ (18945283809153/50000000000000 : ℝ)^3199
        have hw : |(2397174153/5000000000 : ℝ)|=(2397174153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-256271309/1000000000 : ℝ)|^4223 ≤ (8286952298963/50000000000000 : ℝ)^3199
        have hw : |(-256271309/1000000000 : ℝ)|=(256271309/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s0_3 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4192158969/10000000000 : ℝ)*x 0 + (3116483429/10000000000 : ℝ)*x 1 + (1406610517/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4192158969/10000000000 : ℝ)^4223 ≤ (31738036312883/100000000000000 : ℝ)^3199 := by
    have hnat : (4192158969 : ℕ)^4223*100000000000000^3199 ≤ 31738036312883^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4192158969 10000000000 31738036312883 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3116483429/10000000000 : ℝ)^4223 ≤ (21457885111713/100000000000000 : ℝ)^3199 := by
    have hnat : (3116483429 : ℕ)^4223*100000000000000^3199 ≤ 21457885111713^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3116483429 10000000000 21457885111713 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1406610517/2500000000 : ℝ)^4223 ≤ (46804078561513/100000000000000 : ℝ)^3199 := by
    have hnat : (1406610517 : ℕ)^4223*100000000000000^3199 ≤ 46804078561513^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1406610517 2500000000 46804078561513 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4192158969/10000000000 : ℝ), (3116483429/10000000000 : ℝ), (1406610517/2500000000 : ℝ)] ![(31738036312883/100000000000000 : ℝ), (21457885111713/100000000000000 : ℝ), (46804078561513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4192158969/10000000000 : ℝ)|^4223 ≤ (31738036312883/100000000000000 : ℝ)^3199
        have hw : |(4192158969/10000000000 : ℝ)|=(4192158969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3116483429/10000000000 : ℝ)|^4223 ≤ (21457885111713/100000000000000 : ℝ)^3199
        have hw : |(3116483429/10000000000 : ℝ)|=(3116483429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1406610517/2500000000 : ℝ)|^4223 ≤ (46804078561513/100000000000000 : ℝ)^3199
        have hw : |(1406610517/2500000000 : ℝ)|=(1406610517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s0_4 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-372399399/2000000000 : ℝ)*x 0 + (241306837/500000000 : ℝ)*x 1 + (2998058539/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (372399399/2000000000 : ℝ)^4223 ≤ (10871744142291/100000000000000 : ℝ)^3199 := by
    have hnat : (372399399 : ℕ)^4223*100000000000000^3199 ≤ 10871744142291^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372399399 2000000000 10871744142291 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241306837/500000000 : ℝ)^4223 ≤ (3822256712717/10000000000000 : ℝ)^3199 := by
    have hnat : (241306837 : ℕ)^4223*10000000000000^3199 ≤ 3822256712717^3199*500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241306837 500000000 3822256712717 10000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2998058539/5000000000 : ℝ)^4223 ≤ (5090568871867/10000000000000 : ℝ)^3199 := by
    have hnat : (2998058539 : ℕ)^4223*10000000000000^3199 ≤ 5090568871867^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2998058539 5000000000 5090568871867 10000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-372399399/2000000000 : ℝ), (241306837/500000000 : ℝ), (2998058539/5000000000 : ℝ)] ![(10871744142291/100000000000000 : ℝ), (3822256712717/10000000000000 : ℝ), (5090568871867/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-372399399/2000000000 : ℝ)|^4223 ≤ (10871744142291/100000000000000 : ℝ)^3199
        have hw : |(-372399399/2000000000 : ℝ)|=(372399399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241306837/500000000 : ℝ)|^4223 ≤ (3822256712717/10000000000000 : ℝ)^3199
        have hw : |(241306837/500000000 : ℝ)|=(241306837/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2998058539/5000000000 : ℝ)|^4223 ≤ (5090568871867/10000000000000 : ℝ)^3199
        have hw : |(2998058539/5000000000 : ℝ)|=(2998058539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s0_5 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (646819309/1250000000 : ℝ)*x 0 + (-68047101/500000000 : ℝ)*x 1 + (5996119441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (646819309/1250000000 : ℝ)^4223 ≤ (4190672186021/10000000000000 : ℝ)^3199 := by
    have hnat : (646819309 : ℕ)^4223*10000000000000^3199 ≤ 4190672186021^3199*1250000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      646819309 1250000000 4190672186021 10000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (68047101/500000000 : ℝ)^4223 ≤ (224611341387/3125000000000 : ℝ)^3199 := by
    have hnat : (68047101 : ℕ)^4223*3125000000000^3199 ≤ 224611341387^3199*500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      68047101 500000000 224611341387 3125000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5996119441/10000000000 : ℝ)^4223 ≤ (50905715201647/100000000000000 : ℝ)^3199 := by
    have hnat : (5996119441 : ℕ)^4223*100000000000000^3199 ≤ 50905715201647^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5996119441 10000000000 50905715201647 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(646819309/1250000000 : ℝ), (-68047101/500000000 : ℝ), (5996119441/10000000000 : ℝ)] ![(4190672186021/10000000000000 : ℝ), (224611341387/3125000000000 : ℝ), (50905715201647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(646819309/1250000000 : ℝ)|^4223 ≤ (4190672186021/10000000000000 : ℝ)^3199
        have hw : |(646819309/1250000000 : ℝ)|=(646819309/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-68047101/500000000 : ℝ)|^4223 ≤ (224611341387/3125000000000 : ℝ)^3199
        have hw : |(-68047101/500000000 : ℝ)|=(68047101/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5996119441/10000000000 : ℝ)|^4223 ≤ (50905715201647/100000000000000 : ℝ)^3199
        have hw : |(5996119441/10000000000 : ℝ)|=(5996119441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s0_6 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5174555467/10000000000 : ℝ)*x 0 + (2998058753/5000000000 : ℝ)*x 1 + (-272188721/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174555467/10000000000 : ℝ)^4223 ≤ (5238341562217/12500000000000 : ℝ)^3199 := by
    have hnat : (5174555467 : ℕ)^4223*12500000000000^3199 ≤ 5238341562217^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174555467 10000000000 5238341562217 12500000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2998058753/5000000000 : ℝ)^4223 ≤ (50905693515417/100000000000000 : ℝ)^3199 := by
    have hnat : (2998058753 : ℕ)^4223*100000000000000^3199 ≤ 50905693515417^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2998058753 5000000000 50905693515417 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272188721/2000000000 : ℝ)^4223 ≤ (718757397479/10000000000000 : ℝ)^3199 := by
    have hnat : (272188721 : ℕ)^4223*10000000000000^3199 ≤ 718757397479^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272188721 2000000000 718757397479 10000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174555467/10000000000 : ℝ), (2998058753/5000000000 : ℝ), (-272188721/2000000000 : ℝ)] ![(5238341562217/12500000000000 : ℝ), (50905693515417/100000000000000 : ℝ), (718757397479/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174555467/10000000000 : ℝ)|^4223 ≤ (5238341562217/12500000000000 : ℝ)^3199
        have hw : |(5174555467/10000000000 : ℝ)|=(5174555467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2998058753/5000000000 : ℝ)|^4223 ≤ (50905693515417/100000000000000 : ℝ)^3199
        have hw : |(2998058753/5000000000 : ℝ)|=(2998058753/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272188721/2000000000 : ℝ)|^4223 ≤ (718757397479/10000000000000 : ℝ)^3199
        have hw : |(-272188721/2000000000 : ℝ)|=(272188721/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s0_7 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4201972097/10000000000 : ℝ)*x 0 + (2780912741/5000000000 : ℝ)*x 1 + (3183384383/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4201972097/10000000000 : ℝ)^4223 ≤ (15918073826339/50000000000000 : ℝ)^3199 := by
    have hnat : (4201972097 : ℕ)^4223*50000000000000^3199 ≤ 15918073826339^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4201972097 10000000000 15918073826339 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2780912741/5000000000 : ℝ)^4223 ≤ (46095807331693/100000000000000 : ℝ)^3199 := by
    have hnat : (2780912741 : ℕ)^4223*100000000000000^3199 ≤ 46095807331693^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2780912741 5000000000 46095807331693 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3183384383/10000000000 : ℝ)^4223 ≤ (22068044996321/100000000000000 : ℝ)^3199 := by
    have hnat : (3183384383 : ℕ)^4223*100000000000000^3199 ≤ 22068044996321^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3183384383 10000000000 22068044996321 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4201972097/10000000000 : ℝ), (2780912741/5000000000 : ℝ), (3183384383/10000000000 : ℝ)] ![(15918073826339/50000000000000 : ℝ), (46095807331693/100000000000000 : ℝ), (22068044996321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4201972097/10000000000 : ℝ)|^4223 ≤ (15918073826339/50000000000000 : ℝ)^3199
        have hw : |(4201972097/10000000000 : ℝ)|=(4201972097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2780912741/5000000000 : ℝ)|^4223 ≤ (46095807331693/100000000000000 : ℝ)^3199
        have hw : |(2780912741/5000000000 : ℝ)|=(2780912741/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3183384383/10000000000 : ℝ)|^4223 ≤ (22068044996321/100000000000000 : ℝ)^3199
        have hw : |(3183384383/10000000000 : ℝ)|=(3183384383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1253_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (431/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5479/20000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8445/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8445 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8445*1^2048 ≤ 0^2048*1^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8445/2048 : ℝ) ≤ (2286021887151977599/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8445 ≤ (2286021887151977599/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8445*100000000000000000000^2048 ≤ 2286021887151977599^2048*5^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2286021887151977599 100000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2286021887151977599/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8445 := by
      have hnat : (1 : ℕ)^2048*1^8445 ≤ 1^8445*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102286021887151977599/100000000000000000000 : ℝ) ≤ (5027482365896149/5000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (102286021887151977599/100000000000000000000 : ℝ)^2048 ≤ (5027482365896149/5000000000000000 : ℝ)^8445 := by
      have hnat : (102286021887151977599 : ℕ)^2048*5000000000000000^8445 ≤ 5027482365896149^8445*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102286021887151977599 100000000000000000000 5027482365896149 5000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5027482365896149/5000000000000000 : ℝ)) (X := (102286021887151977599/100000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52286021887151977599/50000000000000000000 : ℝ) ≤ (2527482365896149/2500000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (52286021887151977599/50000000000000000000 : ℝ)^2048 ≤ (2527482365896149/2500000000000000 : ℝ)^8445 := by
      have hnat : (52286021887151977599 : ℕ)^2048*2500000000000000^8445 ≤ 2527482365896149^8445*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52286021887151977599 50000000000000000000 2527482365896149 2500000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2527482365896149/2500000000000000 : ℝ)) (X := (52286021887151977599/50000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(27482365896149/2000000000000000 : ℝ)*(0 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(27482365896149/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2286021887151977599/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(27482365896149/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8445/2048 : ℝ) := by
    rw [show (1 : ℝ)+(27482365896149/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5027482365896149/5000000000000000 : ℝ) by norm_num, show 1+(2286021887151977599/100000000000000000000 : ℝ)+(0 : ℝ)=(102286021887151977599/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2286021887151977599/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(27482365896149/2000000000000000 : ℝ)*(2/5 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(27482365896149/2000000000000000 : ℝ)*(2/5 : ℝ)=(2527482365896149/2500000000000000 : ℝ) by norm_num, show 1+2*(2286021887151977599/100000000000000000000 : ℝ)=(52286021887151977599/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(27482365896149/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27482365896149/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(27482365896149/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27482365896149/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(27482365896149/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (27482365896149/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-464292673/2500000000 : ℝ)*X 0 0+(6029029447/10000000000 : ℝ)*X 0 1+(1198587071/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1377634951/2500000000 : ℝ)*X 1 0+(-2562713111/10000000000 : ℝ)*X 1 1+(4794348223/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2755269871/5000000000 : ℝ)*X 2 0+(2397174153/5000000000 : ℝ)*X 2 1+(-256271309/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4192158969/10000000000 : ℝ)*X 0 0+(3116483429/10000000000 : ℝ)*X 0 1+(1406610517/2500000000 : ℝ)*X 0 2+(4192158969/10000000000 : ℝ)*X 1 0+(3116483429/10000000000 : ℝ)*X 1 1+(1406610517/2500000000 : ℝ)*X 1 2+(4192158969/10000000000 : ℝ)*X 2 0+(3116483429/10000000000 : ℝ)*X 2 1+(1406610517/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-372399399/2000000000 : ℝ)*X 0 0+(241306837/500000000 : ℝ)*X 0 1+(2998058539/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((646819309/1250000000 : ℝ)*X 1 0+(-68047101/500000000 : ℝ)*X 1 1+(5996119441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5174555467/10000000000 : ℝ)*X 2 0+(2998058753/5000000000 : ℝ)*X 2 1+(-272188721/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4201972097/10000000000 : ℝ)*X 0 0+(2780912741/5000000000 : ℝ)*X 0 1+(3183384383/10000000000 : ℝ)*X 0 2+(4201972097/10000000000 : ℝ)*X 1 0+(2780912741/5000000000 : ℝ)*X 1 1+(3183384383/10000000000 : ℝ)*X 1 2+(4201972097/10000000000 : ℝ)*X 2 0+(2780912741/5000000000 : ℝ)*X 2 1+(3183384383/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (78614865238759632609981/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2650273/6250000000000 : ℝ)*(base1) + (777959387/100000000000000 : ℝ)*(base19) + (358523611/50000000000000 : ℝ)*(base23) + (10359903/20000000000000 : ℝ)*(base24) + (85212337/50000000000000 : ℝ)*(upper3) + (151043154698123/25000000000000 : ℝ)*(major0) + (151043154698123/25000000000000 : ℝ)*(major1) + (151043154698123/25000000000000 : ℝ)*(major2) + (404964161388119/50000000000000 : ℝ)*(sp0) + (50620577742009/6250000000000 : ℝ)*(sp1) + (809929252984793/100000000000000 : ℝ)*(sp2) + (24900858383217/6250000000000 : ℝ)*(sp3) + (1741459661/100000000000000 : ℝ)*(sp4) + (1334397787/100000000000000 : ℝ)*(sp7) + (398415110933627/100000000000000 : ℝ)*(f.failure) + (80993002183153/10000000000000 : ℝ)*(f.sum) + (1660805328327/25000000000000000000000000000 : ℝ)*base65 + (243375104171673/50000000000000000000000000000 : ℝ)*base68 + (148610929878327/50000000000000000000000000000 : ℝ)*base69 + (128926610921673/50000000000000000000000000000 : ℝ)*base72 + (27357182721673/25000000000000000000000000000 : ℝ)*base74 + (275595768221673/50000000000000000000000000000 : ℝ)*base76 + (196392792421673/50000000000000000000000000000 : ℝ)*base78 + (87844360771673/50000000000000000000000000000 : ℝ)*base80 + (34213359553327/25000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (22672373/5000000000000000000000 : ℝ)*base90 + (22672373/5000000000000000000000 : ℝ)*base92 + (22672373/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (243178876840425991175199/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93277043/50000000000000 : ℝ)*(base1) + (552890353/50000000000000 : ℝ)*(base19) + (250171503/20000000000000 : ℝ)*(base23) + (252806361/100000000000000 : ℝ)*(upper3) + (637579174312817/100000000000000 : ℝ)*(major0) + (637579174312817/100000000000000 : ℝ)*(major1) + (637579174312817/100000000000000 : ℝ)*(major2) + (291282363/12500000000000 : ℝ)*(sp1) + (2033434429/100000000000000 : ℝ)*(sp2) + (161816383/100000000000000 : ℝ)*(sp3) + (854713669739579/100000000000000 : ℝ)*(sp4) + (427355023572941/50000000000000 : ℝ)*(sp5) + (213677549723387/25000000000000 : ℝ)*(sp6) + (26277772184401/6250000000000 : ℝ)*(sp7) + (84088940664177/20000000000000 : ℝ)*(f.failure) + (854713483185493/100000000000000 : ℝ)*(f.sum) + (64003175758267/100000000000000000000000000000 : ℝ)*base66 + (31456594158267/200000000000000000000000000000 : ℝ)*base68 + (417743245158267/200000000000000000000000000000 : ℝ)*base70 + (1034047341841733/200000000000000000000000000000 : ℝ)*base71 + (152193121858267/100000000000000000000000000000 : ℝ)*base74 + (844018876441733/200000000000000000000000000000 : ℝ)*base75 + (783426319041733/200000000000000000000000000000 : ℝ)*base77 + (651054185441733/200000000000000000000000000000 : ℝ)*base79 + (255068260558267/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (841823/1000000000000000000000 : ℝ)*base90 + (841823/1000000000000000000000 : ℝ)*base92 + (841823/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1253_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (431/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5479/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1253_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1253_s1_0 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1026890433/5000000000 : ℝ)*x 0 + (2836426251/5000000000 : ℝ)*x 1 + (157021009/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026890433/5000000000 : ℝ)^4223 ≤ (12373787415517/100000000000000 : ℝ)^3199 := by
    have hnat : (1026890433 : ℕ)^4223*100000000000000^3199 ≤ 12373787415517^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026890433 5000000000 12373787415517 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2836426251/5000000000 : ℝ)^4223 ≤ (5914300060741/12500000000000 : ℝ)^3199 := by
    have hnat : (2836426251 : ℕ)^4223*12500000000000^3199 ≤ 5914300060741^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2836426251 5000000000 5914300060741 12500000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (157021009/312500000 : ℝ)^4223 ≤ (314936031991/781250000000 : ℝ)^3199 := by
    have hnat : (157021009 : ℕ)^4223*781250000000^3199 ≤ 314936031991^3199*312500000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      157021009 312500000 314936031991 781250000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1026890433/5000000000 : ℝ), (2836426251/5000000000 : ℝ), (157021009/312500000 : ℝ)] ![(12373787415517/100000000000000 : ℝ), (5914300060741/12500000000000 : ℝ), (314936031991/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1026890433/5000000000 : ℝ)|^4223 ≤ (12373787415517/100000000000000 : ℝ)^3199
        have hw : |(-1026890433/5000000000 : ℝ)|=(1026890433/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2836426251/5000000000 : ℝ)|^4223 ≤ (5914300060741/12500000000000 : ℝ)^3199
        have hw : |(2836426251/5000000000 : ℝ)|=(2836426251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(157021009/312500000 : ℝ)|^4223 ≤ (314936031991/781250000000 : ℝ)^3199
        have hw : |(157021009/312500000 : ℝ)|=(157021009/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s1_1 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2706530691/5000000000 : ℝ)*x 0 + (-600415997/2500000000 : ℝ)*x 1 + (502467217/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706530691/5000000000 : ℝ)^4223 ≤ (44475212562261/100000000000000 : ℝ)^3199 := by
    have hnat : (2706530691 : ℕ)^4223*100000000000000^3199 ≤ 44475212562261^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706530691 5000000000 44475212562261 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (600415997/2500000000 : ℝ)^4223 ≤ (7606488289251/50000000000000 : ℝ)^3199 := by
    have hnat : (600415997 : ℕ)^4223*50000000000000^3199 ≤ 7606488289251^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      600415997 2500000000 7606488289251 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502467217/1000000000 : ℝ)^4223 ≤ (20155905422563/50000000000000 : ℝ)^3199 := by
    have hnat : (502467217 : ℕ)^4223*50000000000000^3199 ≤ 20155905422563^3199*1000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502467217 1000000000 20155905422563 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706530691/5000000000 : ℝ), (-600415997/2500000000 : ℝ), (502467217/1000000000 : ℝ)] ![(44475212562261/100000000000000 : ℝ), (7606488289251/50000000000000 : ℝ), (20155905422563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706530691/5000000000 : ℝ)|^4223 ≤ (44475212562261/100000000000000 : ℝ)^3199
        have hw : |(2706530691/5000000000 : ℝ)|=(2706530691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-600415997/2500000000 : ℝ)|^4223 ≤ (7606488289251/50000000000000 : ℝ)^3199
        have hw : |(-600415997/2500000000 : ℝ)|=(600415997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(502467217/1000000000 : ℝ)|^4223 ≤ (20155905422563/50000000000000 : ℝ)^3199
        have hw : |(502467217/1000000000 : ℝ)|=(502467217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s1_2 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270653063/500000000 : ℝ)*x 0 + (5024672283/10000000000 : ℝ)*x 1 + (-1200832001/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270653063/500000000 : ℝ)^4223 ≤ (11118802809753/25000000000000 : ℝ)^3199 := by
    have hnat : (270653063 : ℕ)^4223*25000000000000^3199 ≤ 11118802809753^3199*500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270653063 500000000 11118802809753 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5024672283/10000000000 : ℝ)^4223 ≤ (40311812041893/100000000000000 : ℝ)^3199 := by
    have hnat : (5024672283 : ℕ)^4223*100000000000000^3199 ≤ 40311812041893^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5024672283 10000000000 40311812041893 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200832001/5000000000 : ℝ)^4223 ≤ (1521297669557/10000000000000 : ℝ)^3199 := by
    have hnat : (1200832001 : ℕ)^4223*10000000000000^3199 ≤ 1521297669557^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200832001 5000000000 1521297669557 10000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270653063/500000000 : ℝ), (5024672283/10000000000 : ℝ), (-1200832001/5000000000 : ℝ)] ![(11118802809753/25000000000000 : ℝ), (40311812041893/100000000000000 : ℝ), (1521297669557/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270653063/500000000 : ℝ)|^4223 ≤ (11118802809753/25000000000000 : ℝ)^3199
        have hw : |(270653063/500000000 : ℝ)|=(270653063/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5024672283/10000000000 : ℝ)|^4223 ≤ (40311812041893/100000000000000 : ℝ)^3199
        have hw : |(5024672283/10000000000 : ℝ)|=(5024672283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1200832001/5000000000 : ℝ)|^4223 ≤ (1521297669557/10000000000000 : ℝ)^3199
        have hw : |(-1200832001/5000000000 : ℝ)|=(1200832001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s1_3 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4307899539/10000000000 : ℝ)*x 0 + (1848715759/5000000000 : ℝ)*x 1 + (5015104163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307899539/10000000000 : ℝ)^4223 ≤ (8224963363149/25000000000000 : ℝ)^3199 := by
    have hnat : (4307899539 : ℕ)^4223*25000000000000^3199 ≤ 8224963363149^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307899539 10000000000 8224963363149 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1848715759/5000000000 : ℝ)^4223 ≤ (13444819133937/50000000000000 : ℝ)^3199 := by
    have hnat : (1848715759 : ℕ)^4223*50000000000000^3199 ≤ 13444819133937^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1848715759 5000000000 13444819133937 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5015104163/10000000000 : ℝ)^4223 ≤ (8042101654953/20000000000000 : ℝ)^3199 := by
    have hnat : (5015104163 : ℕ)^4223*20000000000000^3199 ≤ 8042101654953^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5015104163 10000000000 8042101654953 20000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307899539/10000000000 : ℝ), (1848715759/5000000000 : ℝ), (5015104163/10000000000 : ℝ)] ![(8224963363149/25000000000000 : ℝ), (13444819133937/50000000000000 : ℝ), (8042101654953/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307899539/10000000000 : ℝ)|^4223 ≤ (8224963363149/25000000000000 : ℝ)^3199
        have hw : |(4307899539/10000000000 : ℝ)|=(4307899539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1848715759/5000000000 : ℝ)|^4223 ≤ (13444819133937/50000000000000 : ℝ)^3199
        have hw : |(1848715759/5000000000 : ℝ)|=(1848715759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5015104163/10000000000 : ℝ)|^4223 ≤ (8042101654953/20000000000000 : ℝ)^3199
        have hw : |(5015104163/10000000000 : ℝ)|=(5015104163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s1_4 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2054444309/10000000000 : ℝ)*x 0 + (5033149959/10000000000 : ℝ)*x 1 + (5664214197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2054444309/10000000000 : ℝ)^4223 ≤ (12379064347011/100000000000000 : ℝ)^3199 := by
    have hnat : (2054444309 : ℕ)^4223*100000000000000^3199 ≤ 12379064347011^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2054444309 10000000000 12379064347011 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5033149959/10000000000 : ℝ)^4223 ≤ (10100405549441/25000000000000 : ℝ)^3199 := by
    have hnat : (5033149959 : ℕ)^4223*25000000000000^3199 ≤ 10100405549441^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5033149959 10000000000 10100405549441 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5664214197/10000000000 : ℝ)^4223 ≤ (47219313445229/100000000000000 : ℝ)^3199 := by
    have hnat : (5664214197 : ℕ)^4223*100000000000000^3199 ≤ 47219313445229^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664214197 10000000000 47219313445229 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2054444309/10000000000 : ℝ), (5033149959/10000000000 : ℝ), (5664214197/10000000000 : ℝ)] ![(12379064347011/100000000000000 : ℝ), (10100405549441/25000000000000 : ℝ), (47219313445229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2054444309/10000000000 : ℝ)|^4223 ≤ (12379064347011/100000000000000 : ℝ)^3199
        have hw : |(-2054444309/10000000000 : ℝ)|=(2054444309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5033149959/10000000000 : ℝ)|^4223 ≤ (10100405549441/25000000000000 : ℝ)^3199
        have hw : |(5033149959/10000000000 : ℝ)|=(5033149959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5664214197/10000000000 : ℝ)|^4223 ≤ (47219313445229/100000000000000 : ℝ)^3199
        have hw : |(5664214197/10000000000 : ℝ)|=(5664214197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s1_5 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1311496091/2500000000 : ℝ)*x 0 + (-881060949/5000000000 : ℝ)*x 1 + (708026813/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311496091/2500000000 : ℝ)^4223 ≤ (10668014856023/25000000000000 : ℝ)^3199 := by
    have hnat : (1311496091 : ℕ)^4223*25000000000000^3199 ≤ 10668014856023^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311496091 2500000000 10668014856023 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (881060949/5000000000 : ℝ)^4223 ≤ (2527155935089/25000000000000 : ℝ)^3199 := by
    have hnat : (881060949 : ℕ)^4223*25000000000000^3199 ≤ 2527155935089^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      881060949 5000000000 2527155935089 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708026813/1250000000 : ℝ)^4223 ≤ (47219316823739/100000000000000 : ℝ)^3199 := by
    have hnat : (708026813 : ℕ)^4223*100000000000000^3199 ≤ 47219316823739^3199*1250000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708026813 1250000000 47219316823739 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311496091/2500000000 : ℝ), (-881060949/5000000000 : ℝ), (708026813/1250000000 : ℝ)] ![(10668014856023/25000000000000 : ℝ), (2527155935089/25000000000000 : ℝ), (47219316823739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311496091/2500000000 : ℝ)|^4223 ≤ (10668014856023/25000000000000 : ℝ)^3199
        have hw : |(1311496091/2500000000 : ℝ)|=(1311496091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-881060949/5000000000 : ℝ)|^4223 ≤ (2527155935089/25000000000000 : ℝ)^3199
        have hw : |(-881060949/5000000000 : ℝ)|=(881060949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(708026813/1250000000 : ℝ)|^4223 ≤ (47219316823739/100000000000000 : ℝ)^3199
        have hw : |(708026813/1250000000 : ℝ)|=(708026813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s1_6 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5245984287/10000000000 : ℝ)*x 0 + (5664214283/10000000000 : ℝ)*x 1 + (-220265291/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5245984287/10000000000 : ℝ)^4223 ≤ (21336029298633/50000000000000 : ℝ)^3199 := by
    have hnat : (5245984287 : ℕ)^4223*50000000000000^3199 ≤ 21336029298633^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245984287 10000000000 21336029298633 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5664214283/10000000000 : ℝ)^4223 ≤ (11804828597913/25000000000000 : ℝ)^3199 := by
    have hnat : (5664214283 : ℕ)^4223*25000000000000^3199 ≤ 11804828597913^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5664214283 10000000000 11804828597913 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (220265291/1250000000 : ℝ)^4223 ≤ (2527156749177/25000000000000 : ℝ)^3199 := by
    have hnat : (220265291 : ℕ)^4223*25000000000000^3199 ≤ 2527156749177^3199*1250000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      220265291 1250000000 2527156749177 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5245984287/10000000000 : ℝ), (5664214283/10000000000 : ℝ), (-220265291/1250000000 : ℝ)] ![(21336029298633/50000000000000 : ℝ), (11804828597913/25000000000000 : ℝ), (2527156749177/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5245984287/10000000000 : ℝ)|^4223 ≤ (21336029298633/50000000000000 : ℝ)^3199
        have hw : |(5245984287/10000000000 : ℝ)|=(5245984287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5664214283/10000000000 : ℝ)|^4223 ≤ (11804828597913/25000000000000 : ℝ)^3199
        have hw : |(5664214283/10000000000 : ℝ)|=(5664214283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-220265291/1250000000 : ℝ)|^4223 ≤ (2527156749177/25000000000000 : ℝ)^3199
        have hw : |(-220265291/1250000000 : ℝ)|=(220265291/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s1_7 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4309247963/10000000000 : ℝ)*x 0 + (2498935091/5000000000 : ℝ)*x 1 + (3714991929/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4309247963/10000000000 : ℝ)^4223 ≤ (4114181073223/12500000000000 : ℝ)^3199 := by
    have hnat : (4309247963 : ℕ)^4223*12500000000000^3199 ≤ 4114181073223^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4309247963 10000000000 4114181073223 12500000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2498935091/5000000000 : ℝ)^4223 ≤ (20014098622763/50000000000000 : ℝ)^3199 := by
    have hnat : (2498935091 : ℕ)^4223*50000000000000^3199 ≤ 20014098622763^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2498935091 5000000000 20014098622763 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3714991929/10000000000 : ℝ)^4223 ≤ (2705835415543/10000000000000 : ℝ)^3199 := by
    have hnat : (3714991929 : ℕ)^4223*10000000000000^3199 ≤ 2705835415543^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3714991929 10000000000 2705835415543 10000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4309247963/10000000000 : ℝ), (2498935091/5000000000 : ℝ), (3714991929/10000000000 : ℝ)] ![(4114181073223/12500000000000 : ℝ), (20014098622763/50000000000000 : ℝ), (2705835415543/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4309247963/10000000000 : ℝ)|^4223 ≤ (4114181073223/12500000000000 : ℝ)^3199
        have hw : |(4309247963/10000000000 : ℝ)|=(4309247963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2498935091/5000000000 : ℝ)|^4223 ≤ (20014098622763/50000000000000 : ℝ)^3199
        have hw : |(2498935091/5000000000 : ℝ)|=(2498935091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3714991929/10000000000 : ℝ)|^4223 ≤ (2705835415543/10000000000000 : ℝ)^3199
        have hw : |(3714991929/10000000000 : ℝ)|=(3714991929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1253_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5479/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (431/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (781/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1247/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5479/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (431/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5479/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (431/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5479/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (431/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5479/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (431/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5479/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (431/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5479/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (431/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (431/50000 : ℝ) ^ (8445/2048 : ℝ) ≤ (306896284651/100000000000000000000 : ℝ) := by
    have hpowers : (431/50000 : ℝ)^8445 ≤ (306896284651/100000000000000000000 : ℝ)^2048 := by
      have hnat : (431 : ℕ)^8445*100000000000000000000^2048 ≤ 306896284651^2048*50000^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        431 50000 306896284651 100000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (431/50000 : ℝ)) (X := (306896284651/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5479/20000 : ℝ) ^ (8445/2048 : ℝ) ≤ (479974158482863251/100000000000000000000 : ℝ) := by
    have hpowers : (5479/20000 : ℝ)^8445 ≤ (479974158482863251/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5479 : ℕ)^8445*100000000000000000000^2048 ≤ 479974158482863251^2048*20000^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5479 20000 479974158482863251 100000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5479/20000 : ℝ)) (X := (479974158482863251/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000306896284651/50000000000000000000 : ℝ) ≤ (5000000007442553/5000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (50000000306896284651/50000000000000000000 : ℝ)^2048 ≤ (5000000007442553/5000000000000000 : ℝ)^8445 := by
      have hnat : (50000000306896284651 : ℕ)^2048*5000000000000000^8445 ≤ 5000000007442553^8445*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000306896284651 50000000000000000000 5000000007442553 5000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000007442553/5000000000000000 : ℝ)) (X := (50000000306896284651/50000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50239987232689573951/50000000000000000000 : ℝ) ≤ (500580938875669/500000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (50239987232689573951/50000000000000000000 : ℝ)^2048 ≤ (500580938875669/500000000000000 : ℝ)^8445 := by
      have hnat : (50239987232689573951 : ℕ)^2048*500000000000000^8445 ≤ 500580938875669^8445*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50239987232689573951 50000000000000000000 500580938875669 500000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500580938875669/500000000000000 : ℝ)) (X := (50239987232689573951/50000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50479974158482863251/50000000000000000000 : ℝ) ≤ (5011618770070827/5000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (50479974158482863251/50000000000000000000 : ℝ)^2048 ≤ (5011618770070827/5000000000000000 : ℝ)^8445 := by
      have hnat : (50479974158482863251 : ℕ)^2048*5000000000000000^8445 ≤ 5011618770070827^8445*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50479974158482863251 50000000000000000000 5011618770070827 5000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011618770070827/5000000000000000 : ℝ)) (X := (50479974158482863251/50000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(306896284651/100000000000000000000 : ℝ) ≤ ((132654984824087686561/132665000000000000000 : ℝ)+2*(5809381314137/1326650000000000 : ℝ)*(431/50000 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (132654984824087686561/132665000000000000000 : ℝ)+2*(5809381314137/1326650000000000 : ℝ)*(431/50000 : ℝ)=(5000000007442553/5000000000000000 : ℝ) by norm_num, show 1+2*(306896284651/100000000000000000000 : ℝ)=(50000000306896284651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(479974158482863251/100000000000000000000 : ℝ)+(306896284651/100000000000000000000 : ℝ) ≤ ((132654984824087686561/132665000000000000000 : ℝ)+(5809381314137/1326650000000000 : ℝ)*((5479/20000 : ℝ)+(431/50000 : ℝ)))^(8445/2048 : ℝ) := by
    rw [show (132654984824087686561/132665000000000000000 : ℝ)+(5809381314137/1326650000000000 : ℝ)*((5479/20000 : ℝ)+(431/50000 : ℝ))=(500580938875669/500000000000000 : ℝ) by norm_num, show 1+(479974158482863251/100000000000000000000 : ℝ)+(306896284651/100000000000000000000 : ℝ)=(50239987232689573951/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(479974158482863251/100000000000000000000 : ℝ) ≤ ((132654984824087686561/132665000000000000000 : ℝ)+2*(5809381314137/1326650000000000 : ℝ)*(5479/20000 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (132654984824087686561/132665000000000000000 : ℝ)+2*(5809381314137/1326650000000000 : ℝ)*(5479/20000 : ℝ)=(5011618770070827/5000000000000000 : ℝ) by norm_num, show 1+2*(479974158482863251/100000000000000000000 : ℝ)=(50479974158482863251/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (132654984824087686561/132665000000000000000 : ℝ)*(X 1 0+X 2 0)+(5809381314137/1326650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (431/50000 : ℝ)) (hi := (5479/20000 : ℝ)) (c := (132654984824087686561/132665000000000000000 : ℝ)) (alpha := (5809381314137/1326650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (132654984824087686561/132665000000000000000 : ℝ)*(X 0 1+X 2 1)+(5809381314137/1326650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (431/50000 : ℝ)) (hi := (5479/20000 : ℝ)) (c := (132654984824087686561/132665000000000000000 : ℝ)) (alpha := (5809381314137/1326650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (132654984824087686561/132665000000000000000 : ℝ)*(X 0 2+X 1 2)+(5809381314137/1326650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (431/50000 : ℝ)) (hi := (5479/20000 : ℝ)) (c := (132654984824087686561/132665000000000000000 : ℝ)) (alpha := (5809381314137/1326650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1026890433/5000000000 : ℝ)*X 0 0+(2836426251/5000000000 : ℝ)*X 0 1+(157021009/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706530691/5000000000 : ℝ)*X 1 0+(-600415997/2500000000 : ℝ)*X 1 1+(502467217/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((270653063/500000000 : ℝ)*X 2 0+(5024672283/10000000000 : ℝ)*X 2 1+(-1200832001/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4307899539/10000000000 : ℝ)*X 0 0+(1848715759/5000000000 : ℝ)*X 0 1+(5015104163/10000000000 : ℝ)*X 0 2+(4307899539/10000000000 : ℝ)*X 1 0+(1848715759/5000000000 : ℝ)*X 1 1+(5015104163/10000000000 : ℝ)*X 1 2+(4307899539/10000000000 : ℝ)*X 2 0+(1848715759/5000000000 : ℝ)*X 2 1+(5015104163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2054444309/10000000000 : ℝ)*X 0 0+(5033149959/10000000000 : ℝ)*X 0 1+(5664214197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1311496091/2500000000 : ℝ)*X 1 0+(-881060949/5000000000 : ℝ)*X 1 1+(708026813/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5245984287/10000000000 : ℝ)*X 2 0+(5664214283/10000000000 : ℝ)*X 2 1+(-220265291/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4309247963/10000000000 : ℝ)*X 0 0+(2498935091/5000000000 : ℝ)*X 0 1+(3714991929/10000000000 : ℝ)*X 0 2+(4309247963/10000000000 : ℝ)*X 1 0+(2498935091/5000000000 : ℝ)*X 1 1+(3714991929/10000000000 : ℝ)*X 1 2+(4309247963/10000000000 : ℝ)*X 2 0+(2498935091/5000000000 : ℝ)*X 2 1+(3714991929/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62143643981151896532724373241/6633250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (104197261/100000000000000 : ℝ)*(base1) + (1969807533/100000000000000 : ℝ)*(base19) + (967517889/50000000000000 : ℝ)*(base23) + (108583183/50000000000000 : ℝ)*(upper3) + (4057469/2000000000000 : ℝ)*(upper5) + (1150863591448209/100000000000000 : ℝ)*(major0) + (1150863591448209/100000000000000 : ℝ)*(major1) + (1150863591448209/100000000000000 : ℝ)*(major2) + (154279157873073/10000000000000 : ℝ)*(sp0) + (385700082480601/25000000000000 : ℝ)*(sp1) + (1542800364694159/100000000000000 : ℝ)*(sp2) + (379459532531863/50000000000000 : ℝ)*(sp3) + (10825196469/100000000000000 : ℝ)*(sp4) + (1350405487/25000000000000 : ℝ)*(sp7) + (151784914176587/20000000000000 : ℝ)*(f.failure) + (1542802299729937/100000000000000 : ℝ)*(f.sum) + (23483096481161/132665000000000000000000000000 : ℝ)*base65 + (85117450597507380751/13266500000000000000000000000000000 : ℝ)*base68 + (95561871902669380751/13266500000000000000000000000000000 : ℝ)*base70 + (72463395001318880751/13266500000000000000000000000000000 : ℝ)*base72 + (154772572450843/66332500000000000000000000000 : ℝ)*base73 + (60660576590194880751/13266500000000000000000000000000000 : ℝ)*base76 + (68247009597516880751/13266500000000000000000000000000000 : ℝ)*base78 + (41606166524146380751/13266500000000000000000000000000000 : ℝ)*base80 + (20349677621893/66332500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (3690587/1000000000000000000000 : ℝ)*base89 + (3690587/1000000000000000000000 : ℝ)*base91 + (3690587/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7710502229327855125881267/2072890625000000000000000000000 : ℝ) := by norm_num
    linear_combination (9671949/100000000000000 : ℝ)*(base1) + (334147943/50000000000000 : ℝ)*(base19) + (123255681/20000000000000 : ℝ)*(base23) + (1038393/1000000000000 : ℝ)*(upper3) + (771467/1000000000000 : ℝ)*(upper5) + (5910304206567/500000000000 : ℝ)*(major0) + (5910304206567/500000000000 : ℝ)*(major1) + (5910304206567/500000000000 : ℝ)*(major2) + (3582077621/100000000000000 : ℝ)*(sp1) + (334887543/12500000000000 : ℝ)*(sp2) + (1584624307802067/100000000000000 : ℝ)*(sp4) + (158462004775661/10000000000000 : ℝ)*(sp5) + (1584621002751369/100000000000000 : ℝ)*(sp6) + (194874312708799/25000000000000 : ℝ)*(sp7) + (155899452101429/20000000000000 : ℝ)*(f.failure) + (792312149065059/50000000000000 : ℝ)*(f.sum) + (8968015321333/5306600000000000000000000000 : ℝ)*base66 + (59975388820816413/66332500000000000000000000000000 : ℝ)*base68 + (559511341245351413/66332500000000000000000000000000 : ℝ)*base70 + (64963134131578913/66332500000000000000000000000000 : ℝ)*base72 + (1639840694501/829156250000000000000000000 : ℝ)*base74 + (85569978486491087/66332500000000000000000000000000 : ℝ)*base75 + (224269526809511413/66332500000000000000000000000000 : ℝ)*base78 + (163387990209211413/66332500000000000000000000000000 : ℝ)*base80 + (33802406440173/6633250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1739429/1000000000000000000000 : ℝ)*base89 + (1739429/1000000000000000000000 : ℝ)*base91 + (1739429/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1253_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5479/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (431/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (781/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1247/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1253_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1253_s2_0 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1050639681/5000000000 : ℝ)*x 0 + (2745462863/5000000000 : ℝ)*x 1 + (5176297119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050639681/5000000000 : ℝ)^4223 ≤ (6376477638529/50000000000000 : ℝ)^3199 := by
    have hnat : (1050639681 : ℕ)^4223*50000000000000^3199 ≤ 6376477638529^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050639681 5000000000 6376477638529 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745462863/5000000000 : ℝ)^4223 ≤ (22660845618247/50000000000000 : ℝ)^3199 := by
    have hnat : (2745462863 : ℕ)^4223*50000000000000^3199 ≤ 22660845618247^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745462863 5000000000 22660845618247 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5176297119/10000000000 : ℝ)^4223 ≤ (41925353470733/100000000000000 : ℝ)^3199 := by
    have hnat : (5176297119 : ℕ)^4223*100000000000000^3199 ≤ 41925353470733^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176297119 10000000000 41925353470733 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1050639681/5000000000 : ℝ), (2745462863/5000000000 : ℝ), (5176297119/10000000000 : ℝ)] ![(6376477638529/50000000000000 : ℝ), (22660845618247/50000000000000 : ℝ), (41925353470733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1050639681/5000000000 : ℝ)|^4223 ≤ (6376477638529/50000000000000 : ℝ)^3199
        have hw : |(-1050639681/5000000000 : ℝ)|=(1050639681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745462863/5000000000 : ℝ)|^4223 ≤ (22660845618247/50000000000000 : ℝ)^3199
        have hw : |(2745462863/5000000000 : ℝ)|=(2745462863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5176297119/10000000000 : ℝ)|^4223 ≤ (41925353470733/100000000000000 : ℝ)^3199
        have hw : |(5176297119/10000000000 : ℝ)|=(5176297119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s2_1 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369239943/10000000000 : ℝ)*x 0 + (-2264192723/10000000000 : ℝ)*x 1 + (2588148613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369239943/10000000000 : ℝ)^4223 ≤ (44000528723673/100000000000000 : ℝ)^3199 := by
    have hnat : (5369239943 : ℕ)^4223*100000000000000^3199 ≤ 44000528723673^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369239943 10000000000 44000528723673 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2264192723/10000000000 : ℝ)^4223 ≤ (14074116652073/100000000000000 : ℝ)^3199 := by
    have hnat : (2264192723 : ℕ)^4223*100000000000000^3199 ≤ 14074116652073^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2264192723 10000000000 14074116652073 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588148613/5000000000 : ℝ)^4223 ≤ (41925354614791/100000000000000 : ℝ)^3199 := by
    have hnat : (2588148613 : ℕ)^4223*100000000000000^3199 ≤ 41925354614791^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588148613 5000000000 41925354614791 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369239943/10000000000 : ℝ), (-2264192723/10000000000 : ℝ), (2588148613/5000000000 : ℝ)] ![(44000528723673/100000000000000 : ℝ), (14074116652073/100000000000000 : ℝ), (41925354614791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369239943/10000000000 : ℝ)|^4223 ≤ (44000528723673/100000000000000 : ℝ)^3199
        have hw : |(5369239943/10000000000 : ℝ)|=(5369239943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2264192723/10000000000 : ℝ)|^4223 ≤ (14074116652073/100000000000000 : ℝ)^3199
        have hw : |(-2264192723/10000000000 : ℝ)|=(2264192723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588148613/5000000000 : ℝ)|^4223 ≤ (41925354614791/100000000000000 : ℝ)^3199
        have hw : |(2588148613/5000000000 : ℝ)|=(2588148613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s2_2 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342309959/2500000000 : ℝ)*x 0 + (517629729/1000000000 : ℝ)*x 1 + (-113209639/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342309959/2500000000 : ℝ)^4223 ≤ (22000263783067/50000000000000 : ℝ)^3199 := by
    have hnat : (1342309959 : ℕ)^4223*50000000000000^3199 ≤ 22000263783067^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342309959 2500000000 22000263783067 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517629729/1000000000 : ℝ)^4223 ≤ (2620334706193/6250000000000 : ℝ)^3199 := by
    have hnat : (517629729 : ℕ)^4223*6250000000000^3199 ≤ 2620334706193^3199*1000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517629729 1000000000 2620334706193 6250000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (113209639/500000000 : ℝ)^4223 ≤ (14074117119797/100000000000000 : ℝ)^3199 := by
    have hnat : (113209639 : ℕ)^4223*100000000000000^3199 ≤ 14074117119797^3199*500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113209639 500000000 14074117119797 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342309959/2500000000 : ℝ), (517629729/1000000000 : ℝ), (-113209639/500000000 : ℝ)] ![(22000263783067/50000000000000 : ℝ), (2620334706193/6250000000000 : ℝ), (14074117119797/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342309959/2500000000 : ℝ)|^4223 ≤ (22000263783067/50000000000000 : ℝ)^3199
        have hw : |(1342309959/2500000000 : ℝ)|=(1342309959/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(517629729/1000000000 : ℝ)|^4223 ≤ (2620334706193/6250000000000 : ℝ)^3199
        have hw : |(517629729/1000000000 : ℝ)|=(517629729/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-113209639/500000000 : ℝ)|^4223 ≤ (14074117119797/100000000000000 : ℝ)^3199
        have hw : |(-113209639/500000000 : ℝ)|=(113209639/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s2_3 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4340729293/10000000000 : ℝ)*x 0 + (806462153/2000000000 : ℝ)*x 1 + (4671912637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4340729293/10000000000 : ℝ)^4223 ≤ (8307809327223/25000000000000 : ℝ)^3199 := by
    have hnat : (4340729293 : ℕ)^4223*25000000000000^3199 ≤ 8307809327223^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4340729293 10000000000 8307809327223 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (806462153/2000000000 : ℝ)^4223 ≤ (30150312426727/100000000000000 : ℝ)^3199 := by
    have hnat : (806462153 : ℕ)^4223*100000000000000^3199 ≤ 30150312426727^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806462153 2000000000 30150312426727 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4671912637/10000000000 : ℝ)^4223 ≤ (18309225125657/50000000000000 : ℝ)^3199 := by
    have hnat : (4671912637 : ℕ)^4223*50000000000000^3199 ≤ 18309225125657^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4671912637 10000000000 18309225125657 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4340729293/10000000000 : ℝ), (806462153/2000000000 : ℝ), (4671912637/10000000000 : ℝ)] ![(8307809327223/25000000000000 : ℝ), (30150312426727/100000000000000 : ℝ), (18309225125657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4340729293/10000000000 : ℝ)|^4223 ≤ (8307809327223/25000000000000 : ℝ)^3199
        have hw : |(4340729293/10000000000 : ℝ)|=(4340729293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(806462153/2000000000 : ℝ)|^4223 ≤ (30150312426727/100000000000000 : ℝ)^3199
        have hw : |(806462153/2000000000 : ℝ)|=(806462153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4671912637/10000000000 : ℝ)|^4223 ≤ (18309225125657/50000000000000 : ℝ)^3199
        have hw : |(4671912637/10000000000 : ℝ)|=(4671912637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s2_4 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-525338881/2500000000 : ℝ)*x 0 + (5178304419/10000000000 : ℝ)*x 1 + (274444987/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525338881/2500000000 : ℝ)^4223 ≤ (6376782740313/50000000000000 : ℝ)^3199 := by
    have hnat : (525338881 : ℕ)^4223*50000000000000^3199 ≤ 6376782740313^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525338881 2500000000 6376782740313 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5178304419/10000000000 : ℝ)^4223 ≤ (41946817122487/100000000000000 : ℝ)^3199 := by
    have hnat : (5178304419 : ℕ)^4223*100000000000000^3199 ≤ 41946817122487^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178304419 10000000000 41946817122487 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (274444987/500000000 : ℝ)^4223 ≤ (22649808691131/50000000000000 : ℝ)^3199 := by
    have hnat : (274444987 : ℕ)^4223*50000000000000^3199 ≤ 22649808691131^3199*500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274444987 500000000 22649808691131 50000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-525338881/2500000000 : ℝ), (5178304419/10000000000 : ℝ), (274444987/500000000 : ℝ)] ![(6376782740313/50000000000000 : ℝ), (41946817122487/100000000000000 : ℝ), (22649808691131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-525338881/2500000000 : ℝ)|^4223 ≤ (6376782740313/50000000000000 : ℝ)^3199
        have hw : |(-525338881/2500000000 : ℝ)|=(525338881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5178304419/10000000000 : ℝ)|^4223 ≤ (41946817122487/100000000000000 : ℝ)^3199
        have hw : |(5178304419/10000000000 : ℝ)|=(5178304419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(274444987/500000000 : ℝ)|^4223 ≤ (22649808691131/50000000000000 : ℝ)^3199
        have hw : |(274444987/500000000 : ℝ)|=(274444987/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s2_5 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2644418773/5000000000 : ℝ)*x 0 + (-1951589959/10000000000 : ℝ)*x 1 + (1097779957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644418773/5000000000 : ℝ)^4223 ≤ (2156640872659/5000000000000 : ℝ)^3199 := by
    have hnat : (2644418773 : ℕ)^4223*5000000000000^3199 ≤ 2156640872659^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644418773 5000000000 2156640872659 5000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1951589959/10000000000 : ℝ)^4223 ≤ (2891891164147/25000000000000 : ℝ)^3199 := by
    have hnat : (1951589959 : ℕ)^4223*25000000000000^3199 ≤ 2891891164147^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951589959 10000000000 2891891164147 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1097779957/2000000000 : ℝ)^4223 ≤ (11324904468131/25000000000000 : ℝ)^3199 := by
    have hnat : (1097779957 : ℕ)^4223*25000000000000^3199 ≤ 11324904468131^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097779957 2000000000 11324904468131 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644418773/5000000000 : ℝ), (-1951589959/10000000000 : ℝ), (1097779957/2000000000 : ℝ)] ![(2156640872659/5000000000000 : ℝ), (2891891164147/25000000000000 : ℝ), (11324904468131/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644418773/5000000000 : ℝ)|^4223 ≤ (2156640872659/5000000000000 : ℝ)^3199
        have hw : |(2644418773/5000000000 : ℝ)|=(2644418773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1951589959/10000000000 : ℝ)|^4223 ≤ (2891891164147/25000000000000 : ℝ)^3199
        have hw : |(-1951589959/10000000000 : ℝ)|=(1951589959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1097779957/2000000000 : ℝ)|^4223 ≤ (11324904468131/25000000000000 : ℝ)^3199
        have hw : |(1097779957/2000000000 : ℝ)|=(1097779957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s2_6 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322209423/2500000000 : ℝ)*x 0 + (1097779977/2000000000 : ℝ)*x 1 + (-1951589619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322209423/2500000000 : ℝ)^4223 ≤ (43132819025017/100000000000000 : ℝ)^3199 := by
    have hnat : (1322209423 : ℕ)^4223*100000000000000^3199 ≤ 43132819025017^3199*2500000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322209423 2500000000 43132819025017 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1097779977/2000000000 : ℝ)^4223 ≤ (11324904740499/25000000000000 : ℝ)^3199 := by
    have hnat : (1097779977 : ℕ)^4223*25000000000000^3199 ≤ 11324904740499^3199*2000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1097779977 2000000000 11324904740499 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1951589619/10000000000 : ℝ)^4223 ≤ (2891890499059/25000000000000 : ℝ)^3199 := by
    have hnat : (1951589619 : ℕ)^4223*25000000000000^3199 ≤ 2891890499059^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1951589619 10000000000 2891890499059 25000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322209423/2500000000 : ℝ), (1097779977/2000000000 : ℝ), (-1951589619/10000000000 : ℝ)] ![(43132819025017/100000000000000 : ℝ), (11324904740499/25000000000000 : ℝ), (2891890499059/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322209423/2500000000 : ℝ)|^4223 ≤ (43132819025017/100000000000000 : ℝ)^3199
        have hw : |(1322209423/2500000000 : ℝ)|=(1322209423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1097779977/2000000000 : ℝ)|^4223 ≤ (11324904740499/25000000000000 : ℝ)^3199
        have hw : |(1097779977/2000000000 : ℝ)|=(1097779977/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1951589619/10000000000 : ℝ)|^4223 ≤ (2891890499059/25000000000000 : ℝ)^3199
        have hw : |(-1951589619/10000000000 : ℝ)|=(1951589619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1253_s2_7 (p : ℝ) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2170441817/5000000000 : ℝ)*x 0 + (4667832431/10000000000 : ℝ)*x 1 + (4036428569/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2170441817/5000000000 : ℝ)^4223 ≤ (16226951723/48828125000 : ℝ)^3199 := by
    have hnat : (2170441817 : ℕ)^4223*48828125000^3199 ≤ 16226951723^3199*5000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2170441817 5000000000 16226951723 48828125000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4667832431/10000000000 : ℝ)^4223 ≤ (36576238491617/100000000000000 : ℝ)^3199 := by
    have hnat : (4667832431 : ℕ)^4223*100000000000000^3199 ≤ 36576238491617^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4667832431 10000000000 36576238491617 100000000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4036428569/10000000000 : ℝ)^4223 ≤ (3773870546057/12500000000000 : ℝ)^3199 := by
    have hnat : (4036428569 : ℕ)^4223*12500000000000^3199 ≤ 3773870546057^3199*10000000000^4223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036428569 10000000000 3773870546057 12500000000000 4223 3199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4223/1024 : ℝ)) 4223 3199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2170441817/5000000000 : ℝ), (4667832431/10000000000 : ℝ), (4036428569/10000000000 : ℝ)] ![(16226951723/48828125000 : ℝ), (36576238491617/100000000000000 : ℝ), (3773870546057/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2170441817/5000000000 : ℝ)|^4223 ≤ (16226951723/48828125000 : ℝ)^3199
        have hw : |(2170441817/5000000000 : ℝ)|=(2170441817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4667832431/10000000000 : ℝ)|^4223 ≤ (36576238491617/100000000000000 : ℝ)^3199
        have hw : |(4667832431/10000000000 : ℝ)|=(4667832431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4036428569/10000000000 : ℝ)|^4223 ≤ (3773870546057/12500000000000 : ℝ)^3199
        have hw : |(4036428569/10000000000 : ℝ)|=(4036428569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1253_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1247/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (781/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1193/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8097/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1247/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (781/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1247/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (781/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1247/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (781/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1247/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (781/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1247/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (781/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1247/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (781/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (781/12500 : ℝ) ^ (8445/2048 : ℝ) ≤ (540960763854879/50000000000000000000 : ℝ) := by
    have hpowers : (781/12500 : ℝ)^8445 ≤ (540960763854879/50000000000000000000 : ℝ)^2048 := by
      have hnat : (781 : ℕ)^8445*50000000000000000000^2048 ≤ 540960763854879^2048*12500^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781 12500 540960763854879 50000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (781/12500 : ℝ)) (X := (540960763854879/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1247/6250 : ℝ) ^ (8445/2048 : ℝ) ≤ (64929112086665273/50000000000000000000 : ℝ) := by
    have hpowers : (1247/6250 : ℝ)^8445 ≤ (64929112086665273/50000000000000000000 : ℝ)^2048 := by
      have hnat : (1247 : ℕ)^8445*50000000000000000000^2048 ≤ 64929112086665273^2048*6250^8445 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1247 6250 64929112086665273 50000000000000000000 8445 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1247/6250 : ℝ)) (X := (64929112086665273/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000540960763854879/25000000000000000000 : ℝ) ≤ (10000052475006033/10000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (25000540960763854879/25000000000000000000 : ℝ)^2048 ≤ (10000052475006033/10000000000000000 : ℝ)^8445 := by
      have hnat : (25000540960763854879 : ℕ)^2048*10000000000000000^8445 ≤ 10000052475006033^8445*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000540960763854879 25000000000000000000 10000052475006033 10000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000052475006033/10000000000000000 : ℝ)) (X := (25000540960763854879/25000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6258183759106315019/6250000000000000000 : ℝ) ≤ (500158693030969/500000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (6258183759106315019/6250000000000000000 : ℝ)^2048 ≤ (500158693030969/500000000000000 : ℝ)^8445 := by
      have hnat : (6258183759106315019 : ℕ)^2048*500000000000000^8445 ≤ 500158693030969^8445*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6258183759106315019 6250000000000000000 500158693030969 500000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500158693030969/500000000000000 : ℝ)) (X := (6258183759106315019/6250000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25064929112086665273/25000000000000000000 : ℝ) ≤ (10006295246232727/10000000000000000 : ℝ) ^ (8445/2048 : ℝ) := by
    have hpowers : (25064929112086665273/25000000000000000000 : ℝ)^2048 ≤ (10006295246232727/10000000000000000 : ℝ)^8445 := by
      have hnat : (25064929112086665273 : ℕ)^2048*10000000000000000^8445 ≤ 10006295246232727^8445*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25064929112086665273 25000000000000000000 10006295246232727 10000000000000000 2048 8445 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006295246232727/10000000000000000 : ℝ)) (X := (25064929112086665273/25000000000000000000 : ℝ)) (by norm_num) 8445 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(540960763854879/50000000000000000000 : ℝ) ≤ ((3425042857071457303/3426000000000000000 : ℝ)+2*(3121385613347/1370400000000000 : ℝ)*(781/12500 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (3425042857071457303/3426000000000000000 : ℝ)+2*(3121385613347/1370400000000000 : ℝ)*(781/12500 : ℝ)=(10000052475006033/10000000000000000 : ℝ) by norm_num, show 1+2*(540960763854879/50000000000000000000 : ℝ)=(25000540960763854879/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(64929112086665273/50000000000000000000 : ℝ)+(540960763854879/50000000000000000000 : ℝ) ≤ ((3425042857071457303/3426000000000000000 : ℝ)+(3121385613347/1370400000000000 : ℝ)*((1247/6250 : ℝ)+(781/12500 : ℝ)))^(8445/2048 : ℝ) := by
    rw [show (3425042857071457303/3426000000000000000 : ℝ)+(3121385613347/1370400000000000 : ℝ)*((1247/6250 : ℝ)+(781/12500 : ℝ))=(500158693030969/500000000000000 : ℝ) by norm_num, show 1+(64929112086665273/50000000000000000000 : ℝ)+(540960763854879/50000000000000000000 : ℝ)=(6258183759106315019/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(64929112086665273/50000000000000000000 : ℝ) ≤ ((3425042857071457303/3426000000000000000 : ℝ)+2*(3121385613347/1370400000000000 : ℝ)*(1247/6250 : ℝ))^(8445/2048 : ℝ) := by
    rw [show (3425042857071457303/3426000000000000000 : ℝ)+2*(3121385613347/1370400000000000 : ℝ)*(1247/6250 : ℝ)=(10006295246232727/10000000000000000 : ℝ) by norm_num, show 1+2*(64929112086665273/50000000000000000000 : ℝ)=(25064929112086665273/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3425042857071457303/3426000000000000000 : ℝ)*(X 1 0+X 2 0)+(3121385613347/1370400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (781/12500 : ℝ)) (hi := (1247/6250 : ℝ)) (c := (3425042857071457303/3426000000000000000 : ℝ)) (alpha := (3121385613347/1370400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3425042857071457303/3426000000000000000 : ℝ)*(X 0 1+X 2 1)+(3121385613347/1370400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (781/12500 : ℝ)) (hi := (1247/6250 : ℝ)) (c := (3425042857071457303/3426000000000000000 : ℝ)) (alpha := (3121385613347/1370400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3425042857071457303/3426000000000000000 : ℝ)*(X 0 2+X 1 2)+(3121385613347/1370400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8445/2048 : ℝ)) (lo := (781/12500 : ℝ)) (hi := (1247/6250 : ℝ)) (c := (3425042857071457303/3426000000000000000 : ℝ)) (alpha := (3121385613347/1370400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1050639681/5000000000 : ℝ)*X 0 0+(2745462863/5000000000 : ℝ)*X 0 1+(5176297119/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369239943/10000000000 : ℝ)*X 1 0+(-2264192723/10000000000 : ℝ)*X 1 1+(2588148613/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1342309959/2500000000 : ℝ)*X 2 0+(517629729/1000000000 : ℝ)*X 2 1+(-113209639/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4340729293/10000000000 : ℝ)*X 0 0+(806462153/2000000000 : ℝ)*X 0 1+(4671912637/10000000000 : ℝ)*X 0 2+(4340729293/10000000000 : ℝ)*X 1 0+(806462153/2000000000 : ℝ)*X 1 1+(4671912637/10000000000 : ℝ)*X 1 2+(4340729293/10000000000 : ℝ)*X 2 0+(806462153/2000000000 : ℝ)*X 2 1+(4671912637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-525338881/2500000000 : ℝ)*X 0 0+(5178304419/10000000000 : ℝ)*X 0 1+(274444987/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644418773/5000000000 : ℝ)*X 1 0+(-1951589959/10000000000 : ℝ)*X 1 1+(1097779957/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322209423/2500000000 : ℝ)*X 2 0+(1097779977/2000000000 : ℝ)*X 2 1+(-1951589619/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2170441817/5000000000 : ℝ)*X 0 0+(4667832431/10000000000 : ℝ)*X 0 1+(4036428569/10000000000 : ℝ)*X 0 2+(2170441817/5000000000 : ℝ)*X 1 0+(4667832431/10000000000 : ℝ)*X 1 1+(4036428569/10000000000 : ℝ)*X 1 2+(2170441817/5000000000 : ℝ)*X 2 0+(4667832431/10000000000 : ℝ)*X 2 1+(4036428569/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1253_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (14652571491026969460649701/3568750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (344383261/50000000000000 : ℝ)*(base19) + (117529359/20000000000000 : ℝ)*(base23) + (507127/2500000000000 : ℝ)*(lower2) + (15674859/12500000000000 : ℝ)*(upper3) + (10056139/25000000000000 : ℝ)*(upper5) + (296365501600617/12500000000000 : ℝ)*(major0) + (296365501600617/12500000000000 : ℝ)*(major1) + (296365501600617/12500000000000 : ℝ)*(major2) + (1589179969930631/50000000000000 : ℝ)*(sp0) + (1589183477884863/50000000000000 : ℝ)*(sp1) + (794591764222363/25000000000000 : ℝ)*(sp2) + (781738024297341/50000000000000 : ℝ)*(sp3) + (3852337493/50000000000000 : ℝ)*(sp4) + (4195618957/100000000000000 : ℝ)*(sp7) + (1563480244213639/100000000000000 : ℝ)*(f.failure) + (397295955567031/12500000000000 : ℝ)*(f.sum) + (10085782174847/2855000000000000000000000000 : ℝ)*base66 + (120232622255757183/14275000000000000000000000000000 : ℝ)*base68 + (31534213735307183/14275000000000000000000000000000 : ℝ)*base70 + (18310544602482183/14275000000000000000000000000000 : ℝ)*base72 + (2048350804653/713750000000000000000000000 : ℝ)*base74 + (120015977718257183/14275000000000000000000000000000 : ℝ)*base76 + (27694293671667817/14275000000000000000000000000000 : ℝ)*base77 + (18423261358607183/14275000000000000000000000000000 : ℝ)*base80 + (539746178369/356875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (19528361/5000000000000000000000 : ℝ)*base90 + (19528361/5000000000000000000000 : ℝ)*base92 + (19528361/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3394326601627171923409/5710000000000000000000000000 : ℝ) := by norm_num
    linear_combination (507231843/100000000000000 : ℝ)*(base19) + (213568961/25000000000000 : ℝ)*(base23) + (16317651/20000000000000 : ℝ)*(upper2) + (25650073/25000000000000 : ℝ)*(upper3) + (5618109/100000000000000 : ℝ)*(upper5) + (600424319965753/25000000000000 : ℝ)*(major0) + (600424319965753/25000000000000 : ℝ)*(major1) + (600424319965753/25000000000000 : ℝ)*(major2) + (2250547337/50000000000000 : ℝ)*(sp1) + (11335655807/100000000000000 : ℝ)*(sp2) + (1609810598478991/50000000000000 : ℝ)*(sp4) + (1609808094315733/50000000000000 : ℝ)*(sp5) + (3219609007026331/100000000000000 : ℝ)*(sp6) + (395943335738233/25000000000000 : ℝ)*(sp7) + (395943335738233/25000000000000 : ℝ)*(f.failure) + (1609810598478991/50000000000000 : ℝ)*(f.sum) + (8502277636309/17130000000000000000000000000 : ℝ)*base66 + (172921713392490553/28550000000000000000000000000000 : ℝ)*base67 + (36127847567590553/28550000000000000000000000000000 : ℝ)*base69 + (69314780191309447/28550000000000000000000000000000 : ℝ)*base72 + (135137771308811/17130000000000000000000000000 : ℝ)*base73 + (20129483594109447/28550000000000000000000000000000 : ℝ)*base76 + (119426016726609447/28550000000000000000000000000000 : ℝ)*base78 + (486491716317640553/28550000000000000000000000000000 : ℝ)*base79 + (79651089617621/17130000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (11735767/1250000000000000000000 : ℝ)*base90 + (11735767/1250000000000000000000 : ℝ)*base92 + (11735767/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1253_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1247/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (781/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1193/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1253_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1253_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1193/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1253_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1253_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1253_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8445/2048 : ℝ) ≤ p) (hpb : p ≤ (4223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75822001/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1193/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1253_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
