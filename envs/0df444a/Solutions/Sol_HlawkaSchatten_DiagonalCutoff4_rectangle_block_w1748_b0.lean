-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1748_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T02:18:30.665203+00:00
-- url     : https://prove2.me/submissions/a7aef3a0-08da-4511-9629-5b1aa8e6610d

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
theorem support_rectangle_w1748_s0_0 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-593404479/5000000000 : ℝ)*x 0 + (5636556603/10000000000 : ℝ)*x 1 + (2487419183/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (593404479/5000000000 : ℝ)^5743 ≤ (1868383282569/25000000000000 : ℝ)^4719 := by
    have hnat : (593404479 : ℕ)^5743*25000000000000^4719 ≤ 1868383282569^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      593404479 5000000000 1868383282569 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5636556603/10000000000 : ℝ)^5743 ≤ (49772000462669/100000000000000 : ℝ)^4719 := by
    have hnat : (5636556603 : ℕ)^5743*100000000000000^4719 ≤ 49772000462669^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5636556603 10000000000 49772000462669 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2487419183/5000000000 : ℝ)^5743 ≤ (21377233191509/50000000000000 : ℝ)^4719 := by
    have hnat : (2487419183 : ℕ)^5743*50000000000000^4719 ≤ 21377233191509^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2487419183 5000000000 21377233191509 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-593404479/5000000000 : ℝ), (5636556603/10000000000 : ℝ), (2487419183/5000000000 : ℝ)] ![(1868383282569/25000000000000 : ℝ), (49772000462669/100000000000000 : ℝ), (21377233191509/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-593404479/5000000000 : ℝ)|^5743 ≤ (1868383282569/25000000000000 : ℝ)^4719
        have hw : |(-593404479/5000000000 : ℝ)|=(593404479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5636556603/10000000000 : ℝ)|^5743 ≤ (49772000462669/100000000000000 : ℝ)^4719
        have hw : |(5636556603/10000000000 : ℝ)|=(5636556603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2487419183/5000000000 : ℝ)|^5743 ≤ (21377233191509/50000000000000 : ℝ)^4719
        have hw : |(2487419183/5000000000 : ℝ)|=(2487419183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s0_1 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687072309/5000000000 : ℝ)*x 0 + (-1542149777/10000000000 : ℝ)*x 1 + (4974838731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687072309/5000000000 : ℝ)^5743 ≤ (4696645620819/10000000000000 : ℝ)^4719 := by
    have hnat : (2687072309 : ℕ)^5743*10000000000000^4719 ≤ 4696645620819^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687072309 5000000000 4696645620819 10000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1542149777/10000000000 : ℝ)^5743 ≤ (5139536790917/50000000000000 : ℝ)^4719 := by
    have hnat : (1542149777 : ℕ)^5743*50000000000000^4719 ≤ 5139536790917^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1542149777 10000000000 5139536790917 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4974838731/10000000000 : ℝ)^5743 ≤ (42754470200563/100000000000000 : ℝ)^4719 := by
    have hnat : (4974838731 : ℕ)^5743*100000000000000^4719 ≤ 42754470200563^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4974838731 10000000000 42754470200563 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687072309/5000000000 : ℝ), (-1542149777/10000000000 : ℝ), (4974838731/10000000000 : ℝ)] ![(4696645620819/10000000000000 : ℝ), (5139536790917/50000000000000 : ℝ), (42754470200563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687072309/5000000000 : ℝ)|^5743 ≤ (4696645620819/10000000000000 : ℝ)^4719
        have hw : |(2687072309/5000000000 : ℝ)|=(2687072309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1542149777/10000000000 : ℝ)|^5743 ≤ (5139536790917/50000000000000 : ℝ)^4719
        have hw : |(-1542149777/10000000000 : ℝ)|=(1542149777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4974838731/10000000000 : ℝ)|^5743 ≤ (42754470200563/100000000000000 : ℝ)^4719
        have hw : |(4974838731/10000000000 : ℝ)|=(4974838731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s0_2 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5374145951/10000000000 : ℝ)*x 0 + (1243709491/2500000000 : ℝ)*x 1 + (-771074509/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374145951/10000000000 : ℝ)^5743 ≤ (46966470385617/100000000000000 : ℝ)^4719 := by
    have hnat : (5374145951 : ℕ)^5743*100000000000000^4719 ≤ 46966470385617^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374145951 10000000000 46966470385617 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1243709491/2500000000 : ℝ)^5743 ≤ (5344307772311/12500000000000 : ℝ)^4719 := by
    have hnat : (1243709491 : ℕ)^5743*12500000000000^4719 ≤ 5344307772311^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1243709491 2500000000 5344307772311 12500000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (771074509/5000000000 : ℝ)^5743 ≤ (321220857031/3125000000000 : ℝ)^4719 := by
    have hnat : (771074509 : ℕ)^5743*3125000000000^4719 ≤ 321220857031^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      771074509 5000000000 321220857031 3125000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374145951/10000000000 : ℝ), (1243709491/2500000000 : ℝ), (-771074509/5000000000 : ℝ)] ![(46966470385617/100000000000000 : ℝ), (5344307772311/12500000000000 : ℝ), (321220857031/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374145951/10000000000 : ℝ)|^5743 ≤ (46966470385617/100000000000000 : ℝ)^4719
        have hw : |(5374145951/10000000000 : ℝ)|=(5374145951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1243709491/2500000000 : ℝ)|^5743 ≤ (5344307772311/12500000000000 : ℝ)^4719
        have hw : |(1243709491/2500000000 : ℝ)|=(1243709491/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-771074509/5000000000 : ℝ)|^5743 ≤ (321220857031/3125000000000 : ℝ)^4719
        have hw : |(-771074509/5000000000 : ℝ)|=(771074509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s0_3 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1990252177/5000000000 : ℝ)*x 0 + (2982090449/10000000000 : ℝ)*x 1 + (2569240141/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1990252177/5000000000 : ℝ)^5743 ≤ (2037073217587/6250000000000 : ℝ)^4719 := by
    have hnat : (1990252177 : ℕ)^5743*6250000000000^4719 ≤ 2037073217587^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990252177 5000000000 2037073217587 6250000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2982090449/10000000000 : ℝ)^5743 ≤ (11467384997193/50000000000000 : ℝ)^4719 := by
    have hnat : (2982090449 : ℕ)^5743*50000000000000^4719 ≤ 11467384997193^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2982090449 10000000000 11467384997193 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569240141/5000000000 : ℝ)^5743 ≤ (44472058506339/100000000000000 : ℝ)^4719 := by
    have hnat : (2569240141 : ℕ)^5743*100000000000000^4719 ≤ 44472058506339^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569240141 5000000000 44472058506339 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1990252177/5000000000 : ℝ), (2982090449/10000000000 : ℝ), (2569240141/5000000000 : ℝ)] ![(2037073217587/6250000000000 : ℝ), (11467384997193/50000000000000 : ℝ), (44472058506339/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1990252177/5000000000 : ℝ)|^5743 ≤ (2037073217587/6250000000000 : ℝ)^4719
        have hw : |(1990252177/5000000000 : ℝ)|=(1990252177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2982090449/10000000000 : ℝ)|^5743 ≤ (11467384997193/50000000000000 : ℝ)^4719
        have hw : |(2982090449/10000000000 : ℝ)|=(2982090449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569240141/5000000000 : ℝ)|^5743 ≤ (44472058506339/100000000000000 : ℝ)^4719
        have hw : |(2569240141/5000000000 : ℝ)|=(2569240141/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s0_4 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1188215969/10000000000 : ℝ)*x 0 + (2495874867/5000000000 : ℝ)*x 1 + (1404770471/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1188215969/10000000000 : ℝ)^5743 ≤ (1496863463017/20000000000000 : ℝ)^4719 := by
    have hnat : (1188215969 : ℕ)^5743*20000000000000^4719 ≤ 1496863463017^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1188215969 10000000000 1496863463017 20000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2495874867/5000000000 : ℝ)^5743 ≤ (42931408044731/100000000000000 : ℝ)^4719 := by
    have hnat : (2495874867 : ℕ)^5743*100000000000000^4719 ≤ 42931408044731^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495874867 5000000000 42931408044731 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1404770471/2500000000 : ℝ)^5743 ≤ (49584274630847/100000000000000 : ℝ)^4719 := by
    have hnat : (1404770471 : ℕ)^5743*100000000000000^4719 ≤ 49584274630847^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404770471 2500000000 49584274630847 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1188215969/10000000000 : ℝ), (2495874867/5000000000 : ℝ), (1404770471/2500000000 : ℝ)] ![(1496863463017/20000000000000 : ℝ), (42931408044731/100000000000000 : ℝ), (49584274630847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1188215969/10000000000 : ℝ)|^5743 ≤ (1496863463017/20000000000000 : ℝ)^4719
        have hw : |(-1188215969/10000000000 : ℝ)|=(1188215969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2495874867/5000000000 : ℝ)|^5743 ≤ (42931408044731/100000000000000 : ℝ)^4719
        have hw : |(2495874867/5000000000 : ℝ)|=(2495874867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1404770471/2500000000 : ℝ)|^5743 ≤ (49584274630847/100000000000000 : ℝ)^4719
        have hw : |(1404770471/2500000000 : ℝ)|=(1404770471/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s0_5 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1299353871/2500000000 : ℝ)*x 0 + (-179581111/2000000000 : ℝ)*x 1 + (702385249/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1299353871/2500000000 : ℝ)^5743 ≤ (22546788922231/50000000000000 : ℝ)^4719 := by
    have hnat : (1299353871 : ℕ)^5743*50000000000000^4719 ≤ 22546788922231^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1299353871 2500000000 22546788922231 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179581111/2000000000 : ℝ)^5743 ≤ (5322146354587/100000000000000 : ℝ)^4719 := by
    have hnat : (179581111 : ℕ)^5743*100000000000000^4719 ≤ 5322146354587^4719*2000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179581111 2000000000 5322146354587 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (702385249/1250000000 : ℝ)^5743 ≤ (12396068947667/25000000000000 : ℝ)^4719 := by
    have hnat : (702385249 : ℕ)^5743*25000000000000^4719 ≤ 12396068947667^4719*1250000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702385249 1250000000 12396068947667 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1299353871/2500000000 : ℝ), (-179581111/2000000000 : ℝ), (702385249/1250000000 : ℝ)] ![(22546788922231/50000000000000 : ℝ), (5322146354587/100000000000000 : ℝ), (12396068947667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1299353871/2500000000 : ℝ)|^5743 ≤ (22546788922231/50000000000000 : ℝ)^4719
        have hw : |(1299353871/2500000000 : ℝ)|=(1299353871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179581111/2000000000 : ℝ)|^5743 ≤ (5322146354587/100000000000000 : ℝ)^4719
        have hw : |(-179581111/2000000000 : ℝ)|=(179581111/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(702385249/1250000000 : ℝ)|^5743 ≤ (12396068947667/25000000000000 : ℝ)^4719
        have hw : |(702385249/1250000000 : ℝ)|=(702385249/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s0_6 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5197415149/10000000000 : ℝ)*x 0 + (2809540983/5000000000 : ℝ)*x 1 + (-448953041/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5197415149/10000000000 : ℝ)^5743 ≤ (45093574307251/100000000000000 : ℝ)^4719 := by
    have hnat : (5197415149 : ℕ)^5743*100000000000000^4719 ≤ 45093574307251^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5197415149 10000000000 45093574307251 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2809540983/5000000000 : ℝ)^5743 ≤ (12396068877863/25000000000000 : ℝ)^4719 := by
    have hnat : (2809540983 : ℕ)^5743*25000000000000^4719 ≤ 12396068877863^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2809540983 5000000000 12396068877863 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448953041/5000000000 : ℝ)^5743 ≤ (5322150156093/100000000000000 : ℝ)^4719 := by
    have hnat : (448953041 : ℕ)^5743*100000000000000^4719 ≤ 5322150156093^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448953041 5000000000 5322150156093 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5197415149/10000000000 : ℝ), (2809540983/5000000000 : ℝ), (-448953041/5000000000 : ℝ)] ![(45093574307251/100000000000000 : ℝ), (12396068877863/25000000000000 : ℝ), (5322150156093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5197415149/10000000000 : ℝ)|^5743 ≤ (45093574307251/100000000000000 : ℝ)^4719
        have hw : |(5197415149/10000000000 : ℝ)|=(5197415149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2809540983/5000000000 : ℝ)|^5743 ≤ (12396068877863/25000000000000 : ℝ)^4719
        have hw : |(2809540983/5000000000 : ℝ)|=(2809540983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-448953041/5000000000 : ℝ)|^5743 ≤ (5322150156093/100000000000000 : ℝ)^4719
        have hw : |(-448953041/5000000000 : ℝ)|=(448953041/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s0_7 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1992544959/5000000000 : ℝ)*x 0 + (1270842243/2500000000 : ℝ)*x 1 + (3039036233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1992544959/5000000000 : ℝ)^5743 ≤ (6527774468413/20000000000000 : ℝ)^4719 := by
    have hnat : (1992544959 : ℕ)^5743*20000000000000^4719 ≤ 6527774468413^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992544959 5000000000 6527774468413 20000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1270842243/2500000000 : ℝ)^5743 ≤ (5486532845323/12500000000000 : ℝ)^4719 := by
    have hnat : (1270842243 : ℕ)^5743*12500000000000^4719 ≤ 5486532845323^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1270842243 2500000000 5486532845323 12500000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3039036233/10000000000 : ℝ)^5743 ≤ (11734432441817/50000000000000 : ℝ)^4719 := by
    have hnat : (3039036233 : ℕ)^5743*50000000000000^4719 ≤ 11734432441817^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3039036233 10000000000 11734432441817 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1992544959/5000000000 : ℝ), (1270842243/2500000000 : ℝ), (3039036233/10000000000 : ℝ)] ![(6527774468413/20000000000000 : ℝ), (5486532845323/12500000000000 : ℝ), (11734432441817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1992544959/5000000000 : ℝ)|^5743 ≤ (6527774468413/20000000000000 : ℝ)^4719
        have hw : |(1992544959/5000000000 : ℝ)|=(1992544959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1270842243/2500000000 : ℝ)|^5743 ≤ (5486532845323/12500000000000 : ℝ)^4719
        have hw : |(1270842243/2500000000 : ℝ)|=(1270842243/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3039036233/10000000000 : ℝ)|^5743 ≤ (11734432441817/50000000000000 : ℝ)^4719
        have hw : |(3039036233/10000000000 : ℝ)|=(3039036233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1748_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1661/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1047/5000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (5727/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^5727 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^5727*1^1024 ≤ 0^1024*1^5727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 5727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (5727/1024 : ℝ) ≤ (297427892708491431/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^5727 ≤ (297427892708491431/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^5727*50000000000000000000^1024 ≤ 297427892708491431^1024*5^5727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 297427892708491431 50000000000000000000 5727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (297427892708491431/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^5727 := by
      have hnat : (1 : ℕ)^1024*1^5727 ≤ 1^5727*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50297427892708491431/50000000000000000000 : ℝ) ≤ (10010610265168321/10000000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (50297427892708491431/50000000000000000000 : ℝ)^1024 ≤ (10010610265168321/10000000000000000 : ℝ)^5727 := by
      have hnat : (50297427892708491431 : ℕ)^1024*10000000000000000^5727 ≤ 10010610265168321^5727*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50297427892708491431 50000000000000000000 10010610265168321 10000000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010610265168321/10000000000000000 : ℝ)) (X := (50297427892708491431/50000000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25297427892708491431/25000000000000000000 : ℝ) ≤ (5010610265168321/5000000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (25297427892708491431/25000000000000000000 : ℝ)^1024 ≤ (5010610265168321/5000000000000000 : ℝ)^5727 := by
      have hnat : (25297427892708491431 : ℕ)^1024*5000000000000000^5727 ≤ 5010610265168321^5727*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25297427892708491431 25000000000000000000 5010610265168321 5000000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010610265168321/5000000000000000 : ℝ)) (X := (25297427892708491431/25000000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(10610265168321/4000000000000000 : ℝ)*(0 : ℝ))^(5727/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10610265168321/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(297427892708491431/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(10610265168321/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(5727/1024 : ℝ) := by
    rw [show (1 : ℝ)+(10610265168321/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10010610265168321/10000000000000000 : ℝ) by norm_num, show 1+(297427892708491431/50000000000000000000 : ℝ)+(0 : ℝ)=(50297427892708491431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(297427892708491431/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(10610265168321/4000000000000000 : ℝ)*(2/5 : ℝ))^(5727/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(10610265168321/4000000000000000 : ℝ)*(2/5 : ℝ)=(5010610265168321/5000000000000000 : ℝ) by norm_num, show 1+2*(297427892708491431/50000000000000000000 : ℝ)=(25297427892708491431/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(10610265168321/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10610265168321/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(10610265168321/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10610265168321/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(10610265168321/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (10610265168321/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-593404479/5000000000 : ℝ)*X 0 0+(5636556603/10000000000 : ℝ)*X 0 1+(2487419183/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2687072309/5000000000 : ℝ)*X 1 0+(-1542149777/10000000000 : ℝ)*X 1 1+(4974838731/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5374145951/10000000000 : ℝ)*X 2 0+(1243709491/2500000000 : ℝ)*X 2 1+(-771074509/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1990252177/5000000000 : ℝ)*X 0 0+(2982090449/10000000000 : ℝ)*X 0 1+(2569240141/5000000000 : ℝ)*X 0 2+(1990252177/5000000000 : ℝ)*X 1 0+(2982090449/10000000000 : ℝ)*X 1 1+(2569240141/5000000000 : ℝ)*X 1 2+(1990252177/5000000000 : ℝ)*X 2 0+(2982090449/10000000000 : ℝ)*X 2 1+(2569240141/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1188215969/10000000000 : ℝ)*X 0 0+(2495874867/5000000000 : ℝ)*X 0 1+(1404770471/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1299353871/2500000000 : ℝ)*X 1 0+(-179581111/2000000000 : ℝ)*X 1 1+(702385249/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5197415149/10000000000 : ℝ)*X 2 0+(2809540983/5000000000 : ℝ)*X 2 1+(-448953041/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1992544959/5000000000 : ℝ)*X 0 0+(1270842243/2500000000 : ℝ)*X 0 1+(3039036233/10000000000 : ℝ)*X 0 2+(1992544959/5000000000 : ℝ)*X 1 0+(1270842243/2500000000 : ℝ)*X 1 1+(3039036233/10000000000 : ℝ)*X 1 2+(1992544959/5000000000 : ℝ)*X 2 0+(1270842243/2500000000 : ℝ)*X 2 1+(3039036233/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8308320329419858331937/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (139596367/50000000000000 : ℝ)*(base19) + (120111653/25000000000000 : ℝ)*(base23) + (67123833/100000000000000 : ℝ)*(base24) + (28607799/50000000000000 : ℝ)*(upper4) + (53067989/50000000000000 : ℝ)*(upper5) + (123435020306299/12500000000000 : ℝ)*(major0) + (123435020306299/12500000000000 : ℝ)*(major1) + (123435020306299/12500000000000 : ℝ)*(major2) + (755608886304257/50000000000000 : ℝ)*(sp0) + (377805131834261/25000000000000 : ℝ)*(sp1) + (755610129479667/50000000000000 : ℝ)*(sp2) + (28983673416521/6250000000000 : ℝ)*(sp3) + (189620079/6250000000000 : ℝ)*(sp4) + (344158931/50000000000000 : ℝ)*(sp7) + (231869731491099/50000000000000 : ℝ)*(f.failure) + (755610403264889/50000000000000 : ℝ)*(f.sum) + (94295314246021/25000000000000000000000000000 : ℝ)*base66 + (79593889253979/50000000000000000000000000000 : ℝ)*base67 + (156085093346021/50000000000000000000000000000 : ℝ)*base70 + (253220961046021/50000000000000000000000000000 : ℝ)*base72 + (13444426946021/25000000000000000000000000000 : ℝ)*base74 + (126686176546021/50000000000000000000000000000 : ℝ)*base76 + (223477333146021/50000000000000000000000000000 : ℝ)*base78 + (482690823646021/50000000000000000000000000000 : ℝ)*base80 + (118229853096021/25000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (31412017/2500000000000000000000 : ℝ)*base89 + (31412017/2500000000000000000000 : ℝ)*base91 + (31412017/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19220150812593421709541/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1008092597/50000000000000 : ℝ)*(base19) + (75719617/4000000000000 : ℝ)*(base23) + (3866879/50000000000000 : ℝ)*(upper2) + (344004981/100000000000000 : ℝ)*(upper3) + (2395997/781250000000 : ℝ)*(upper5) + (20832086823607/2000000000000 : ℝ)*(major0) + (20832086823607/2000000000000 : ℝ)*(major1) + (20832086823607/2000000000000 : ℝ)*(major2) + (8637808217/100000000000000 : ℝ)*(sp1) + (3799357193/50000000000000 : ℝ)*(sp2) + (797025577721661/50000000000000 : ℝ)*(sp4) + (199255062681239/12500000000000 : ℝ)*(sp5) + (99627603983657/6250000000000 : ℝ)*(sp6) + (244578603290761/50000000000000 : ℝ)*(sp7) + (244578603290761/50000000000000 : ℝ)*(f.failure) + (797025577721661/50000000000000 : ℝ)*(f.sum) + (4157853358153/4000000000000000000000000000 : ℝ)*base66 + (62739202502153/8000000000000000000000000000 : ℝ)*base68 + (12310030838153/8000000000000000000000000000 : ℝ)*base70 + (78613978326153/8000000000000000000000000000 : ℝ)*base72 + (12336264893847/4000000000000000000000000000 : ℝ)*base73 + (97524900302153/8000000000000000000000000000 : ℝ)*base76 + (68893225206153/8000000000000000000000000000 : ℝ)*base78 + (132651589286153/8000000000000000000000000000 : ℝ)*base80 + (19366156577847/4000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (14194363/2500000000000000000000 : ℝ)*base89 + (14194363/2500000000000000000000 : ℝ)*base91 + (14194363/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1748_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1661/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1047/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1748_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1748_s1_0 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1232261349/10000000000 : ℝ)*x 0 + (5503373921/10000000000 : ℝ)*x 1 + (1015531173/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1232261349/10000000000 : ℝ)^5743 ≤ (977912021331/12500000000000 : ℝ)^4719 := by
    have hnat : (1232261349 : ℕ)^5743*12500000000000^4719 ≤ 977912021331^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232261349 10000000000 977912021331 12500000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5503373921/10000000000 : ℝ)^5743 ≤ (1933778710451/4000000000000 : ℝ)^4719 := by
    have hnat : (5503373921 : ℕ)^5743*4000000000000^4719 ≤ 1933778710451^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5503373921 10000000000 1933778710451 4000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1015531173/2000000000 : ℝ)^5743 ≤ (43832236050253/100000000000000 : ℝ)^4719 := by
    have hnat : (1015531173 : ℕ)^5743*100000000000000^4719 ≤ 43832236050253^4719*2000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015531173 2000000000 43832236050253 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1232261349/10000000000 : ℝ), (5503373921/10000000000 : ℝ), (1015531173/2000000000 : ℝ)] ![(977912021331/12500000000000 : ℝ), (1933778710451/4000000000000 : ℝ), (43832236050253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1232261349/10000000000 : ℝ)|^5743 ≤ (977912021331/12500000000000 : ℝ)^4719
        have hw : |(-1232261349/10000000000 : ℝ)|=(1232261349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5503373921/10000000000 : ℝ)|^5743 ≤ (1933778710451/4000000000000 : ℝ)^4719
        have hw : |(5503373921/10000000000 : ℝ)|=(5503373921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1015531173/2000000000 : ℝ)|^5743 ≤ (43832236050253/100000000000000 : ℝ)^4719
        have hw : |(1015531173/2000000000 : ℝ)|=(1015531173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s1_1 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1067738953/2000000000 : ℝ)*x 0 + (-363798061/2500000000 : ℝ)*x 1 + (5077655753/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1067738953/2000000000 : ℝ)^5743 ≤ (46589691468131/100000000000000 : ℝ)^4719 := by
    have hnat : (1067738953 : ℕ)^5743*100000000000000^4719 ≤ 46589691468131^4719*2000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067738953 2000000000 46589691468131 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (363798061/2500000000 : ℝ)^5743 ≤ (2394518410051/25000000000000 : ℝ)^4719 := by
    have hnat : (363798061 : ℕ)^5743*25000000000000^4719 ≤ 2394518410051^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363798061 2500000000 2394518410051 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5077655753/10000000000 : ℝ)^5743 ≤ (43832234873631/100000000000000 : ℝ)^4719 := by
    have hnat : (5077655753 : ℕ)^5743*100000000000000^4719 ≤ 43832234873631^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5077655753 10000000000 43832234873631 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1067738953/2000000000 : ℝ), (-363798061/2500000000 : ℝ), (5077655753/10000000000 : ℝ)] ![(46589691468131/100000000000000 : ℝ), (2394518410051/25000000000000 : ℝ), (43832234873631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1067738953/2000000000 : ℝ)|^5743 ≤ (46589691468131/100000000000000 : ℝ)^4719
        have hw : |(1067738953/2000000000 : ℝ)|=(1067738953/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-363798061/2500000000 : ℝ)|^5743 ≤ (2394518410051/25000000000000 : ℝ)^4719
        have hw : |(-363798061/2500000000 : ℝ)|=(363798061/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5077655753/10000000000 : ℝ)|^5743 ≤ (43832234873631/100000000000000 : ℝ)^4719
        have hw : |(5077655753/10000000000 : ℝ)|=(5077655753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s1_2 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2669347171/5000000000 : ℝ)*x 0 + (634707003/1250000000 : ℝ)*x 1 + (-1455192451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2669347171/5000000000 : ℝ)^5743 ≤ (23294843487837/50000000000000 : ℝ)^4719 := by
    have hnat : (2669347171 : ℕ)^5743*50000000000000^4719 ≤ 23294843487837^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2669347171 5000000000 23294843487837 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (634707003/1250000000 : ℝ)^5743 ≤ (43832237720637/100000000000000 : ℝ)^4719 := by
    have hnat : (634707003 : ℕ)^5743*100000000000000^4719 ≤ 43832237720637^4719*1250000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      634707003 1250000000 43832237720637 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1455192451/10000000000 : ℝ)^5743 ≤ (1197259412291/12500000000000 : ℝ)^4719 := by
    have hnat : (1455192451 : ℕ)^5743*12500000000000^4719 ≤ 1197259412291^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1455192451 10000000000 1197259412291 12500000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2669347171/5000000000 : ℝ), (634707003/1250000000 : ℝ), (-1455192451/10000000000 : ℝ)] ![(23294843487837/50000000000000 : ℝ), (43832237720637/100000000000000 : ℝ), (1197259412291/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2669347171/5000000000 : ℝ)|^5743 ≤ (23294843487837/50000000000000 : ℝ)^4719
        have hw : |(2669347171/5000000000 : ℝ)|=(2669347171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(634707003/1250000000 : ℝ)|^5743 ≤ (43832237720637/100000000000000 : ℝ)^4719
        have hw : |(634707003/1250000000 : ℝ)|=(634707003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1455192451/10000000000 : ℝ)|^5743 ≤ (1197259412291/12500000000000 : ℝ)^4719
        have hw : |(-1455192451/10000000000 : ℝ)|=(1455192451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s1_3 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (804826449/2000000000 : ℝ)*x 0 + (84082403/250000000 : ℝ)*x 1 + (2375306537/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (804826449/2000000000 : ℝ)^5743 ≤ (2064277437141/6250000000000 : ℝ)^4719 := by
    have hnat : (804826449 : ℕ)^5743*6250000000000^4719 ≤ 2064277437141^4719*2000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      804826449 2000000000 2064277437141 6250000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84082403/250000000 : ℝ)^5743 ≤ (13275333653967/50000000000000 : ℝ)^4719 := by
    have hnat : (84082403 : ℕ)^5743*50000000000000^4719 ≤ 13275333653967^4719*250000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84082403 250000000 13275333653967 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2375306537/5000000000 : ℝ)^5743 ≤ (10105223419853/25000000000000 : ℝ)^4719 := by
    have hnat : (2375306537 : ℕ)^5743*25000000000000^4719 ≤ 10105223419853^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2375306537 5000000000 10105223419853 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(804826449/2000000000 : ℝ), (84082403/250000000 : ℝ), (2375306537/5000000000 : ℝ)] ![(2064277437141/6250000000000 : ℝ), (13275333653967/50000000000000 : ℝ), (10105223419853/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(804826449/2000000000 : ℝ)|^5743 ≤ (2064277437141/6250000000000 : ℝ)^4719
        have hw : |(804826449/2000000000 : ℝ)|=(804826449/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84082403/250000000 : ℝ)|^5743 ≤ (13275333653967/50000000000000 : ℝ)^4719
        have hw : |(84082403/250000000 : ℝ)|=(84082403/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2375306537/5000000000 : ℝ)|^5743 ≤ (10105223419853/25000000000000 : ℝ)^4719
        have hw : |(2375306537/5000000000 : ℝ)|=(2375306537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s1_4 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1232633199/10000000000 : ℝ)*x 0 + (5084665009/10000000000 : ℝ)*x 1 + (43969723/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1232633199/10000000000 : ℝ)^5743 ≤ (3913084658629/50000000000000 : ℝ)^4719 := by
    have hnat : (1232633199 : ℕ)^5743*50000000000000^4719 ≤ 3913084658629^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1232633199 10000000000 3913084658629 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5084665009/10000000000 : ℝ)^5743 ≤ (21952941028187/50000000000000 : ℝ)^4719 := by
    have hnat : (5084665009 : ℕ)^5743*50000000000000^4719 ≤ 21952941028187^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5084665009 10000000000 21952941028187 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43969723/80000000 : ℝ)^5743 ≤ (24133974308539/50000000000000 : ℝ)^4719 := by
    have hnat : (43969723 : ℕ)^5743*50000000000000^4719 ≤ 24133974308539^4719*80000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43969723 80000000 24133974308539 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1232633199/10000000000 : ℝ), (5084665009/10000000000 : ℝ), (43969723/80000000 : ℝ)] ![(3913084658629/50000000000000 : ℝ), (21952941028187/50000000000000 : ℝ), (24133974308539/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1232633199/10000000000 : ℝ)|^5743 ≤ (3913084658629/50000000000000 : ℝ)^4719
        have hw : |(-1232633199/10000000000 : ℝ)|=(1232633199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5084665009/10000000000 : ℝ)|^5743 ≤ (21952941028187/50000000000000 : ℝ)^4719
        have hw : |(5084665009/10000000000 : ℝ)|=(5084665009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43969723/80000000 : ℝ)|^5743 ≤ (24133974308539/50000000000000 : ℝ)^4719
        have hw : |(43969723/80000000 : ℝ)|=(43969723/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s1_5 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (40826263/78125000 : ℝ)*x 0 + (-1036632763/10000000000 : ℝ)*x 1 + (2748107687/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (40826263/78125000 : ℝ)^5743 ≤ (22696528701679/50000000000000 : ℝ)^4719 := by
    have hnat : (40826263 : ℕ)^5743*50000000000000^4719 ≤ 22696528701679^4719*78125000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40826263 78125000 22696528701679 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036632763/10000000000 : ℝ)^5743 ≤ (6338993966529/100000000000000 : ℝ)^4719 := by
    have hnat : (1036632763 : ℕ)^5743*100000000000000^4719 ≤ 6338993966529^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036632763 10000000000 6338993966529 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2748107687/5000000000 : ℝ)^5743 ≤ (48267948606391/100000000000000 : ℝ)^4719 := by
    have hnat : (2748107687 : ℕ)^5743*100000000000000^4719 ≤ 48267948606391^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748107687 5000000000 48267948606391 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(40826263/78125000 : ℝ), (-1036632763/10000000000 : ℝ), (2748107687/5000000000 : ℝ)] ![(22696528701679/50000000000000 : ℝ), (6338993966529/100000000000000 : ℝ), (48267948606391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(40826263/78125000 : ℝ)|^5743 ≤ (22696528701679/50000000000000 : ℝ)^4719
        have hw : |(40826263/78125000 : ℝ)|=(40826263/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1036632763/10000000000 : ℝ)|^5743 ≤ (6338993966529/100000000000000 : ℝ)^4719
        have hw : |(-1036632763/10000000000 : ℝ)|=(1036632763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2748107687/5000000000 : ℝ)|^5743 ≤ (48267948606391/100000000000000 : ℝ)^4719
        have hw : |(2748107687/5000000000 : ℝ)|=(2748107687/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s1_6 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225761531/10000000000 : ℝ)*x 0 + (2748107787/5000000000 : ℝ)*x 1 + (-1036632667/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225761531/10000000000 : ℝ)^5743 ≤ (363144447979/800000000000 : ℝ)^4719 := by
    have hnat : (5225761531 : ℕ)^5743*800000000000^4719 ≤ 363144447979^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225761531 10000000000 363144447979 800000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2748107787/5000000000 : ℝ)^5743 ≤ (48267950743929/100000000000000 : ℝ)^4719 := by
    have hnat : (2748107787 : ℕ)^5743*100000000000000^4719 ≤ 48267950743929^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748107787 5000000000 48267950743929 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036632667/10000000000 : ℝ)^5743 ≤ (3169496626053/50000000000000 : ℝ)^4719 := by
    have hnat : (1036632667 : ℕ)^5743*50000000000000^4719 ≤ 3169496626053^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036632667 10000000000 3169496626053 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225761531/10000000000 : ℝ), (2748107787/5000000000 : ℝ), (-1036632667/10000000000 : ℝ)] ![(363144447979/800000000000 : ℝ), (48267950743929/100000000000000 : ℝ), (3169496626053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225761531/10000000000 : ℝ)|^5743 ≤ (363144447979/800000000000 : ℝ)^4719
        have hw : |(5225761531/10000000000 : ℝ)|=(5225761531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2748107787/5000000000 : ℝ)|^5743 ≤ (48267950743929/100000000000000 : ℝ)^4719
        have hw : |(2748107787/5000000000 : ℝ)|=(2748107787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1036632667/10000000000 : ℝ)|^5743 ≤ (3169496626053/50000000000000 : ℝ)^4719
        have hw : |(-1036632667/10000000000 : ℝ)|=(1036632667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s1_7 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (503168013/1250000000 : ℝ)*x 0 + (94555467/200000000 : ℝ)*x 1 + (3386622831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503168013/1250000000 : ℝ)^5743 ≤ (264324353321/800000000000 : ℝ)^4719 := by
    have hnat : (503168013 : ℕ)^5743*800000000000^4719 ≤ 264324353321^4719*1250000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503168013 1250000000 264324353321 800000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (94555467/200000000 : ℝ)^5743 ≤ (40184514588739/100000000000000 : ℝ)^4719 := by
    have hnat : (94555467 : ℕ)^5743*100000000000000^4719 ≤ 40184514588739^4719*200000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94555467 200000000 40184514588739 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3386622831/10000000000 : ℝ)^5743 ≤ (13387470615031/50000000000000 : ℝ)^4719 := by
    have hnat : (3386622831 : ℕ)^5743*50000000000000^4719 ≤ 13387470615031^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3386622831 10000000000 13387470615031 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(503168013/1250000000 : ℝ), (94555467/200000000 : ℝ), (3386622831/10000000000 : ℝ)] ![(264324353321/800000000000 : ℝ), (40184514588739/100000000000000 : ℝ), (13387470615031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(503168013/1250000000 : ℝ)|^5743 ≤ (264324353321/800000000000 : ℝ)^4719
        have hw : |(503168013/1250000000 : ℝ)|=(503168013/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(94555467/200000000 : ℝ)|^5743 ≤ (40184514588739/100000000000000 : ℝ)^4719
        have hw : |(94555467/200000000 : ℝ)|=(94555467/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3386622831/10000000000 : ℝ)|^5743 ≤ (13387470615031/50000000000000 : ℝ)^4719
        have hw : |(3386622831/10000000000 : ℝ)|=(3386622831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1748_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1047/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (8951/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4523/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1047/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1047/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1661/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1047/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1047/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1661/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1047/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1047/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1661/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1661/25000 : ℝ) ^ (5727/1024 : ℝ) ≤ (12974352211029/50000000000000000000 : ℝ) := by
    have hpowers : (1661/25000 : ℝ)^5727 ≤ (12974352211029/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1661 : ℕ)^5727*50000000000000000000^1024 ≤ 12974352211029^1024*25000^5727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1661 25000 12974352211029 50000000000000000000 5727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1661/25000 : ℝ)) (X := (12974352211029/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1047/5000 : ℝ) ^ (5727/1024 : ℝ) ≤ (3983973181552387/25000000000000000000 : ℝ) := by
    have hpowers : (1047/5000 : ℝ)^5727 ≤ (3983973181552387/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1047 : ℕ)^5727*25000000000000000000^1024 ≤ 3983973181552387^1024*5000^5727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1047 5000 3983973181552387 25000000000000000000 5727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1047/5000 : ℝ)) (X := (3983973181552387/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000012974352211029/25000000000000000000 : ℝ) ≤ (1000000092793671/1000000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (25000012974352211029/25000000000000000000 : ℝ)^1024 ≤ (1000000092793671/1000000000000000 : ℝ)^5727 := by
      have hnat : (25000012974352211029 : ℕ)^1024*1000000000000000^5727 ≤ 1000000092793671^5727*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000012974352211029 25000000000000000000 1000000092793671 1000000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000092793671/1000000000000000 : ℝ)) (X := (25000012974352211029/25000000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50007980920715315803/50000000000000000000 : ℝ) ≤ (1250035672809709/1250000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (50007980920715315803/50000000000000000000 : ℝ)^1024 ≤ (1250035672809709/1250000000000000 : ℝ)^5727 := by
      have hnat : (50007980920715315803 : ℕ)^1024*1250000000000000^5727 ≤ 1250035672809709^5727*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007980920715315803 50000000000000000000 1250035672809709 1250000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250035672809709/1250000000000000 : ℝ)) (X := (50007980920715315803/50000000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503983973181552387/12500000000000000000 : ℝ) ≤ (5000284918509317/5000000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (12503983973181552387/12500000000000000000 : ℝ)^1024 ≤ (5000284918509317/5000000000000000 : ℝ)^5727 := by
      have hnat : (12503983973181552387 : ℕ)^1024*5000000000000000^5727 ≤ 5000284918509317^5727*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503983973181552387 12500000000000000000 5000284918509317 5000000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000284918509317/5000000000000000 : ℝ)) (X := (12503983973181552387/12500000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12974352211029/50000000000000000000 : ℝ) ≤ ((2233691147403795361/2233750000000000000 : ℝ)+2*(142227270481/714800000000000 : ℝ)*(1661/25000 : ℝ))^(5727/1024 : ℝ) := by
    rw [show (2233691147403795361/2233750000000000000 : ℝ)+2*(142227270481/714800000000000 : ℝ)*(1661/25000 : ℝ)=(1000000092793671/1000000000000000 : ℝ) by norm_num, show 1+2*(12974352211029/50000000000000000000 : ℝ)=(25000012974352211029/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3983973181552387/25000000000000000000 : ℝ)+(12974352211029/50000000000000000000 : ℝ) ≤ ((2233691147403795361/2233750000000000000 : ℝ)+(142227270481/714800000000000 : ℝ)*((1047/5000 : ℝ)+(1661/25000 : ℝ)))^(5727/1024 : ℝ) := by
    rw [show (2233691147403795361/2233750000000000000 : ℝ)+(142227270481/714800000000000 : ℝ)*((1047/5000 : ℝ)+(1661/25000 : ℝ))=(1250035672809709/1250000000000000 : ℝ) by norm_num, show 1+(3983973181552387/25000000000000000000 : ℝ)+(12974352211029/50000000000000000000 : ℝ)=(50007980920715315803/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3983973181552387/25000000000000000000 : ℝ) ≤ ((2233691147403795361/2233750000000000000 : ℝ)+2*(142227270481/714800000000000 : ℝ)*(1047/5000 : ℝ))^(5727/1024 : ℝ) := by
    rw [show (2233691147403795361/2233750000000000000 : ℝ)+2*(142227270481/714800000000000 : ℝ)*(1047/5000 : ℝ)=(5000284918509317/5000000000000000 : ℝ) by norm_num, show 1+2*(3983973181552387/25000000000000000000 : ℝ)=(12503983973181552387/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2233691147403795361/2233750000000000000 : ℝ)*(X 1 0+X 2 0)+(142227270481/714800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (1661/25000 : ℝ)) (hi := (1047/5000 : ℝ)) (c := (2233691147403795361/2233750000000000000 : ℝ)) (alpha := (142227270481/714800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2233691147403795361/2233750000000000000 : ℝ)*(X 0 1+X 2 1)+(142227270481/714800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (1661/25000 : ℝ)) (hi := (1047/5000 : ℝ)) (c := (2233691147403795361/2233750000000000000 : ℝ)) (alpha := (142227270481/714800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2233691147403795361/2233750000000000000 : ℝ)*(X 0 2+X 1 2)+(142227270481/714800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (1661/25000 : ℝ)) (hi := (1047/5000 : ℝ)) (c := (2233691147403795361/2233750000000000000 : ℝ)) (alpha := (142227270481/714800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1232261349/10000000000 : ℝ)*X 0 0+(5503373921/10000000000 : ℝ)*X 0 1+(1015531173/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1067738953/2000000000 : ℝ)*X 1 0+(-363798061/2500000000 : ℝ)*X 1 1+(5077655753/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2669347171/5000000000 : ℝ)*X 2 0+(634707003/1250000000 : ℝ)*X 2 1+(-1455192451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((804826449/2000000000 : ℝ)*X 0 0+(84082403/250000000 : ℝ)*X 0 1+(2375306537/5000000000 : ℝ)*X 0 2+(804826449/2000000000 : ℝ)*X 1 0+(84082403/250000000 : ℝ)*X 1 1+(2375306537/5000000000 : ℝ)*X 1 2+(804826449/2000000000 : ℝ)*X 2 0+(84082403/250000000 : ℝ)*X 2 1+(2375306537/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1232633199/10000000000 : ℝ)*X 0 0+(5084665009/10000000000 : ℝ)*X 0 1+(43969723/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((40826263/78125000 : ℝ)*X 1 0+(-1036632763/10000000000 : ℝ)*X 1 1+(2748107687/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5225761531/10000000000 : ℝ)*X 2 0+(2748107787/5000000000 : ℝ)*X 2 1+(-1036632667/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((503168013/1250000000 : ℝ)*X 0 0+(94555467/200000000 : ℝ)*X 0 1+(3386622831/10000000000 : ℝ)*X 0 2+(503168013/1250000000 : ℝ)*X 1 0+(94555467/200000000 : ℝ)*X 1 1+(3386622831/10000000000 : ℝ)*X 1 2+(503168013/1250000000 : ℝ)*X 2 0+(94555467/200000000 : ℝ)*X 2 1+(3386622831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (551825574633121083234128457/111687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (184974979/25000000000000 : ℝ)*(base19) + (255078419/50000000000000 : ℝ)*(base23) + (36797721/100000000000000 : ℝ)*(lower2) + (32870871/20000000000000 : ℝ)*(upper3) + (6753439/50000000000000 : ℝ)*(lower4) + (1534901132154957/100000000000000 : ℝ)*(major0) + (1534901132154957/100000000000000 : ℝ)*(major1) + (1534901132154957/100000000000000 : ℝ)*(major2) + (587244798230261/25000000000000 : ℝ)*(sp0) + (293622824896959/12500000000000 : ℝ)*(sp1) + (375837252627/16000000000 : ℝ)*(sp2) + (72081696090673/10000000000000 : ℝ)*(sp3) + (4146154543/100000000000000 : ℝ)*(sp4) + (1799634259/100000000000000 : ℝ)*(sp7) + (720818760540989/100000000000000 : ℝ)*(f.failure) + (587245834768897/25000000000000 : ℝ)*(f.sum) + (127559057753297/35740000000000000000000000000 : ℝ)*base65 + (883929458591185051/111687500000000000000000000000000 : ℝ)*base67 + (1062013806600497551/111687500000000000000000000000000 : ℝ)*base69 + (525003784445247551/111687500000000000000000000000000 : ℝ)*base71 + (62725593065637/35740000000000000000000000000 : ℝ)*base73 + (830014372569435051/111687500000000000000000000000000 : ℝ)*base75 + (393105825973997551/111687500000000000000000000000000 : ℝ)*base77 + (405474662182247551/111687500000000000000000000000000 : ℝ)*base79 + (45956323700057/35740000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (59059113/5000000000000000000000 : ℝ)*base90 + (59059113/5000000000000000000000 : ℝ)*base92 + (59059113/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (740998116307289030017032891/55843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (852572421/50000000000000 : ℝ)*(base19) + (944725997/50000000000000 : ℝ)*(base23) + (325996939/100000000000000 : ℝ)*(upper3) + (45913019/50000000000000 : ℝ)*(lower4) + (193329309/100000000000000 : ℝ)*(upper5) + (793865585425923/50000000000000 : ℝ)*(major0) + (793865585425923/50000000000000 : ℝ)*(major1) + (793865585425923/50000000000000 : ℝ)*(major2) + (5276674673/50000000000000 : ℝ)*(sp1) + (1381241541/10000000000000 : ℝ)*(sp2) + (1214916574014433/50000000000000 : ℝ)*(sp4) + (1214910444767339/50000000000000 : ℝ)*(sp5) + (2429817446161461/100000000000000 : ℝ)*(sp6) + (149125750274081/20000000000000 : ℝ)*(sp7) + (149125750274081/20000000000000 : ℝ)*(f.failure) + (1214916574014433/50000000000000 : ℝ)*(f.sum) + (68359393503143/17870000000000000000000000000 : ℝ)*base65 + (2616667077651289/55843750000000000000000000000000 : ℝ)*base67 + (456478976606942461/55843750000000000000000000000000 : ℝ)*base70 + (72960612094963789/55843750000000000000000000000000 : ℝ)*base71 + (83876643134523/17870000000000000000000000000 : ℝ)*base73 + (390159629335692461/55843750000000000000000000000000 : ℝ)*base76 + (104690521047370039/55843750000000000000000000000000 : ℝ)*base77 + (71216600502026289/55843750000000000000000000000000 : ℝ)*base79 + (59030124744497/17870000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2446077/1000000000000000000000 : ℝ)*base90 + (2446077/1000000000000000000000 : ℝ)*base92 + (2446077/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1748_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1047/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1661/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8951/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4523/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1748_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1748_s2_0 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-246675801/2000000000 : ℝ)*x 0 + (5499789569/10000000000 : ℝ)*x 1 + (5080480893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (246675801/2000000000 : ℝ)^5743 ≤ (1957983112409/25000000000000 : ℝ)^4719 := by
    have hnat : (246675801 : ℕ)^5743*25000000000000^4719 ≤ 1957983112409^4719*2000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      246675801 2000000000 1957983112409 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5499789569/10000000000 : ℝ)^5743 ≤ (48306151197203/100000000000000 : ℝ)^4719 := by
    have hnat : (5499789569 : ℕ)^5743*100000000000000^4719 ≤ 48306151197203^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499789569 10000000000 48306151197203 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5080480893/10000000000 : ℝ)^5743 ≤ (43861916342273/100000000000000 : ℝ)^4719 := by
    have hnat : (5080480893 : ℕ)^5743*100000000000000^4719 ≤ 43861916342273^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080480893 10000000000 43861916342273 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-246675801/2000000000 : ℝ), (5499789569/10000000000 : ℝ), (5080480893/10000000000 : ℝ)] ![(1957983112409/25000000000000 : ℝ), (48306151197203/100000000000000 : ℝ), (43861916342273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-246675801/2000000000 : ℝ)|^5743 ≤ (1957983112409/25000000000000 : ℝ)^4719
        have hw : |(-246675801/2000000000 : ℝ)|=(246675801/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5499789569/10000000000 : ℝ)|^5743 ≤ (48306151197203/100000000000000 : ℝ)^4719
        have hw : |(5499789569/10000000000 : ℝ)|=(5499789569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5080480893/10000000000 : ℝ)|^5743 ≤ (43861916342273/100000000000000 : ℝ)^4719
        have hw : |(5080480893/10000000000 : ℝ)|=(5080480893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s2_1 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1334425299/2500000000 : ℝ)*x 0 + (-1452803487/10000000000 : ℝ)*x 1 + (5080481049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1334425299/2500000000 : ℝ)^5743 ≤ (9315827903041/20000000000000 : ℝ)^4719 := by
    have hnat : (1334425299 : ℕ)^5743*20000000000000^4719 ≤ 9315827903041^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1334425299 2500000000 9315827903041 20000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1452803487/10000000000 : ℝ)^5743 ≤ (4779471241887/50000000000000 : ℝ)^4719 := by
    have hnat : (1452803487 : ℕ)^5743*50000000000000^4719 ≤ 4779471241887^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1452803487 10000000000 4779471241887 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5080481049/10000000000 : ℝ)^5743 ≤ (21930958990669/50000000000000 : ℝ)^4719 := by
    have hnat : (5080481049 : ℕ)^5743*50000000000000^4719 ≤ 21930958990669^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080481049 10000000000 21930958990669 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1334425299/2500000000 : ℝ), (-1452803487/10000000000 : ℝ), (5080481049/10000000000 : ℝ)] ![(9315827903041/20000000000000 : ℝ), (4779471241887/50000000000000 : ℝ), (21930958990669/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1334425299/2500000000 : ℝ)|^5743 ≤ (9315827903041/20000000000000 : ℝ)^4719
        have hw : |(1334425299/2500000000 : ℝ)|=(1334425299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1452803487/10000000000 : ℝ)|^5743 ≤ (4779471241887/50000000000000 : ℝ)^4719
        have hw : |(-1452803487/10000000000 : ℝ)|=(1452803487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5080481049/10000000000 : ℝ)|^5743 ≤ (21930958990669/50000000000000 : ℝ)^4719
        have hw : |(5080481049/10000000000 : ℝ)|=(5080481049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s2_2 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5337701179/10000000000 : ℝ)*x 0 + (5080480943/10000000000 : ℝ)*x 1 + (-1452803649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5337701179/10000000000 : ℝ)^5743 ≤ (5822392416833/12500000000000 : ℝ)^4719 := by
    have hnat : (5337701179 : ℕ)^5743*12500000000000^4719 ≤ 5822392416833^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5337701179 10000000000 5822392416833 12500000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5080480943/10000000000 : ℝ)^5743 ≤ (21930958433807/50000000000000 : ℝ)^4719 := by
    have hnat : (5080480943 : ℕ)^5743*50000000000000^4719 ≤ 21930958433807^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5080480943 10000000000 21930958433807 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1452803649/10000000000 : ℝ)^5743 ≤ (4779471890487/50000000000000 : ℝ)^4719 := by
    have hnat : (1452803649 : ℕ)^5743*50000000000000^4719 ≤ 4779471890487^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1452803649 10000000000 4779471890487 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5337701179/10000000000 : ℝ), (5080480943/10000000000 : ℝ), (-1452803649/10000000000 : ℝ)] ![(5822392416833/12500000000000 : ℝ), (21930958433807/50000000000000 : ℝ), (4779471890487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5337701179/10000000000 : ℝ)|^5743 ≤ (5822392416833/12500000000000 : ℝ)^4719
        have hw : |(5337701179/10000000000 : ℝ)|=(5337701179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5080480943/10000000000 : ℝ)|^5743 ≤ (21930958433807/50000000000000 : ℝ)^4719
        have hw : |(5080480943/10000000000 : ℝ)|=(5080480943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1452803649/10000000000 : ℝ)|^5743 ≤ (4779471890487/50000000000000 : ℝ)^4719
        have hw : |(-1452803649/10000000000 : ℝ)|=(1452803649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s2_3 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (503130863/1250000000 : ℝ)*x 0 + (3373669301/10000000000 : ℝ)*x 1 + (4740100773/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503130863/1250000000 : ℝ)^5743 ≤ (264300603063/800000000000 : ℝ)^4719 := by
    have hnat : (503130863 : ℕ)^5743*800000000000^4719 ≤ 264300603063^4719*1250000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503130863 1250000000 264300603063 800000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3373669301/10000000000 : ℝ)^5743 ≤ (26650358391603/100000000000000 : ℝ)^4719 := by
    have hnat : (3373669301 : ℕ)^5743*100000000000000^4719 ≤ 26650358391603^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3373669301 10000000000 26650358391603 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4740100773/10000000000 : ℝ)^5743 ≤ (40312066208377/100000000000000 : ℝ)^4719 := by
    have hnat : (4740100773 : ℕ)^5743*100000000000000^4719 ≤ 40312066208377^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4740100773 10000000000 40312066208377 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(503130863/1250000000 : ℝ), (3373669301/10000000000 : ℝ), (4740100773/10000000000 : ℝ)] ![(264300603063/800000000000 : ℝ), (26650358391603/100000000000000 : ℝ), (40312066208377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(503130863/1250000000 : ℝ)|^5743 ≤ (264300603063/800000000000 : ℝ)^4719
        have hw : |(503130863/1250000000 : ℝ)|=(503130863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3373669301/10000000000 : ℝ)|^5743 ≤ (26650358391603/100000000000000 : ℝ)^4719
        have hw : |(3373669301/10000000000 : ℝ)|=(3373669301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4740100773/10000000000 : ℝ)|^5743 ≤ (40312066208377/100000000000000 : ℝ)^4719
        have hw : |(4740100773/10000000000 : ℝ)|=(4740100773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s2_4 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1233734397/10000000000 : ℝ)*x 0 + (63591003/125000000 : ℝ)*x 1 + (5492847363/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1233734397/10000000000 : ℝ)^5743 ≤ (7834678967601/100000000000000 : ℝ)^4719 := by
    have hnat : (1233734397 : ℕ)^5743*100000000000000^4719 ≤ 7834678967601^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1233734397 10000000000 7834678967601 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (63591003/125000000 : ℝ)^5743 ≤ (43933366280837/100000000000000 : ℝ)^4719 := by
    have hnat : (63591003 : ℕ)^5743*100000000000000^4719 ≤ 43933366280837^4719*125000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63591003 125000000 43933366280837 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5492847363/10000000000 : ℝ)^5743 ≤ (24115977367557/50000000000000 : ℝ)^4719 := by
    have hnat : (5492847363 : ℕ)^5743*50000000000000^4719 ≤ 24115977367557^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492847363 10000000000 24115977367557 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1233734397/10000000000 : ℝ), (63591003/125000000 : ℝ), (5492847363/10000000000 : ℝ)] ![(7834678967601/100000000000000 : ℝ), (43933366280837/100000000000000 : ℝ), (24115977367557/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1233734397/10000000000 : ℝ)|^5743 ≤ (7834678967601/100000000000000 : ℝ)^4719
        have hw : |(-1233734397/10000000000 : ℝ)|=(1233734397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(63591003/125000000 : ℝ)|^5743 ≤ (43933366280837/100000000000000 : ℝ)^4719
        have hw : |(63591003/125000000 : ℝ)|=(63591003/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5492847363/10000000000 : ℝ)|^5743 ≤ (24115977367557/50000000000000 : ℝ)^4719
        have hw : |(5492847363/10000000000 : ℝ)|=(5492847363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s2_5 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226487503/10000000000 : ℝ)*x 0 + (-1040437131/10000000000 : ℝ)*x 1 + (2746423573/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226487503/10000000000 : ℝ)^5743 ≤ (11350182646429/25000000000000 : ℝ)^4719 := by
    have hnat : (5226487503 : ℕ)^5743*25000000000000^4719 ≤ 11350182646429^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226487503 10000000000 11350182646429 25000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1040437131/10000000000 : ℝ)^5743 ≤ (318365849113/5000000000000 : ℝ)^4719 := by
    have hnat : (1040437131 : ℕ)^5743*5000000000000^4719 ≤ 318365849113^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040437131 10000000000 318365849113 5000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2746423573/5000000000 : ℝ)^5743 ≤ (48231952416193/100000000000000 : ℝ)^4719 := by
    have hnat : (2746423573 : ℕ)^5743*100000000000000^4719 ≤ 48231952416193^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746423573 5000000000 48231952416193 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226487503/10000000000 : ℝ), (-1040437131/10000000000 : ℝ), (2746423573/5000000000 : ℝ)] ![(11350182646429/25000000000000 : ℝ), (318365849113/5000000000000 : ℝ), (48231952416193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226487503/10000000000 : ℝ)|^5743 ≤ (11350182646429/25000000000000 : ℝ)^4719
        have hw : |(5226487503/10000000000 : ℝ)|=(5226487503/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1040437131/10000000000 : ℝ)|^5743 ≤ (318365849113/5000000000000 : ℝ)^4719
        have hw : |(-1040437131/10000000000 : ℝ)|=(1040437131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2746423573/5000000000 : ℝ)|^5743 ≤ (48231952416193/100000000000000 : ℝ)^4719
        have hw : |(2746423573/5000000000 : ℝ)|=(2746423573/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s2_6 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5226487421/10000000000 : ℝ)*x 0 + (2746423599/5000000000 : ℝ)*x 1 + (-260109293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5226487421/10000000000 : ℝ)^5743 ≤ (45400729718843/100000000000000 : ℝ)^4719 := by
    have hnat : (5226487421 : ℕ)^5743*100000000000000^4719 ≤ 45400729718843^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5226487421 10000000000 45400729718843 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2746423599/5000000000 : ℝ)^5743 ≤ (48231952971879/100000000000000 : ℝ)^4719 := by
    have hnat : (2746423599 : ℕ)^5743*100000000000000^4719 ≤ 48231952971879^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2746423599 5000000000 48231952971879 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (260109293/2500000000 : ℝ)^5743 ≤ (6367317287621/100000000000000 : ℝ)^4719 := by
    have hnat : (260109293 : ℕ)^5743*100000000000000^4719 ≤ 6367317287621^4719*2500000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      260109293 2500000000 6367317287621 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5226487421/10000000000 : ℝ), (2746423599/5000000000 : ℝ), (-260109293/2500000000 : ℝ)] ![(45400729718843/100000000000000 : ℝ), (48231952971879/100000000000000 : ℝ), (6367317287621/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5226487421/10000000000 : ℝ)|^5743 ≤ (45400729718843/100000000000000 : ℝ)^4719
        have hw : |(5226487421/10000000000 : ℝ)|=(5226487421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2746423599/5000000000 : ℝ)|^5743 ≤ (48231952971879/100000000000000 : ℝ)^4719
        have hw : |(2746423599/5000000000 : ℝ)|=(2746423599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-260109293/2500000000 : ℝ)|^5743 ≤ (6367317287621/100000000000000 : ℝ)^4719
        have hw : |(-260109293/2500000000 : ℝ)|=(260109293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1748_s2_7 (p : ℝ) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4026204299/10000000000 : ℝ)*x 0 + (2358971419/5000000000 : ℝ)*x 1 + (424536619/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4026204299/10000000000 : ℝ)^5743 ≤ (1652456853497/5000000000000 : ℝ)^4719 := by
    have hnat : (4026204299 : ℕ)^5743*5000000000000^4719 ≤ 1652456853497^4719*10000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4026204299 10000000000 1652456853497 5000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2358971419/5000000000 : ℝ)^5743 ≤ (40082850162551/100000000000000 : ℝ)^4719 := by
    have hnat : (2358971419 : ℕ)^5743*100000000000000^4719 ≤ 40082850162551^4719*5000000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2358971419 5000000000 40082850162551 100000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424536619/1250000000 : ℝ)^5743 ≤ (13434006381419/50000000000000 : ℝ)^4719 := by
    have hnat : (424536619 : ℕ)^5743*50000000000000^4719 ≤ 13434006381419^4719*1250000000^5743 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424536619 1250000000 13434006381419 50000000000000 5743 4719 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5743/1024 : ℝ)) 5743 4719 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4026204299/10000000000 : ℝ), (2358971419/5000000000 : ℝ), (424536619/1250000000 : ℝ)] ![(1652456853497/5000000000000 : ℝ), (40082850162551/100000000000000 : ℝ), (13434006381419/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4026204299/10000000000 : ℝ)|^5743 ≤ (1652456853497/5000000000000 : ℝ)^4719
        have hw : |(4026204299/10000000000 : ℝ)|=(4026204299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2358971419/5000000000 : ℝ)|^5743 ≤ (40082850162551/100000000000000 : ℝ)^4719
        have hw : |(2358971419/5000000000 : ℝ)|=(2358971419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424536619/1250000000 : ℝ)|^5743 ≤ (13434006381419/50000000000000 : ℝ)^4719
        have hw : |(424536619/1250000000 : ℝ)|=(424536619/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1748_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8951/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9013/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (563/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8951/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4523/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8951/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8951/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4523/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8951/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8951/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4523/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8951/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8951/100000 : ℝ) ^ (5727/1024 : ℝ) ≤ (27484325372473/20000000000000000000 : ℝ) := by
    have hpowers : (8951/100000 : ℝ)^5727 ≤ (27484325372473/20000000000000000000 : ℝ)^1024 := by
      have hnat : (8951 : ℕ)^5727*20000000000000000000^1024 ≤ 27484325372473^1024*100000^5727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8951 100000 27484325372473 20000000000000000000 5727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8951/100000 : ℝ)) (X := (27484325372473/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4523/25000 : ℝ) ^ (5727/1024 : ℝ) ≤ (7035430261378937/100000000000000000000 : ℝ) := by
    have hpowers : (4523/25000 : ℝ)^5727 ≤ (7035430261378937/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4523 : ℕ)^5727*100000000000000000000^1024 ≤ 7035430261378937^1024*25000^5727 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4523 25000 7035430261378937 100000000000000000000 5727 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4523/25000 : ℝ)) (X := (7035430261378937/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000027484325372473/10000000000000000000 : ℝ) ≤ (500000245712567/500000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (10000027484325372473/10000000000000000000 : ℝ)^1024 ≤ (500000245712567/500000000000000 : ℝ)^5727 := by
      have hnat : (10000027484325372473 : ℕ)^1024*500000000000000^5727 ≤ 500000245712567^5727*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000027484325372473 10000000000000000000 500000245712567 500000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500000245712567/500000000000000 : ℝ)) (X := (10000027484325372473/10000000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50003586425944120651/50000000000000000000 : ℝ) ≤ (5000064124183871/5000000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (50003586425944120651/50000000000000000000 : ℝ)^1024 ≤ (5000064124183871/5000000000000000 : ℝ)^5727 := by
      have hnat : (50003586425944120651 : ℕ)^1024*5000000000000000^5727 ≤ 5000064124183871^5727*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50003586425944120651 50000000000000000000 5000064124183871 5000000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000064124183871/5000000000000000 : ℝ)) (X := (50003586425944120651/50000000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50007035430261378937/50000000000000000000 : ℝ) ≤ (625015723905259/625000000000000 : ℝ) ^ (5727/1024 : ℝ) := by
    have hpowers : (50007035430261378937/50000000000000000000 : ℝ)^1024 ≤ (625015723905259/625000000000000 : ℝ)^5727 := by
      have hnat : (50007035430261378937 : ℕ)^1024*625000000000000^5727 ≤ 625015723905259^5727*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50007035430261378937 50000000000000000000 625015723905259 625000000000000 1024 5727 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625015723905259/625000000000000 : ℝ)) (X := (50007035430261378937/50000000000000000000 : ℝ)) (by norm_num) 5727 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(27484325372473/20000000000000000000 : ℝ) ≤ ((476082484342810783/476093750000000000 : ℝ)+2*(20555686067/152350000000000 : ℝ)*(8951/100000 : ℝ))^(5727/1024 : ℝ) := by
    rw [show (476082484342810783/476093750000000000 : ℝ)+2*(20555686067/152350000000000 : ℝ)*(8951/100000 : ℝ)=(500000245712567/500000000000000 : ℝ) by norm_num, show 1+2*(27484325372473/20000000000000000000 : ℝ)=(10000027484325372473/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7035430261378937/100000000000000000000 : ℝ)+(27484325372473/20000000000000000000 : ℝ) ≤ ((476082484342810783/476093750000000000 : ℝ)+(20555686067/152350000000000 : ℝ)*((4523/25000 : ℝ)+(8951/100000 : ℝ)))^(5727/1024 : ℝ) := by
    rw [show (476082484342810783/476093750000000000 : ℝ)+(20555686067/152350000000000 : ℝ)*((4523/25000 : ℝ)+(8951/100000 : ℝ))=(5000064124183871/5000000000000000 : ℝ) by norm_num, show 1+(7035430261378937/100000000000000000000 : ℝ)+(27484325372473/20000000000000000000 : ℝ)=(50003586425944120651/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7035430261378937/100000000000000000000 : ℝ) ≤ ((476082484342810783/476093750000000000 : ℝ)+2*(20555686067/152350000000000 : ℝ)*(4523/25000 : ℝ))^(5727/1024 : ℝ) := by
    rw [show (476082484342810783/476093750000000000 : ℝ)+2*(20555686067/152350000000000 : ℝ)*(4523/25000 : ℝ)=(625015723905259/625000000000000 : ℝ) by norm_num, show 1+2*(7035430261378937/100000000000000000000 : ℝ)=(50007035430261378937/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (476082484342810783/476093750000000000 : ℝ)*(X 1 0+X 2 0)+(20555686067/152350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (8951/100000 : ℝ)) (hi := (4523/25000 : ℝ)) (c := (476082484342810783/476093750000000000 : ℝ)) (alpha := (20555686067/152350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (476082484342810783/476093750000000000 : ℝ)*(X 0 1+X 2 1)+(20555686067/152350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (8951/100000 : ℝ)) (hi := (4523/25000 : ℝ)) (c := (476082484342810783/476093750000000000 : ℝ)) (alpha := (20555686067/152350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (476082484342810783/476093750000000000 : ℝ)*(X 0 2+X 1 2)+(20555686067/152350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5727/1024 : ℝ)) (lo := (8951/100000 : ℝ)) (hi := (4523/25000 : ℝ)) (c := (476082484342810783/476093750000000000 : ℝ)) (alpha := (20555686067/152350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-246675801/2000000000 : ℝ)*X 0 0+(5499789569/10000000000 : ℝ)*X 0 1+(5080480893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1334425299/2500000000 : ℝ)*X 1 0+(-1452803487/10000000000 : ℝ)*X 1 1+(5080481049/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5337701179/10000000000 : ℝ)*X 2 0+(5080480943/10000000000 : ℝ)*X 2 1+(-1452803649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((503130863/1250000000 : ℝ)*X 0 0+(3373669301/10000000000 : ℝ)*X 0 1+(4740100773/10000000000 : ℝ)*X 0 2+(503130863/1250000000 : ℝ)*X 1 0+(3373669301/10000000000 : ℝ)*X 1 1+(4740100773/10000000000 : ℝ)*X 1 2+(503130863/1250000000 : ℝ)*X 2 0+(3373669301/10000000000 : ℝ)*X 2 1+(4740100773/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1233734397/10000000000 : ℝ)*X 0 0+(63591003/125000000 : ℝ)*X 0 1+(5492847363/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5226487503/10000000000 : ℝ)*X 1 0+(-1040437131/10000000000 : ℝ)*X 1 1+(2746423573/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5226487421/10000000000 : ℝ)*X 2 0+(2746423599/5000000000 : ℝ)*X 2 1+(-260109293/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4026204299/10000000000 : ℝ)*X 0 0+(2358971419/5000000000 : ℝ)*X 0 1+(424536619/1250000000 : ℝ)*X 0 2+(4026204299/10000000000 : ℝ)*X 1 0+(2358971419/5000000000 : ℝ)*X 1 1+(424536619/1250000000 : ℝ)*X 1 2+(4026204299/10000000000 : ℝ)*X 2 0+(2358971419/5000000000 : ℝ)*X 2 1+(424536619/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1748_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (558819548360230389995285211/47609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (724817933/50000000000000 : ℝ)*(base19) + (629967863/50000000000000 : ℝ)*(base23) + (48600969/50000000000000 : ℝ)*(lower2) + (83749489/25000000000000 : ℝ)*(upper3) + (120003343/100000000000000 : ℝ)*(upper5) + (1558370395285281/100000000000000 : ℝ)*(major0) + (1558370395285281/100000000000000 : ℝ)*(major1) + (1558370395285281/100000000000000 : ℝ)*(major2) + (23848899539649/1000000000000 : ℝ)*(sp0) + (476979715372933/20000000000000 : ℝ)*(sp1) + (596224691641201/25000000000000 : ℝ)*(sp2) + (146367240816831/20000000000000 : ℝ)*(sp3) + (1007253563/10000000000000 : ℝ)*(sp4) + (4168732707/100000000000000 : ℝ)*(sp7) + (365920186408431/50000000000000 : ℝ)*(f.failure) + (2384900026500531/100000000000000 : ℝ)*(f.sum) + (8196392902551/15235000000000000000000000000 : ℝ)*base66 + (197963065440772523/47609375000000000000000000000000 : ℝ)*base67 + (193300924630522523/47609375000000000000000000000000 : ℝ)*base69 + (357099999326647523/47609375000000000000000000000000 : ℝ)*base71 + (126083839241/952187500000000000000000000 : ℝ)*base74 + (40506292845222199/23804687500000000000000000000000 : ℝ)*base75 + (367094893653647523/47609375000000000000000000000000 : ℝ)*base77 + (298444990331647523/47609375000000000000000000000000 : ℝ)*base79 + (59155017809851/15235000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (31275027/2500000000000000000000 : ℝ)*base90 + (31275027/2500000000000000000000 : ℝ)*base92 + (31275027/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (673925054565674769023498199/47609375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (901565123/50000000000000 : ℝ)*(base19) + (1867184253/100000000000000 : ℝ)*(base23) + (259628217/100000000000000 : ℝ)*(upper3) + (3263981/6250000000000 : ℝ)*(lower4) + (287283397/100000000000000 : ℝ)*(upper5) + (805578279106819/50000000000000 : ℝ)*(major0) + (805578279106819/50000000000000 : ℝ)*(major1) + (805578279106819/50000000000000 : ℝ)*(major2) + (12114595053/100000000000000 : ℝ)*(sp1) + (6123501401/50000000000000 : ℝ)*(sp2) + (246568288583289/10000000000000 : ℝ)*(sp4) + (308208621013449/12500000000000 : ℝ)*(sp5) + (493133754329167/20000000000000 : ℝ)*(sp6) + (756629758751/100000000000 : ℝ)*(sp7) + (756629758751/100000000000 : ℝ)*(f.failure) + (246568288583289/10000000000000 : ℝ)*(f.sum) + (25544518264479/7617500000000000000000000000 : ℝ)*base66 + (59543449422308799/11902343750000000000000000000000 : ℝ)*base68 + (8570749474991777/23804687500000000000000000000000 : ℝ)*base69 + (21889569093377981/2975585937500000000000000000000 : ℝ)*base72 + (43175337156203/15235000000000000000000000000 : ℝ)*base74 + (217030637504282071/47609375000000000000000000000000 : ℝ)*base76 + (109569568254407071/47609375000000000000000000000000 : ℝ)*base78 + (14041255219284951/11902343750000000000000000000000 : ℝ)*base79 + (907119373111/7617500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (45533/5000000000000000000 : ℝ)*base89 + (45533/5000000000000000000 : ℝ)*base91 + (45533/5000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1748_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4523/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8951/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9013/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1748_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1748_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9013/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1748_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1748_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1748_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5727/1024 : ℝ) ≤ p) (hpb : p ≤ (5743/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (106469283/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9013/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (563/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1748_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
