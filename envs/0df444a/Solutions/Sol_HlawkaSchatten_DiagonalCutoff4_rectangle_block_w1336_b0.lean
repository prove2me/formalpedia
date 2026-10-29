-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1336_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:03:18.908968+00:00
-- url     : https://prove2.me/submissions/d8353350-a7ba-4d28-aef6-f8ffd7f8b8fa

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
theorem support_rectangle_w1336_s0_0 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-906349281/5000000000 : ℝ)*x 0 + (5999512183/10000000000 : ℝ)*x 1 + (300592217/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (906349281/5000000000 : ℝ)^537 ≤ (5311073746783/50000000000000 : ℝ)^409 := by
    have hnat : (906349281 : ℕ)^537*50000000000000^409 ≤ 5311073746783^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906349281 5000000000 5311073746783 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5999512183/10000000000 : ℝ)^537 ≤ (51129959795057/100000000000000 : ℝ)^409 := by
    have hnat : (5999512183 : ℕ)^537*100000000000000^409 ≤ 51129959795057^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5999512183 10000000000 51129959795057 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300592217/625000000 : ℝ)^537 ≤ (38247892696931/100000000000000 : ℝ)^409 := by
    have hnat : (300592217 : ℕ)^537*100000000000000^409 ≤ 38247892696931^409*625000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300592217 625000000 38247892696931 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-906349281/5000000000 : ℝ), (5999512183/10000000000 : ℝ), (300592217/625000000 : ℝ)] ![(5311073746783/50000000000000 : ℝ), (51129959795057/100000000000000 : ℝ), (38247892696931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-906349281/5000000000 : ℝ)|^537 ≤ (5311073746783/50000000000000 : ℝ)^409
        have hw : |(-906349281/5000000000 : ℝ)|=(906349281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5999512183/10000000000 : ℝ)|^537 ≤ (51129959795057/100000000000000 : ℝ)^409
        have hw : |(5999512183/10000000000 : ℝ)|=(5999512183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(300592217/625000000 : ℝ)|^537 ≤ (38247892696931/100000000000000 : ℝ)^409
        have hw : |(300592217/625000000 : ℝ)|=(300592217/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s0_1 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5502484697/10000000000 : ℝ)*x 0 + (-622351363/2500000000 : ℝ)*x 1 + (4809475847/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5502484697/10000000000 : ℝ)^537 ≤ (45641987217683/100000000000000 : ℝ)^409 := by
    have hnat : (5502484697 : ℕ)^537*100000000000000^409 ≤ 45641987217683^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502484697 10000000000 45641987217683 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (622351363/2500000000 : ℝ)^537 ≤ (1006882259617/6250000000000 : ℝ)^409 := by
    have hnat : (622351363 : ℕ)^537*6250000000000^409 ≤ 1006882259617^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622351363 2500000000 1006882259617 6250000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4809475847/10000000000 : ℝ)^537 ≤ (19123948306237/50000000000000 : ℝ)^409 := by
    have hnat : (4809475847 : ℕ)^537*50000000000000^409 ≤ 19123948306237^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4809475847 10000000000 19123948306237 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5502484697/10000000000 : ℝ), (-622351363/2500000000 : ℝ), (4809475847/10000000000 : ℝ)] ![(45641987217683/100000000000000 : ℝ), (1006882259617/6250000000000 : ℝ), (19123948306237/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5502484697/10000000000 : ℝ)|^537 ≤ (45641987217683/100000000000000 : ℝ)^409
        have hw : |(5502484697/10000000000 : ℝ)|=(5502484697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-622351363/2500000000 : ℝ)|^537 ≤ (1006882259617/6250000000000 : ℝ)^409
        have hw : |(-622351363/2500000000 : ℝ)|=(622351363/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4809475847/10000000000 : ℝ)|^537 ≤ (19123948306237/50000000000000 : ℝ)^409
        have hw : |(4809475847/10000000000 : ℝ)|=(4809475847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s0_2 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5502484289/10000000000 : ℝ)*x 0 + (2404737893/5000000000 : ℝ)*x 1 + (-2489406051/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5502484289/10000000000 : ℝ)^537 ≤ (11410495693567/25000000000000 : ℝ)^409 := by
    have hnat : (5502484289 : ℕ)^537*25000000000000^409 ≤ 11410495693567^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5502484289 10000000000 11410495693567 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2404737893/5000000000 : ℝ)^537 ≤ (19123947987773/50000000000000 : ℝ)^409 := by
    have hnat : (2404737893 : ℕ)^537*50000000000000^409 ≤ 19123947987773^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2404737893 5000000000 19123947987773 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2489406051/10000000000 : ℝ)^537 ≤ (16110121243439/100000000000000 : ℝ)^409 := by
    have hnat : (2489406051 : ℕ)^537*100000000000000^409 ≤ 16110121243439^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2489406051 10000000000 16110121243439 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5502484289/10000000000 : ℝ), (2404737893/5000000000 : ℝ), (-2489406051/10000000000 : ℝ)] ![(11410495693567/25000000000000 : ℝ), (19123947987773/50000000000000 : ℝ), (16110121243439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5502484289/10000000000 : ℝ)|^537 ≤ (11410495693567/25000000000000 : ℝ)^409
        have hw : |(5502484289/10000000000 : ℝ)|=(5502484289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2404737893/5000000000 : ℝ)|^537 ≤ (19123947987773/50000000000000 : ℝ)^409
        have hw : |(2404737893/5000000000 : ℝ)|=(2404737893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2489406051/10000000000 : ℝ)|^537 ≤ (16110121243439/100000000000000 : ℝ)^409
        have hw : |(-2489406051/10000000000 : ℝ)|=(2489406051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s0_3 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1044911567/2500000000 : ℝ)*x 0 + (3106868553/10000000000 : ℝ)*x 1 + (5593859679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1044911567/2500000000 : ℝ)^537 ≤ (31810606369831/100000000000000 : ℝ)^409 := by
    have hnat : (1044911567 : ℕ)^537*100000000000000^409 ≤ 31810606369831^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044911567 2500000000 31810606369831 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3106868553/10000000000 : ℝ)^537 ≤ (21549690741293/100000000000000 : ℝ)^409 := by
    have hnat : (3106868553 : ℕ)^537*100000000000000^409 ≤ 21549690741293^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3106868553 10000000000 21549690741293 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5593859679/10000000000 : ℝ)^537 ≤ (46639702879043/100000000000000 : ℝ)^409 := by
    have hnat : (5593859679 : ℕ)^537*100000000000000^409 ≤ 46639702879043^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5593859679 10000000000 46639702879043 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1044911567/2500000000 : ℝ), (3106868553/10000000000 : ℝ), (5593859679/10000000000 : ℝ)] ![(31810606369831/100000000000000 : ℝ), (21549690741293/100000000000000 : ℝ), (46639702879043/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1044911567/2500000000 : ℝ)|^537 ≤ (31810606369831/100000000000000 : ℝ)^409
        have hw : |(1044911567/2500000000 : ℝ)|=(1044911567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3106868553/10000000000 : ℝ)|^537 ≤ (21549690741293/100000000000000 : ℝ)^409
        have hw : |(3106868553/10000000000 : ℝ)|=(3106868553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5593859679/10000000000 : ℝ)|^537 ≤ (46639702879043/100000000000000 : ℝ)^409
        have hw : |(5593859679/10000000000 : ℝ)|=(5593859679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s0_4 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-227148337/1250000000 : ℝ)*x 0 + (2420057539/5000000000 : ℝ)*x 1 + (298388949/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (227148337/1250000000 : ℝ)^537 ≤ (2131338283397/20000000000000 : ℝ)^409 := by
    have hnat : (227148337 : ℕ)^537*20000000000000^409 ≤ 2131338283397^409*1250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227148337 1250000000 2131338283397 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2420057539/5000000000 : ℝ)^537 ≤ (38568133042589/100000000000000 : ℝ)^409 := by
    have hnat : (2420057539 : ℕ)^537*100000000000000^409 ≤ 38568133042589^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2420057539 5000000000 38568133042589 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (298388949/500000000 : ℝ)^537 ≤ (50775175519357/100000000000000 : ℝ)^409 := by
    have hnat : (298388949 : ℕ)^537*100000000000000^409 ≤ 50775175519357^409*500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298388949 500000000 50775175519357 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-227148337/1250000000 : ℝ), (2420057539/5000000000 : ℝ), (298388949/500000000 : ℝ)] ![(2131338283397/20000000000000 : ℝ), (38568133042589/100000000000000 : ℝ), (50775175519357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-227148337/1250000000 : ℝ)|^537 ≤ (2131338283397/20000000000000 : ℝ)^409
        have hw : |(-227148337/1250000000 : ℝ)|=(227148337/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2420057539/5000000000 : ℝ)|^537 ≤ (38568133042589/100000000000000 : ℝ)^409
        have hw : |(2420057539/5000000000 : ℝ)|=(2420057539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(298388949/500000000 : ℝ)|^537 ≤ (50775175519357/100000000000000 : ℝ)^409
        have hw : |(298388949/500000000 : ℝ)|=(298388949/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s0_5 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2589099759/5000000000 : ℝ)*x 0 + (-1331103233/10000000000 : ℝ)*x 1 + (5967778803/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2589099759/5000000000 : ℝ)^537 ≤ (21071653807091/50000000000000 : ℝ)^409 := by
    have hnat : (2589099759 : ℕ)^537*50000000000000^409 ≤ 21071653807091^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589099759 5000000000 21071653807091 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1331103233/10000000000 : ℝ)^537 ≤ (3540759414973/50000000000000 : ℝ)^409 := by
    have hnat : (1331103233 : ℕ)^537*50000000000000^409 ≤ 3540759414973^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1331103233 10000000000 3540759414973 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5967778803/10000000000 : ℝ)^537 ≤ (50775173542101/100000000000000 : ℝ)^409 := by
    have hnat : (5967778803 : ℕ)^537*100000000000000^409 ≤ 50775173542101^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5967778803 10000000000 50775173542101 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2589099759/5000000000 : ℝ), (-1331103233/10000000000 : ℝ), (5967778803/10000000000 : ℝ)] ![(21071653807091/50000000000000 : ℝ), (3540759414973/50000000000000 : ℝ), (50775173542101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2589099759/5000000000 : ℝ)|^537 ≤ (21071653807091/50000000000000 : ℝ)^409
        have hw : |(2589099759/5000000000 : ℝ)|=(2589099759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1331103233/10000000000 : ℝ)|^537 ≤ (3540759414973/50000000000000 : ℝ)^409
        have hw : |(-1331103233/10000000000 : ℝ)|=(1331103233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5967778803/10000000000 : ℝ)|^537 ≤ (50775173542101/100000000000000 : ℝ)^409
        have hw : |(5967778803/10000000000 : ℝ)|=(5967778803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s0_6 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5178199523/10000000000 : ℝ)*x 0 + (2983889483/5000000000 : ℝ)*x 1 + (-332775741/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5178199523/10000000000 : ℝ)^537 ≤ (4214330766761/10000000000000 : ℝ)^409 := by
    have hnat : (5178199523 : ℕ)^537*10000000000000^409 ≤ 4214330766761^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178199523 10000000000 4214330766761 10000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2983889483/5000000000 : ℝ)^537 ≤ (12693793840741/25000000000000 : ℝ)^409 := by
    have hnat : (2983889483 : ℕ)^537*25000000000000^409 ≤ 12693793840741^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2983889483 5000000000 12693793840741 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (332775741/2500000000 : ℝ)^537 ≤ (885189618873/12500000000000 : ℝ)^409 := by
    have hnat : (332775741 : ℕ)^537*12500000000000^409 ≤ 885189618873^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332775741 2500000000 885189618873 12500000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5178199523/10000000000 : ℝ), (2983889483/5000000000 : ℝ), (-332775741/2500000000 : ℝ)] ![(4214330766761/10000000000000 : ℝ), (12693793840741/25000000000000 : ℝ), (885189618873/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5178199523/10000000000 : ℝ)|^537 ≤ (4214330766761/10000000000000 : ℝ)^409
        have hw : |(5178199523/10000000000 : ℝ)|=(5178199523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2983889483/5000000000 : ℝ)|^537 ≤ (12693793840741/25000000000000 : ℝ)^409
        have hw : |(2983889483/5000000000 : ℝ)|=(2983889483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-332775741/2500000000 : ℝ)|^537 ≤ (885189618873/12500000000000 : ℝ)^409
        have hw : |(-332775741/2500000000 : ℝ)|=(332775741/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s0_7 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1047256073/2500000000 : ℝ)*x 0 + (552982849/1000000000 : ℝ)*x 1 + (1586592677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1047256073/2500000000 : ℝ)^537 ≤ (398804389421/1250000000000 : ℝ)^409 := by
    have hnat : (1047256073 : ℕ)^537*1250000000000^409 ≤ 398804389421^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047256073 2500000000 398804389421 1250000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552982849/1000000000 : ℝ)^537 ≤ (11485003043011/25000000000000 : ℝ)^409 := by
    have hnat : (552982849 : ℕ)^537*25000000000000^409 ≤ 11485003043011^409*1000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552982849 1000000000 11485003043011 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1586592677/5000000000 : ℝ)^537 ≤ (22155636663509/100000000000000 : ℝ)^409 := by
    have hnat : (1586592677 : ℕ)^537*100000000000000^409 ≤ 22155636663509^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1586592677 5000000000 22155636663509 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1047256073/2500000000 : ℝ), (552982849/1000000000 : ℝ), (1586592677/5000000000 : ℝ)] ![(398804389421/1250000000000 : ℝ), (11485003043011/25000000000000 : ℝ), (22155636663509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1047256073/2500000000 : ℝ)|^537 ≤ (398804389421/1250000000000 : ℝ)^409
        have hw : |(1047256073/2500000000 : ℝ)|=(1047256073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552982849/1000000000 : ℝ)|^537 ≤ (11485003043011/25000000000000 : ℝ)^409
        have hw : |(552982849/1000000000 : ℝ)|=(552982849/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1586592677/5000000000 : ℝ)|^537 ≤ (22155636663509/100000000000000 : ℝ)^409
        have hw : |(1586592677/5000000000 : ℝ)|=(1586592677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1336_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1369/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13457/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4295/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4295 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4295*1^1024 ≤ 0^1024*1^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4295/1024 : ℝ) ≤ (535606611559713783/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4295 ≤ (535606611559713783/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4295*25000000000000000000^1024 ≤ 535606611559713783^1024*5^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 535606611559713783 25000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (535606611559713783/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4295 := by
      have hnat : (1 : ℕ)^1024*1^4295 ≤ 1^4295*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25535606611559713783/25000000000000000000 : ℝ) ≤ (10050667491982549/10000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (25535606611559713783/25000000000000000000 : ℝ)^1024 ≤ (10050667491982549/10000000000000000 : ℝ)^4295 := by
      have hnat : (25535606611559713783 : ℕ)^1024*10000000000000000^4295 ≤ 10050667491982549^4295*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25535606611559713783 25000000000000000000 10050667491982549 10000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10050667491982549/10000000000000000 : ℝ)) (X := (25535606611559713783/25000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (13035606611559713783/12500000000000000000 : ℝ) ≤ (5050667491982549/5000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (13035606611559713783/12500000000000000000 : ℝ)^1024 ≤ (5050667491982549/5000000000000000 : ℝ)^4295 := by
      have hnat : (13035606611559713783 : ℕ)^1024*5000000000000000^4295 ≤ 5050667491982549^4295*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13035606611559713783 12500000000000000000 5050667491982549 5000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5050667491982549/5000000000000000 : ℝ)) (X := (13035606611559713783/12500000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(50667491982549/4000000000000000 : ℝ)*(0 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(50667491982549/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(535606611559713783/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(50667491982549/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4295/1024 : ℝ) := by
    rw [show (1 : ℝ)+(50667491982549/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10050667491982549/10000000000000000 : ℝ) by norm_num, show 1+(535606611559713783/25000000000000000000 : ℝ)+(0 : ℝ)=(25535606611559713783/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(535606611559713783/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(50667491982549/4000000000000000 : ℝ)*(2/5 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(50667491982549/4000000000000000 : ℝ)*(2/5 : ℝ)=(5050667491982549/5000000000000000 : ℝ) by norm_num, show 1+2*(535606611559713783/25000000000000000000 : ℝ)=(13035606611559713783/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(50667491982549/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50667491982549/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(50667491982549/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50667491982549/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(50667491982549/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (50667491982549/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-906349281/5000000000 : ℝ)*X 0 0+(5999512183/10000000000 : ℝ)*X 0 1+(300592217/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5502484697/10000000000 : ℝ)*X 1 0+(-622351363/2500000000 : ℝ)*X 1 1+(4809475847/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5502484289/10000000000 : ℝ)*X 2 0+(2404737893/5000000000 : ℝ)*X 2 1+(-2489406051/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1044911567/2500000000 : ℝ)*X 0 0+(3106868553/10000000000 : ℝ)*X 0 1+(5593859679/10000000000 : ℝ)*X 0 2+(1044911567/2500000000 : ℝ)*X 1 0+(3106868553/10000000000 : ℝ)*X 1 1+(5593859679/10000000000 : ℝ)*X 1 2+(1044911567/2500000000 : ℝ)*X 2 0+(3106868553/10000000000 : ℝ)*X 2 1+(5593859679/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-227148337/1250000000 : ℝ)*X 0 0+(2420057539/5000000000 : ℝ)*X 0 1+(298388949/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2589099759/5000000000 : ℝ)*X 1 0+(-1331103233/10000000000 : ℝ)*X 1 1+(5967778803/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5178199523/10000000000 : ℝ)*X 2 0+(2983889483/5000000000 : ℝ)*X 2 1+(-332775741/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1047256073/2500000000 : ℝ)*X 0 0+(552982849/1000000000 : ℝ)*X 0 1+(1586592677/5000000000 : ℝ)*X 0 2+(1047256073/2500000000 : ℝ)*X 1 0+(552982849/1000000000 : ℝ)*X 1 1+(1586592677/5000000000 : ℝ)*X 1 2+(1047256073/2500000000 : ℝ)*X 2 0+(552982849/1000000000 : ℝ)*X 2 1+(1586592677/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (543107816654262784110093/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11762421/12500000000000 : ℝ)*(base1) + (329529359/25000000000000 : ℝ)*(base19) + (251161861/20000000000000 : ℝ)*(base23) + (111777759/50000000000000 : ℝ)*(upper3) + (25683457/50000000000000 : ℝ)*(upper5) + (621207626318419/100000000000000 : ℝ)*(major0) + (621207626318419/100000000000000 : ℝ)*(major1) + (621207626318419/100000000000000 : ℝ)*(major2) + (168062999818473/20000000000000 : ℝ)*(sp0) + (840317444859341/100000000000000 : ℝ)*(sp1) + (52519844197967/6250000000000 : ℝ)*(sp2) + (50261748596123/12500000000000 : ℝ)*(sp3) + (192899189/5000000000000 : ℝ)*(sp4) + (2225755767/100000000000000 : ℝ)*(sp7) + (402096308624119/100000000000000 : ℝ)*(f.failure) + (840318762976777/100000000000000 : ℝ)*(f.sum) + (44426467929969/200000000000000000000000000000 : ℝ)*base66 + (1299056418470031/400000000000000000000000000000 : ℝ)*base67 + (2435651068329969/400000000000000000000000000000 : ℝ)*base70 + (842891075929969/400000000000000000000000000000 : ℝ)*base72 + (619601295270031/200000000000000000000000000000 : ℝ)*base73 + (698419527129969/400000000000000000000000000000 : ℝ)*base76 + (1396371831670031/400000000000000000000000000000 : ℝ)*base77 + (1106389724329969/400000000000000000000000000000 : ℝ)*base80 + (1050483651129969/200000000000000000000000000000 : ℝ)*base82 + (3916189/1250000000000000000000 : ℝ)*base89 + (3916189/1250000000000000000000 : ℝ)*base91 + (3916189/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (275783077772372506353093/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119039849/25000000000000 : ℝ)*(base19) + (293705753/50000000000000 : ℝ)*(base23) + (27787921/25000000000000 : ℝ)*(base39) + (12267121/25000000000000 : ℝ)*(upper3) + (98556349/100000000000000 : ℝ)*(upper5) + (655560437955369/100000000000000 : ℝ)*(major0) + (655560437955369/100000000000000 : ℝ)*(major1) + (327780163401843/50000000000000 : ℝ)*(major2) + (219689263/20000000000000 : ℝ)*(sp1) + (112979527/10000000000000 : ℝ)*(sp2) + (443394209492801/50000000000000 : ℝ)*(sp4) + (886786844379891/100000000000000 : ℝ)*(sp5) + (221696703232627/25000000000000 : ℝ)*(sp6) + (53041531730719/12500000000000 : ℝ)*(sp7) + (53041531730719/12500000000000 : ℝ)*(f.failure) + (177357706027457/20000000000000 : ℝ)*(f.sum) + (124210322586239/80000000000000000000000000000 : ℝ)*base65 + (354680056762193/200000000000000000000000000000 : ℝ)*base68 + (2786056921655581/400000000000000000000000000000 : ℝ)*base69 + (101827895037807/200000000000000000000000000000 : ℝ)*base71 + (154976650186239/80000000000000000000000000000 : ℝ)*base73 + (438193594455581/400000000000000000000000000000 : ℝ)*base75 + (1862654469655581/400000000000000000000000000000 : ℝ)*base77 + (3114161217655581/400000000000000000000000000000 : ℝ)*base79 + (736459443655581/200000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (441711/156250000000000000000 : ℝ)*base90 + (441711/156250000000000000000 : ℝ)*base92 + (2004211/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1336_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1369/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13457/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1336_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1336_s1_0 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-399676619/2000000000 : ℝ)*x 0 + (1128965903/2000000000 : ℝ)*x 1 + (5045249821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (399676619/2000000000 : ℝ)^537 ≤ (3018285177099/25000000000000 : ℝ)^409 := by
    have hnat : (399676619 : ℕ)^537*25000000000000^409 ≤ 3018285177099^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      399676619 2000000000 3018285177099 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1128965903/2000000000 : ℝ)^537 ≤ (11799615913591/25000000000000 : ℝ)^409 := by
    have hnat : (1128965903 : ℕ)^537*25000000000000^409 ≤ 11799615913591^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1128965903 2000000000 11799615913591 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5045249821/10000000000 : ℝ)^537 ≤ (2036419781703/5000000000000 : ℝ)^409 := by
    have hnat : (5045249821 : ℕ)^537*5000000000000^409 ≤ 2036419781703^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5045249821 10000000000 2036419781703 5000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-399676619/2000000000 : ℝ), (1128965903/2000000000 : ℝ), (5045249821/10000000000 : ℝ)] ![(3018285177099/25000000000000 : ℝ), (11799615913591/25000000000000 : ℝ), (2036419781703/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-399676619/2000000000 : ℝ)|^537 ≤ (3018285177099/25000000000000 : ℝ)^409
        have hw : |(-399676619/2000000000 : ℝ)|=(399676619/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1128965903/2000000000 : ℝ)|^537 ≤ (11799615913591/25000000000000 : ℝ)^409
        have hw : |(1128965903/2000000000 : ℝ)|=(1128965903/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5045249821/10000000000 : ℝ)|^537 ≤ (2036419781703/5000000000000 : ℝ)^409
        have hw : |(5045249821/10000000000 : ℝ)|=(5045249821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s1_1 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (675792797/1250000000 : ℝ)*x 0 + (-115924879/500000000 : ℝ)*x 1 + (5045249651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (675792797/1250000000 : ℝ)^537 ≤ (8919560440497/20000000000000 : ℝ)^409 := by
    have hnat : (675792797 : ℕ)^537*20000000000000^409 ≤ 8919560440497^409*1250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675792797 1250000000 8919560440497 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (115924879/500000000 : ℝ)^537 ≤ (917112747083/6250000000000 : ℝ)^409 := by
    have hnat : (115924879 : ℕ)^537*6250000000000^409 ≤ 917112747083^409*500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      115924879 500000000 917112747083 6250000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5045249651/10000000000 : ℝ)^537 ≤ (40728393832227/100000000000000 : ℝ)^409 := by
    have hnat : (5045249651 : ℕ)^537*100000000000000^409 ≤ 40728393832227^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5045249651 10000000000 40728393832227 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(675792797/1250000000 : ℝ), (-115924879/500000000 : ℝ), (5045249651/10000000000 : ℝ)] ![(8919560440497/20000000000000 : ℝ), (917112747083/6250000000000 : ℝ), (40728393832227/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(675792797/1250000000 : ℝ)|^537 ≤ (8919560440497/20000000000000 : ℝ)^409
        have hw : |(675792797/1250000000 : ℝ)|=(675792797/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-115924879/500000000 : ℝ)|^537 ≤ (917112747083/6250000000000 : ℝ)^409
        have hw : |(-115924879/500000000 : ℝ)|=(115924879/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5045249651/10000000000 : ℝ)|^537 ≤ (40728393832227/100000000000000 : ℝ)^409
        have hw : |(5045249651/10000000000 : ℝ)|=(5045249651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s1_2 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5406342433/10000000000 : ℝ)*x 0 + (5045249419/10000000000 : ℝ)*x 1 + (-2318497801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5406342433/10000000000 : ℝ)^537 ≤ (44597802819841/100000000000000 : ℝ)^409 := by
    have hnat : (5406342433 : ℕ)^537*100000000000000^409 ≤ 44597802819841^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406342433 10000000000 44597802819841 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5045249419/10000000000 : ℝ)^537 ≤ (8145678274651/20000000000000 : ℝ)^409 := by
    have hnat : (5045249419 : ℕ)^537*20000000000000^409 ≤ 8145678274651^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5045249419 10000000000 8145678274651 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2318497801/10000000000 : ℝ)^537 ≤ (14673805789779/100000000000000 : ℝ)^409 := by
    have hnat : (2318497801 : ℕ)^537*100000000000000^409 ≤ 14673805789779^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2318497801 10000000000 14673805789779 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5406342433/10000000000 : ℝ), (5045249419/10000000000 : ℝ), (-2318497801/10000000000 : ℝ)] ![(44597802819841/100000000000000 : ℝ), (8145678274651/20000000000000 : ℝ), (14673805789779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5406342433/10000000000 : ℝ)|^537 ≤ (44597802819841/100000000000000 : ℝ)^409
        have hw : |(5406342433/10000000000 : ℝ)|=(5406342433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5045249419/10000000000 : ℝ)|^537 ≤ (8145678274651/20000000000000 : ℝ)^409
        have hw : |(5045249419/10000000000 : ℝ)|=(5045249419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2318497801/10000000000 : ℝ)|^537 ≤ (14673805789779/100000000000000 : ℝ)^409
        have hw : |(-2318497801/10000000000 : ℝ)|=(2318497801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s1_3 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4293377297/10000000000 : ℝ)*x 0 + (3709336673/10000000000 : ℝ)*x 1 + (4962365953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4293377297/10000000000 : ℝ)^537 ≤ (32951897075151/100000000000000 : ℝ)^409 := by
    have hnat : (4293377297 : ℕ)^537*100000000000000^409 ≤ 32951897075151^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4293377297 10000000000 32951897075151 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3709336673/10000000000 : ℝ)^537 ≤ (27195927996033/100000000000000 : ℝ)^409 := by
    have hnat : (3709336673 : ℕ)^537*100000000000000^409 ≤ 27195927996033^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3709336673 10000000000 27195927996033 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4962365953/10000000000 : ℝ)^537 ≤ (39852174920779/100000000000000 : ℝ)^409 := by
    have hnat : (4962365953 : ℕ)^537*100000000000000^409 ≤ 39852174920779^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4962365953 10000000000 39852174920779 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4293377297/10000000000 : ℝ), (3709336673/10000000000 : ℝ), (4962365953/10000000000 : ℝ)] ![(32951897075151/100000000000000 : ℝ), (27195927996033/100000000000000 : ℝ), (39852174920779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4293377297/10000000000 : ℝ)|^537 ≤ (32951897075151/100000000000000 : ℝ)^409
        have hw : |(4293377297/10000000000 : ℝ)|=(4293377297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3709336673/10000000000 : ℝ)|^537 ≤ (27195927996033/100000000000000 : ℝ)^409
        have hw : |(3709336673/10000000000 : ℝ)|=(3709336673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4962365953/10000000000 : ℝ)|^537 ≤ (39852174920779/100000000000000 : ℝ)^409
        have hw : |(4962365953/10000000000 : ℝ)|=(4962365953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s1_4 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-499732681/2500000000 : ℝ)*x 0 + (5052806857/10000000000 : ℝ)*x 1 + (1409283597/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499732681/2500000000 : ℝ)^537 ≤ (6038742392887/50000000000000 : ℝ)^409 := by
    have hnat : (499732681 : ℕ)^537*50000000000000^409 ≤ 6038742392887^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499732681 2500000000 6038742392887 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5052806857/10000000000 : ℝ)^537 ≤ (8161702311401/20000000000000 : ℝ)^409 := by
    have hnat : (5052806857 : ℕ)^537*20000000000000^409 ≤ 8161702311401^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5052806857 10000000000 8161702311401 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1409283597/2500000000 : ℝ)^537 ≤ (47114003645741/100000000000000 : ℝ)^409 := by
    have hnat : (1409283597 : ℕ)^537*100000000000000^409 ≤ 47114003645741^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1409283597 2500000000 47114003645741 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-499732681/2500000000 : ℝ), (5052806857/10000000000 : ℝ), (1409283597/2500000000 : ℝ)] ![(6038742392887/50000000000000 : ℝ), (8161702311401/20000000000000 : ℝ), (47114003645741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-499732681/2500000000 : ℝ)|^537 ≤ (6038742392887/50000000000000 : ℝ)^409
        have hw : |(-499732681/2500000000 : ℝ)|=(499732681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5052806857/10000000000 : ℝ)|^537 ≤ (8161702311401/20000000000000 : ℝ)^409
        have hw : |(5052806857/10000000000 : ℝ)|=(5052806857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1409283597/2500000000 : ℝ)|^537 ≤ (47114003645741/100000000000000 : ℝ)^409
        have hw : |(1409283597/2500000000 : ℝ)|=(1409283597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s1_5 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1312709573/2500000000 : ℝ)*x 0 + (-1726613209/10000000000 : ℝ)*x 1 + (5637133729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1312709573/2500000000 : ℝ)^537 ≤ (42921198245913/100000000000000 : ℝ)^409 := by
    have hnat : (1312709573 : ℕ)^537*100000000000000^409 ≤ 42921198245913^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1312709573 2500000000 42921198245913 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1726613209/10000000000 : ℝ)^537 ≤ (2491201329657/25000000000000 : ℝ)^409 := by
    have hnat : (1726613209 : ℕ)^537*25000000000000^409 ≤ 2491201329657^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726613209 10000000000 2491201329657 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5637133729/10000000000 : ℝ)^537 ≤ (47113996414247/100000000000000 : ℝ)^409 := by
    have hnat : (5637133729 : ℕ)^537*100000000000000^409 ≤ 47113996414247^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5637133729 10000000000 47113996414247 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1312709573/2500000000 : ℝ), (-1726613209/10000000000 : ℝ), (5637133729/10000000000 : ℝ)] ![(42921198245913/100000000000000 : ℝ), (2491201329657/25000000000000 : ℝ), (47113996414247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1312709573/2500000000 : ℝ)|^537 ≤ (42921198245913/100000000000000 : ℝ)^409
        have hw : |(1312709573/2500000000 : ℝ)|=(1312709573/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1726613209/10000000000 : ℝ)|^537 ≤ (2491201329657/25000000000000 : ℝ)^409
        have hw : |(-1726613209/10000000000 : ℝ)|=(1726613209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5637133729/10000000000 : ℝ)|^537 ≤ (47113996414247/100000000000000 : ℝ)^409
        have hw : |(5637133729/10000000000 : ℝ)|=(5637133729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s1_6 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5250837743/10000000000 : ℝ)*x 0 + (281856677/500000000 : ℝ)*x 1 + (-1726614261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5250837743/10000000000 : ℝ)^537 ≤ (21460596176931/50000000000000 : ℝ)^409 := by
    have hnat : (5250837743 : ℕ)^537*50000000000000^409 ≤ 21460596176931^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5250837743 10000000000 21460596176931 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (281856677/500000000 : ℝ)^537 ≤ (11778498585067/25000000000000 : ℝ)^409 := by
    have hnat : (281856677 : ℕ)^537*25000000000000^409 ≤ 11778498585067^409*500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281856677 500000000 11778498585067 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1726614261/10000000000 : ℝ)^537 ≤ (9964813290137/100000000000000 : ℝ)^409 := by
    have hnat : (1726614261 : ℕ)^537*100000000000000^409 ≤ 9964813290137^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1726614261 10000000000 9964813290137 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5250837743/10000000000 : ℝ), (281856677/500000000 : ℝ), (-1726614261/10000000000 : ℝ)] ![(21460596176931/50000000000000 : ℝ), (11778498585067/25000000000000 : ℝ), (9964813290137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5250837743/10000000000 : ℝ)|^537 ≤ (21460596176931/50000000000000 : ℝ)^409
        have hw : |(5250837743/10000000000 : ℝ)|=(5250837743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(281856677/500000000 : ℝ)|^537 ≤ (11778498585067/25000000000000 : ℝ)^409
        have hw : |(281856677/500000000 : ℝ)|=(281856677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1726614261/10000000000 : ℝ)|^537 ≤ (9964813290137/100000000000000 : ℝ)^409
        have hw : |(-1726614261/10000000000 : ℝ)|=(1726614261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s1_7 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2147260421/5000000000 : ℝ)*x 0 + (2473285877/5000000000 : ℝ)*x 1 + (372542029/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2147260421/5000000000 : ℝ)^537 ≤ (32963421087187/100000000000000 : ℝ)^409 := by
    have hnat : (2147260421 : ℕ)^537*100000000000000^409 ≤ 32963421087187^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147260421 5000000000 32963421087187 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2473285877/5000000000 : ℝ)^537 ≤ (39685720507509/100000000000000 : ℝ)^409 := by
    have hnat : (2473285877 : ℕ)^537*100000000000000^409 ≤ 39685720507509^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2473285877 5000000000 39685720507509 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (372542029/1000000000 : ℝ)^537 ≤ (1709428648877/6250000000000 : ℝ)^409 := by
    have hnat : (372542029 : ℕ)^537*6250000000000^409 ≤ 1709428648877^409*1000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      372542029 1000000000 1709428648877 6250000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2147260421/5000000000 : ℝ), (2473285877/5000000000 : ℝ), (372542029/1000000000 : ℝ)] ![(32963421087187/100000000000000 : ℝ), (39685720507509/100000000000000 : ℝ), (1709428648877/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2147260421/5000000000 : ℝ)|^537 ≤ (32963421087187/100000000000000 : ℝ)^409
        have hw : |(2147260421/5000000000 : ℝ)|=(2147260421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2473285877/5000000000 : ℝ)|^537 ≤ (39685720507509/100000000000000 : ℝ)^409
        have hw : |(2473285877/5000000000 : ℝ)|=(2473285877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(372542029/1000000000 : ℝ)|^537 ≤ (1709428648877/6250000000000 : ℝ)^409
        have hw : |(372542029/1000000000 : ℝ)|=(372542029/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1336_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13457/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3417/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19507/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13457/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13457/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1369/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13457/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13457/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1369/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13457/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13457/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1369/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1369/100000 : ℝ) ^ (4295/1024 : ℝ) ≤ (305126554627/20000000000000000000 : ℝ) := by
    have hpowers : (1369/100000 : ℝ)^4295 ≤ (305126554627/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1369 : ℕ)^4295*20000000000000000000^1024 ≤ 305126554627^1024*100000^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1369 100000 305126554627 20000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1369/100000 : ℝ)) (X := (305126554627/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13457/50000 : ℝ) ^ (4295/1024 : ℝ) ≤ (101642956611212919/25000000000000000000 : ℝ) := by
    have hpowers : (13457/50000 : ℝ)^4295 ≤ (101642956611212919/25000000000000000000 : ℝ)^1024 := by
      have hnat : (13457 : ℕ)^4295*25000000000000000000^1024 ≤ 101642956611212919^1024*50000^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13457 50000 101642956611212919 25000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13457/50000 : ℝ)) (X := (101642956611212919/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000305126554627/10000000000000000000 : ℝ) ≤ (2000000014549457/2000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (10000000305126554627/10000000000000000000 : ℝ)^1024 ≤ (2000000014549457/2000000000000000 : ℝ)^4295 := by
      have hnat : (10000000305126554627 : ℕ)^1024*2000000000000000^4295 ≤ 2000000014549457^4295*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000305126554627 10000000000000000000 2000000014549457 2000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000014549457/2000000000000000 : ℝ)) (X := (10000000305126554627/10000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100406573352077624811/100000000000000000000 : ℝ) ≤ (2001935683745531/2000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (100406573352077624811/100000000000000000000 : ℝ)^1024 ≤ (2001935683745531/2000000000000000 : ℝ)^4295 := by
      have hnat : (100406573352077624811 : ℕ)^1024*2000000000000000^4295 ≤ 2001935683745531^4295*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100406573352077624811 100000000000000000000 2001935683745531 2000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2001935683745531/2000000000000000 : ℝ)) (X := (100406573352077624811/100000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12601642956611212919/12500000000000000000 : ℝ) ≤ (400774270588321/400000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (12601642956611212919/12500000000000000000 : ℝ)^1024 ≤ (400774270588321/400000000000000 : ℝ)^4295 := by
      have hnat : (12601642956611212919 : ℕ)^1024*400000000000000^4295 ≤ 400774270588321^4295*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12601642956611212919 12500000000000000000 400774270588321 400000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400774270588321/400000000000000 : ℝ)) (X := (12601642956611212919/12500000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(305126554627/20000000000000000000 : ℝ) ≤ ((17028233503135676151/17030000000000000000 : ℝ)+2*(322611532679/85150000000000 : ℝ)*(1369/100000 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (17028233503135676151/17030000000000000000 : ℝ)+2*(322611532679/85150000000000 : ℝ)*(1369/100000 : ℝ)=(2000000014549457/2000000000000000 : ℝ) by norm_num, show 1+2*(305126554627/20000000000000000000 : ℝ)=(10000000305126554627/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(101642956611212919/25000000000000000000 : ℝ)+(305126554627/20000000000000000000 : ℝ) ≤ ((17028233503135676151/17030000000000000000 : ℝ)+(322611532679/85150000000000 : ℝ)*((13457/50000 : ℝ)+(1369/100000 : ℝ)))^(4295/1024 : ℝ) := by
    rw [show (17028233503135676151/17030000000000000000 : ℝ)+(322611532679/85150000000000 : ℝ)*((13457/50000 : ℝ)+(1369/100000 : ℝ))=(2001935683745531/2000000000000000 : ℝ) by norm_num, show 1+(101642956611212919/25000000000000000000 : ℝ)+(305126554627/20000000000000000000 : ℝ)=(100406573352077624811/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(101642956611212919/25000000000000000000 : ℝ) ≤ ((17028233503135676151/17030000000000000000 : ℝ)+2*(322611532679/85150000000000 : ℝ)*(13457/50000 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (17028233503135676151/17030000000000000000 : ℝ)+2*(322611532679/85150000000000 : ℝ)*(13457/50000 : ℝ)=(400774270588321/400000000000000 : ℝ) by norm_num, show 1+2*(101642956611212919/25000000000000000000 : ℝ)=(12601642956611212919/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17028233503135676151/17030000000000000000 : ℝ)*(X 1 0+X 2 0)+(322611532679/85150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (1369/100000 : ℝ)) (hi := (13457/50000 : ℝ)) (c := (17028233503135676151/17030000000000000000 : ℝ)) (alpha := (322611532679/85150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17028233503135676151/17030000000000000000 : ℝ)*(X 0 1+X 2 1)+(322611532679/85150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (1369/100000 : ℝ)) (hi := (13457/50000 : ℝ)) (c := (17028233503135676151/17030000000000000000 : ℝ)) (alpha := (322611532679/85150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17028233503135676151/17030000000000000000 : ℝ)*(X 0 2+X 1 2)+(322611532679/85150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (1369/100000 : ℝ)) (hi := (13457/50000 : ℝ)) (c := (17028233503135676151/17030000000000000000 : ℝ)) (alpha := (322611532679/85150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-399676619/2000000000 : ℝ)*X 0 0+(1128965903/2000000000 : ℝ)*X 0 1+(5045249821/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((675792797/1250000000 : ℝ)*X 1 0+(-115924879/500000000 : ℝ)*X 1 1+(5045249651/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5406342433/10000000000 : ℝ)*X 2 0+(5045249419/10000000000 : ℝ)*X 2 1+(-2318497801/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4293377297/10000000000 : ℝ)*X 0 0+(3709336673/10000000000 : ℝ)*X 0 1+(4962365953/10000000000 : ℝ)*X 0 2+(4293377297/10000000000 : ℝ)*X 1 0+(3709336673/10000000000 : ℝ)*X 1 1+(4962365953/10000000000 : ℝ)*X 1 2+(4293377297/10000000000 : ℝ)*X 2 0+(3709336673/10000000000 : ℝ)*X 2 1+(4962365953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-499732681/2500000000 : ℝ)*X 0 0+(5052806857/10000000000 : ℝ)*X 0 1+(1409283597/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1312709573/2500000000 : ℝ)*X 1 0+(-1726613209/10000000000 : ℝ)*X 1 1+(5637133729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5250837743/10000000000 : ℝ)*X 2 0+(281856677/500000000 : ℝ)*X 2 1+(-1726614261/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2147260421/5000000000 : ℝ)*X 0 0+(2473285877/5000000000 : ℝ)*X 0 1+(372542029/1000000000 : ℝ)*X 0 2+(2147260421/5000000000 : ℝ)*X 1 0+(2473285877/5000000000 : ℝ)*X 1 1+(372542029/1000000000 : ℝ)*X 1 2+(2147260421/5000000000 : ℝ)*X 2 0+(2473285877/5000000000 : ℝ)*X 2 1+(372542029/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5068679988936841682690838321/851500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (82052013/100000000000000 : ℝ)*(base1) + (865229911/100000000000000 : ℝ)*(base19) + (3531257/400000000000 : ℝ)*(base23) + (166311257/100000000000000 : ℝ)*(upper3) + (80434771/100000000000000 : ℝ)*(upper5) + (1232956216830557/100000000000000 : ℝ)*(major0) + (1232956216830557/100000000000000 : ℝ)*(major1) + (616478108415279/50000000000000 : ℝ)*(major2) + (1667839105864839/100000000000000 : ℝ)*(sp0) + (416960353309257/25000000000000 : ℝ)*(sp1) + (104240087228293/6250000000000 : ℝ)*(sp2) + (199516917846093/25000000000000 : ℝ)*(sp3) + (3254654113/100000000000000 : ℝ)*(sp4) + (2203336177/100000000000000 : ℝ)*(sp7) + (798069956772561/100000000000000 : ℝ)*(f.failure) + (1667842278466939/100000000000000 : ℝ)*(f.sum) + (2780619751643/851500000000000000000000000 : ℝ)*base66 + (14107327218850653893/1703000000000000000000000000000000 : ℝ)*base68 + (58875409851623933/65500000000000000000000000000000 : ℝ)*base69 + (11880156260968653893/1703000000000000000000000000000000 : ℝ)*base72 + (1379784968021/340600000000000000000000000 : ℝ)*base74 + (61932499655876067/65500000000000000000000000000000 : ℝ)*base76 + (6931406540832453893/1703000000000000000000000000000000 : ℝ)*base78 + (916368849375546107/1703000000000000000000000000000000 : ℝ)*base79 + (7255379894991/2128750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (9200891/1250000000000000000000 : ℝ)*base89 + (9200891/1250000000000000000000 : ℝ)*base91 + (3299109/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5095598640689616880071741519/425750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (677377/2500000000000 : ℝ)*(base1) + (1001878629/50000000000000 : ℝ)*(base19) + (339715381/20000000000000 : ℝ)*(base23) + (158092967/100000000000000 : ℝ)*(upper3) + (303704967/100000000000000 : ℝ)*(upper5) + (1265134284940723/100000000000000 : ℝ)*(major0) + (1265134284940723/100000000000000 : ℝ)*(major1) + (1265134284940723/100000000000000 : ℝ)*(major2) + (9935499371/100000000000000 : ℝ)*(sp1) + (1418123157/25000000000000 : ℝ)*(sp2) + (213921245956169/12500000000000 : ℝ)*(sp4) + (1711358001297643/100000000000000 : ℝ)*(sp5) + (85568128474237/5000000000000 : ℝ)*(sp6) + (409449101640661/50000000000000 : ℝ)*(sp7) + (409449115188201/50000000000000 : ℝ)*(f.failure) + (53480310642321/3125000000000 : ℝ)*(f.sum) + (4725903453153/4257500000000000000000000000 : ℝ)*base66 + (4088321616187197173/1703000000000000000000000000000000 : ℝ)*base67 + (958952304124802827/1703000000000000000000000000000000 : ℝ)*base70 + (5680629511384802827/1703000000000000000000000000000000 : ℝ)*base72 + (25674544042019/8515000000000000000000000000 : ℝ)*base73 + (6897064141600802827/1703000000000000000000000000000000 : ℝ)*base76 + (10411962851260802827/1703000000000000000000000000000000 : ℝ)*base78 + (13135404967616802827/1703000000000000000000000000000000 : ℝ)*base80 + (5928860971827/4257500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (4304269/625000000000000000000 : ℝ)*base90 + (4304269/625000000000000000000 : ℝ)*base92 + (4304269/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1336_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13457/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1369/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3417/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19507/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1336_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1336_s2_0 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-254882199/1250000000 : ℝ)*x 0 + (5481405811/10000000000 : ℝ)*x 1 + (2591314153/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (254882199/1250000000 : ℝ)^537 ≤ (2479360183649/20000000000000 : ℝ)^409 := by
    have hnat : (254882199 : ℕ)^537*20000000000000^409 ≤ 2479360183649^409*1250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254882199 1250000000 2479360183649 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5481405811/10000000000 : ℝ)^537 ≤ (11353140164331/25000000000000 : ℝ)^409 := by
    have hnat : (5481405811 : ℕ)^537*25000000000000^409 ≤ 11353140164331^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5481405811 10000000000 11353140164331 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591314153/5000000000 : ℝ)^537 ≤ (1687625536437/4000000000000 : ℝ)^409 := by
    have hnat : (2591314153 : ℕ)^537*4000000000000^409 ≤ 1687625536437^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591314153 5000000000 1687625536437 4000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-254882199/1250000000 : ℝ), (5481405811/10000000000 : ℝ), (2591314153/5000000000 : ℝ)] ![(2479360183649/20000000000000 : ℝ), (11353140164331/25000000000000 : ℝ), (1687625536437/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-254882199/1250000000 : ℝ)|^537 ≤ (2479360183649/20000000000000 : ℝ)^409
        have hw : |(-254882199/1250000000 : ℝ)|=(254882199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5481405811/10000000000 : ℝ)|^537 ≤ (11353140164331/25000000000000 : ℝ)^409
        have hw : |(5481405811/10000000000 : ℝ)|=(5481405811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591314153/5000000000 : ℝ)|^537 ≤ (1687625536437/4000000000000 : ℝ)^409
        have hw : |(2591314153/5000000000 : ℝ)|=(2591314153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s2_1 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (335398663/625000000 : ℝ)*x 0 + (-2193489317/10000000000 : ℝ)*x 1 + (2591314343/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335398663/625000000 : ℝ)^537 ≤ (22082731893529/50000000000000 : ℝ)^409 := by
    have hnat : (335398663 : ℕ)^537*50000000000000^409 ≤ 22082731893529^409*625000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335398663 625000000 22082731893529 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2193489317/10000000000 : ℝ)^537 ≤ (6821946864053/50000000000000 : ℝ)^409 := by
    have hnat : (2193489317 : ℕ)^537*50000000000000^409 ≤ 6821946864053^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193489317 10000000000 6821946864053 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591314343/5000000000 : ℝ)^537 ≤ (42190642472557/100000000000000 : ℝ)^409 := by
    have hnat : (2591314343 : ℕ)^537*100000000000000^409 ≤ 42190642472557^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591314343 5000000000 42190642472557 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335398663/625000000 : ℝ), (-2193489317/10000000000 : ℝ), (2591314343/5000000000 : ℝ)] ![(22082731893529/50000000000000 : ℝ), (6821946864053/50000000000000 : ℝ), (42190642472557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335398663/625000000 : ℝ)|^537 ≤ (22082731893529/50000000000000 : ℝ)^409
        have hw : |(335398663/625000000 : ℝ)|=(335398663/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2193489317/10000000000 : ℝ)|^537 ≤ (6821946864053/50000000000000 : ℝ)^409
        have hw : |(-2193489317/10000000000 : ℝ)|=(2193489317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591314343/5000000000 : ℝ)|^537 ≤ (42190642472557/100000000000000 : ℝ)^409
        have hw : |(2591314343/5000000000 : ℝ)|=(2591314343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s2_2 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5366378697/10000000000 : ℝ)*x 0 + (2591314291/5000000000 : ℝ)*x 1 + (-438697867/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5366378697/10000000000 : ℝ)^537 ≤ (11041366187191/25000000000000 : ℝ)^409 := by
    have hnat : (5366378697 : ℕ)^537*25000000000000^409 ≤ 11041366187191^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5366378697 10000000000 11041366187191 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591314291/5000000000 : ℝ)^537 ≤ (5273830170119/12500000000000 : ℝ)^409 := by
    have hnat : (2591314291 : ℕ)^537*12500000000000^409 ≤ 5273830170119^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591314291 5000000000 5273830170119 12500000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (438697867/2000000000 : ℝ)^537 ≤ (13643893875109/100000000000000 : ℝ)^409 := by
    have hnat : (438697867 : ℕ)^537*100000000000000^409 ≤ 13643893875109^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      438697867 2000000000 13643893875109 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5366378697/10000000000 : ℝ), (2591314291/5000000000 : ℝ), (-438697867/2000000000 : ℝ)] ![(11041366187191/25000000000000 : ℝ), (5273830170119/12500000000000 : ℝ), (13643893875109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5366378697/10000000000 : ℝ)|^537 ≤ (11041366187191/25000000000000 : ℝ)^409
        have hw : |(5366378697/10000000000 : ℝ)|=(5366378697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591314291/5000000000 : ℝ)|^537 ≤ (5273830170119/12500000000000 : ℝ)^409
        have hw : |(2591314291/5000000000 : ℝ)|=(2591314291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-438697867/2000000000 : ℝ)|^537 ≤ (13643893875109/100000000000000 : ℝ)^409
        have hw : |(-438697867/2000000000 : ℝ)|=(438697867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s2_3 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4321801449/10000000000 : ℝ)*x 0 + (502517781/1250000000 : ℝ)*x 1 + (2322270099/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4321801449/10000000000 : ℝ)^537 ≤ (33238624254949/100000000000000 : ℝ)^409 := by
    have hnat : (4321801449 : ℕ)^537*100000000000000^409 ≤ 33238624254949^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4321801449 10000000000 33238624254949 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (502517781/1250000000 : ℝ)^537 ≤ (30226331046981/100000000000000 : ℝ)^409 := by
    have hnat : (502517781 : ℕ)^537*100000000000000^409 ≤ 30226331046981^409*1250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502517781 1250000000 30226331046981 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2322270099/5000000000 : ℝ)^537 ≤ (7307008934371/20000000000000 : ℝ)^409 := by
    have hnat : (2322270099 : ℕ)^537*20000000000000^409 ≤ 7307008934371^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2322270099 5000000000 7307008934371 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4321801449/10000000000 : ℝ), (502517781/1250000000 : ℝ), (2322270099/5000000000 : ℝ)] ![(33238624254949/100000000000000 : ℝ), (30226331046981/100000000000000 : ℝ), (7307008934371/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4321801449/10000000000 : ℝ)|^537 ≤ (33238624254949/100000000000000 : ℝ)^409
        have hw : |(4321801449/10000000000 : ℝ)|=(4321801449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(502517781/1250000000 : ℝ)|^537 ≤ (30226331046981/100000000000000 : ℝ)^409
        have hw : |(502517781/1250000000 : ℝ)|=(502517781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2322270099/5000000000 : ℝ)|^537 ≤ (7307008934371/20000000000000 : ℝ)^409
        have hw : |(2322270099/5000000000 : ℝ)|=(2322270099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s2_4 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1019562677/5000000000 : ℝ)*x 0 + (1296128821/2500000000 : ℝ)*x 1 + (1369875427/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019562677/5000000000 : ℝ)^537 ≤ (1239734182149/10000000000000 : ℝ)^409 := by
    have hnat : (1019562677 : ℕ)^537*10000000000000^409 ≤ 1239734182149^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019562677 5000000000 1239734182149 10000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1296128821/2500000000 : ℝ)^537 ≤ (4221080853591/10000000000000 : ℝ)^409 := by
    have hnat : (1296128821 : ℕ)^537*10000000000000^409 ≤ 4221080853591^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1296128821 2500000000 4221080853591 10000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1369875427/2500000000 : ℝ)^537 ≤ (4539184962051/10000000000000 : ℝ)^409 := by
    have hnat : (1369875427 : ℕ)^537*10000000000000^409 ≤ 4539184962051^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369875427 2500000000 4539184962051 10000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1019562677/5000000000 : ℝ), (1296128821/2500000000 : ℝ), (1369875427/2500000000 : ℝ)] ![(1239734182149/10000000000000 : ℝ), (4221080853591/10000000000000 : ℝ), (4539184962051/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1019562677/5000000000 : ℝ)|^537 ≤ (1239734182149/10000000000000 : ℝ)^409
        have hw : |(-1019562677/5000000000 : ℝ)|=(1019562677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1296128821/2500000000 : ℝ)|^537 ≤ (4221080853591/10000000000000 : ℝ)^409
        have hw : |(1296128821/2500000000 : ℝ)|=(1296128821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1369875427/2500000000 : ℝ)|^537 ≤ (4539184962051/10000000000000 : ℝ)^409
        have hw : |(1369875427/2500000000 : ℝ)|=(1369875427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s2_5 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1057883809/2000000000 : ℝ)*x 0 + (-1896615997/10000000000 : ℝ)*x 1 + (219180069/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057883809/2000000000 : ℝ)^537 ≤ (8667147005781/20000000000000 : ℝ)^409 := by
    have hnat : (1057883809 : ℕ)^537*20000000000000^409 ≤ 8667147005781^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057883809 2000000000 8667147005781 20000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1896615997/10000000000 : ℝ)^537 ≤ (2818103788017/25000000000000 : ℝ)^409 := by
    have hnat : (1896615997 : ℕ)^537*25000000000000^409 ≤ 2818103788017^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1896615997 10000000000 2818103788017 25000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219180069/400000000 : ℝ)^537 ≤ (4539184980541/10000000000000 : ℝ)^409 := by
    have hnat : (219180069 : ℕ)^537*10000000000000^409 ≤ 4539184980541^409*400000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219180069 400000000 4539184980541 10000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057883809/2000000000 : ℝ), (-1896615997/10000000000 : ℝ), (219180069/400000000 : ℝ)] ![(8667147005781/20000000000000 : ℝ), (2818103788017/25000000000000 : ℝ), (4539184980541/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057883809/2000000000 : ℝ)|^537 ≤ (8667147005781/20000000000000 : ℝ)^409
        have hw : |(1057883809/2000000000 : ℝ)|=(1057883809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1896615997/10000000000 : ℝ)|^537 ≤ (2818103788017/25000000000000 : ℝ)^409
        have hw : |(-1896615997/10000000000 : ℝ)|=(1896615997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(219180069/400000000 : ℝ)|^537 ≤ (4539184980541/10000000000000 : ℝ)^409
        have hw : |(219180069/400000000 : ℝ)|=(219180069/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s2_6 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (132235477/250000000 : ℝ)*x 0 + (1095900343/2000000000 : ℝ)*x 1 + (-948307981/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132235477/250000000 : ℝ)^537 ≤ (43335735405399/100000000000000 : ℝ)^409 := by
    have hnat : (132235477 : ℕ)^537*100000000000000^409 ≤ 43335735405399^409*250000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132235477 250000000 43335735405399 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1095900343/2000000000 : ℝ)^537 ≤ (22695924848323/50000000000000 : ℝ)^409 := by
    have hnat : (1095900343 : ℕ)^537*50000000000000^409 ≤ 22695924848323^409*2000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095900343 2000000000 22695924848323 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (948307981/5000000000 : ℝ)^537 ≤ (5636207439473/50000000000000 : ℝ)^409 := by
    have hnat : (948307981 : ℕ)^537*50000000000000^409 ≤ 5636207439473^409*5000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948307981 5000000000 5636207439473 50000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132235477/250000000 : ℝ), (1095900343/2000000000 : ℝ), (-948307981/5000000000 : ℝ)] ![(43335735405399/100000000000000 : ℝ), (22695924848323/50000000000000 : ℝ), (5636207439473/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132235477/250000000 : ℝ)|^537 ≤ (43335735405399/100000000000000 : ℝ)^409
        have hw : |(132235477/250000000 : ℝ)|=(132235477/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1095900343/2000000000 : ℝ)|^537 ≤ (22695924848323/50000000000000 : ℝ)^409
        have hw : |(1095900343/2000000000 : ℝ)|=(1095900343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-948307981/5000000000 : ℝ)|^537 ≤ (5636207439473/50000000000000 : ℝ)^409
        have hw : |(-948307981/5000000000 : ℝ)|=(948307981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1336_s2_7 (p : ℝ) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1080485857/2500000000 : ℝ)*x 0 + (4640597379/10000000000 : ℝ)*x 1 + (1006030227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1080485857/2500000000 : ℝ)^537 ≤ (33240057945927/100000000000000 : ℝ)^409 := by
    have hnat : (1080485857 : ℕ)^537*100000000000000^409 ≤ 33240057945927^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080485857 2500000000 33240057945927 100000000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4640597379/10000000000 : ℝ)^537 ≤ (72988656983/200000000000 : ℝ)^409 := by
    have hnat : (4640597379 : ℕ)^537*200000000000^409 ≤ 72988656983^409*10000000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4640597379 10000000000 72988656983 200000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1006030227/2500000000 : ℝ)^537 ≤ (1891600846329/6250000000000 : ℝ)^409 := by
    have hnat : (1006030227 : ℕ)^537*6250000000000^409 ≤ 1891600846329^409*2500000000^537 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006030227 2500000000 1891600846329 6250000000000 537 409 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (537/128 : ℝ)) 537 409 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1080485857/2500000000 : ℝ), (4640597379/10000000000 : ℝ), (1006030227/2500000000 : ℝ)] ![(33240057945927/100000000000000 : ℝ), (72988656983/200000000000 : ℝ), (1891600846329/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1080485857/2500000000 : ℝ)|^537 ≤ (33240057945927/100000000000000 : ℝ)^409
        have hw : |(1080485857/2500000000 : ℝ)|=(1080485857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4640597379/10000000000 : ℝ)|^537 ≤ (72988656983/200000000000 : ℝ)^409
        have hw : |(4640597379/10000000000 : ℝ)|=(4640597379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1006030227/2500000000 : ℝ)|^537 ≤ (1891600846329/6250000000000 : ℝ)^409
        have hw : |(1006030227/2500000000 : ℝ)|=(1006030227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1336_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19507/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3417/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2453/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (504/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19507/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3417/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19507/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3417/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19507/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3417/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19507/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3417/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19507/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3417/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19507/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3417/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3417/50000 : ℝ) ^ (4295/1024 : ℝ) ≤ (161862177855953/12500000000000000000 : ℝ) := by
    have hpowers : (3417/50000 : ℝ)^4295 ≤ (161862177855953/12500000000000000000 : ℝ)^1024 := by
      have hnat : (3417 : ℕ)^4295*12500000000000000000^1024 ≤ 161862177855953^1024*50000^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3417 50000 161862177855953 12500000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3417/50000 : ℝ)) (X := (161862177855953/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19507/100000 : ℝ) ^ (4295/1024 : ℝ) ≤ (105395104341782591/100000000000000000000 : ℝ) := by
    have hpowers : (19507/100000 : ℝ)^4295 ≤ (105395104341782591/100000000000000000000 : ℝ)^1024 := by
      have hnat : (19507 : ℕ)^4295*100000000000000000000^1024 ≤ 105395104341782591^1024*100000^4295 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19507 100000 105395104341782591 100000000000000000000 4295 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19507/100000 : ℝ)) (X := (105395104341782591/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250161862177855953/6250000000000000000 : ℝ) ≤ (10000061744441667/10000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (6250161862177855953/6250000000000000000 : ℝ)^1024 ≤ (10000061744441667/10000000000000000 : ℝ)^4295 := by
      have hnat : (6250161862177855953 : ℕ)^1024*10000000000000000^4295 ≤ 10000061744441667^4295*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250161862177855953 6250000000000000000 10000061744441667 10000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000061744441667/10000000000000000 : ℝ)) (X := (6250161862177855953/6250000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20021338000352926043/20000000000000000000 : ℝ) ≤ (500127131786659/500000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (20021338000352926043/20000000000000000000 : ℝ)^1024 ≤ (500127131786659/500000000000000 : ℝ)^4295 := by
      have hnat : (20021338000352926043 : ℕ)^1024*500000000000000^4295 ≤ 500127131786659^4295*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20021338000352926043 20000000000000000000 500127131786659 500000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500127131786659/500000000000000 : ℝ)) (X := (20021338000352926043/20000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50105395104341782591/50000000000000000000 : ℝ) ≤ (10005023527024693/10000000000000000 : ℝ) ^ (4295/1024 : ℝ) := by
    have hpowers : (50105395104341782591/50000000000000000000 : ℝ)^1024 ≤ (10005023527024693/10000000000000000 : ℝ)^4295 := by
      have hnat : (50105395104341782591 : ℕ)^1024*10000000000000000^4295 ≤ 10005023527024693^4295*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50105395104341782591 50000000000000000000 10005023527024693 10000000000000000 1024 4295 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005023527024693/10000000000000000 : ℝ)) (X := (50105395104341782591/50000000000000000000 : ℝ)) (by norm_num) 4295 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(161862177855953/12500000000000000000 : ℝ) ≤ ((126696873665136846207/126730000000000000000 : ℝ)+2*(2480891291513/1267300000000000 : ℝ)*(3417/50000 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (126696873665136846207/126730000000000000000 : ℝ)+2*(2480891291513/1267300000000000 : ℝ)*(3417/50000 : ℝ)=(10000061744441667/10000000000000000 : ℝ) by norm_num, show 1+2*(161862177855953/12500000000000000000 : ℝ)=(6250161862177855953/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(105395104341782591/100000000000000000000 : ℝ)+(161862177855953/12500000000000000000 : ℝ) ≤ ((126696873665136846207/126730000000000000000 : ℝ)+(2480891291513/1267300000000000 : ℝ)*((19507/100000 : ℝ)+(3417/50000 : ℝ)))^(4295/1024 : ℝ) := by
    rw [show (126696873665136846207/126730000000000000000 : ℝ)+(2480891291513/1267300000000000 : ℝ)*((19507/100000 : ℝ)+(3417/50000 : ℝ))=(500127131786659/500000000000000 : ℝ) by norm_num, show 1+(105395104341782591/100000000000000000000 : ℝ)+(161862177855953/12500000000000000000 : ℝ)=(20021338000352926043/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(105395104341782591/100000000000000000000 : ℝ) ≤ ((126696873665136846207/126730000000000000000 : ℝ)+2*(2480891291513/1267300000000000 : ℝ)*(19507/100000 : ℝ))^(4295/1024 : ℝ) := by
    rw [show (126696873665136846207/126730000000000000000 : ℝ)+2*(2480891291513/1267300000000000 : ℝ)*(19507/100000 : ℝ)=(10005023527024693/10000000000000000 : ℝ) by norm_num, show 1+2*(105395104341782591/100000000000000000000 : ℝ)=(50105395104341782591/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (126696873665136846207/126730000000000000000 : ℝ)*(X 1 0+X 2 0)+(2480891291513/1267300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (3417/50000 : ℝ)) (hi := (19507/100000 : ℝ)) (c := (126696873665136846207/126730000000000000000 : ℝ)) (alpha := (2480891291513/1267300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (126696873665136846207/126730000000000000000 : ℝ)*(X 0 1+X 2 1)+(2480891291513/1267300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (3417/50000 : ℝ)) (hi := (19507/100000 : ℝ)) (c := (126696873665136846207/126730000000000000000 : ℝ)) (alpha := (2480891291513/1267300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (126696873665136846207/126730000000000000000 : ℝ)*(X 0 2+X 1 2)+(2480891291513/1267300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4295/1024 : ℝ)) (lo := (3417/50000 : ℝ)) (hi := (19507/100000 : ℝ)) (c := (126696873665136846207/126730000000000000000 : ℝ)) (alpha := (2480891291513/1267300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-254882199/1250000000 : ℝ)*X 0 0+(5481405811/10000000000 : ℝ)*X 0 1+(2591314153/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335398663/625000000 : ℝ)*X 1 0+(-2193489317/10000000000 : ℝ)*X 1 1+(2591314343/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5366378697/10000000000 : ℝ)*X 2 0+(2591314291/5000000000 : ℝ)*X 2 1+(-438697867/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4321801449/10000000000 : ℝ)*X 0 0+(502517781/1250000000 : ℝ)*X 0 1+(2322270099/5000000000 : ℝ)*X 0 2+(4321801449/10000000000 : ℝ)*X 1 0+(502517781/1250000000 : ℝ)*X 1 1+(2322270099/5000000000 : ℝ)*X 1 2+(4321801449/10000000000 : ℝ)*X 2 0+(502517781/1250000000 : ℝ)*X 2 1+(2322270099/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1019562677/5000000000 : ℝ)*X 0 0+(1296128821/2500000000 : ℝ)*X 0 1+(1369875427/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057883809/2000000000 : ℝ)*X 1 0+(-1896615997/10000000000 : ℝ)*X 1 1+(219180069/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((132235477/250000000 : ℝ)*X 2 0+(1095900343/2000000000 : ℝ)*X 2 1+(-948307981/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1080485857/2500000000 : ℝ)*X 0 0+(4640597379/10000000000 : ℝ)*X 0 1+(1006030227/2500000000 : ℝ)*X 0 2+(1080485857/2500000000 : ℝ)*X 1 0+(4640597379/10000000000 : ℝ)*X 1 1+(1006030227/2500000000 : ℝ)*X 1 2+(1080485857/2500000000 : ℝ)*X 2 0+(4640597379/10000000000 : ℝ)*X 2 1+(1006030227/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1336_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5939774498412413134265901147/792062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (66347357/5000000000000 : ℝ)*(base19) + (672494451/50000000000000 : ℝ)*(base23) + (10053251/50000000000000 : ℝ)*(lower2) + (89338887/50000000000000 : ℝ)*(upper3) + (36342439/25000000000000 : ℝ)*(upper5) + (618571498904807/25000000000000 : ℝ)*(major0) + (618571498904807/25000000000000 : ℝ)*(major1) + (2474285995619229/100000000000000 : ℝ)*(major2) + (3346991976623171/100000000000000 : ℝ)*(sp0) + (3347010447622887/100000000000000 : ℝ)*(sp1) + (1673505214790563/50000000000000 : ℝ)*(sp2) + (100096940226367/6250000000000 : ℝ)*(sp3) + (2474743357/12500000000000 : ℝ)*(sp4) + (2230768941/25000000000000 : ℝ)*(sp7) + (400389991674409/25000000000000 : ℝ)*(f.failure) + (3347011774570027/100000000000000 : ℝ)*(f.sum) + (27746350750459/6670000000000000000000000000 : ℝ)*base65 + (45148508044366307951/3168250000000000000000000000000000 : ℝ)*base68 + (98226100223064685597/12673000000000000000000000000000000 : ℝ)*base70 + (63769289809213057951/3168250000000000000000000000000000 : ℝ)*base72 + (20389658449229/6670000000000000000000000000 : ℝ)*base73 + (79056140564251314403/12673000000000000000000000000000000 : ℝ)*base75 + (25659195403750382951/3168250000000000000000000000000000 : ℝ)*base78 + (75204193228936882951/3168250000000000000000000000000000 : ℝ)*base80 + (24104793277647/31682500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (3810179/312500000000000000000 : ℝ)*base89 + (3810179/312500000000000000000 : ℝ)*base91 + (685179/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18022673251290075074307/3168250000000000000000000000 : ℝ) := by norm_num
    linear_combination (295460137/25000000000000 : ℝ)*(base19) + (344588721/25000000000000 : ℝ)*(base23) + (77249037/50000000000000 : ℝ)*(upper3) + (66932571/100000000000000 : ℝ)*(lower4) + (74982237/100000000000000 : ℝ)*(upper5) + (125302671033651/5000000000000 : ℝ)*(major0) + (125302671033651/5000000000000 : ℝ)*(major1) + (125302671033651/5000000000000 : ℝ)*(major2) + (2597175659/20000000000000 : ℝ)*(sp1) + (16253447367/100000000000000 : ℝ)*(sp2) + (67799684262991/2000000000000 : ℝ)*(sp4) + (847492511357677/25000000000000 : ℝ)*(sp5) + (1694983290673649/50000000000000 : ℝ)*(sp6) + (1622122438578937/100000000000000 : ℝ)*(sp7) + (1622122438578937/100000000000000 : ℝ)*(f.failure) + (67799684262991/2000000000000 : ℝ)*(f.sum) + (8332240361819/3168250000000000000000000000 : ℝ)*base66 + (4887301157436061757/633650000000000000000000000000000 : ℝ)*base67 + (4270410062790388243/633650000000000000000000000000000 : ℝ)*base70 + (4364746011859388243/633650000000000000000000000000000 : ℝ)*base72 + (9763708125527/1584125000000000000000000000 : ℝ)*base73 + (5627251315375888243/633650000000000000000000000000000 : ℝ)*base76 + (245286220291261757/633650000000000000000000000000000 : ℝ)*base77 + (4319717113372461757/633650000000000000000000000000000 : ℝ)*base79 + (33477588350923/12673000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (12177453/1250000000000000000000 : ℝ)*base90 + (12177453/1250000000000000000000 : ℝ)*base92 + (12177453/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1336_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19507/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3417/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2453/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (504/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1336_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1336_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2453/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (504/3125 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1336_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1336_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1336_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4295/1024 : ℝ) ≤ p) (hpb : p ≤ (537/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19311531/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2453/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (504/3125 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1336_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
