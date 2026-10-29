-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1485_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:14:11.333003+00:00
-- url     : https://prove2.me/submissions/25e606ae-4367-4bb7-929c-01fb8d2bf879

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
theorem support_rectangle_w1485_s3_0 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1907969807/10000000000 : ℝ)*x 0 + (5441220257/10000000000 : ℝ)*x 1 + (5212151669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1907969807/10000000000 : ℝ)^4467 ≤ (11657425200543/100000000000000 : ℝ)^3443 := by
    have hnat : (1907969807 : ℕ)^4467*100000000000000^3443 ≤ 11657425200543^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907969807 10000000000 11657425200543 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5441220257/10000000000 : ℝ)^4467 ≤ (45403403694007/100000000000000 : ℝ)^3443 := by
    have hnat : (5441220257 : ℕ)^4467*100000000000000^3443 ≤ 45403403694007^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5441220257 10000000000 45403403694007 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5212151669/10000000000 : ℝ)^4467 ≤ (21469585545751/50000000000000 : ℝ)^3443 := by
    have hnat : (5212151669 : ℕ)^4467*50000000000000^3443 ≤ 21469585545751^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5212151669 10000000000 21469585545751 50000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1907969807/10000000000 : ℝ), (5441220257/10000000000 : ℝ), (5212151669/10000000000 : ℝ)] ![(11657425200543/100000000000000 : ℝ), (45403403694007/100000000000000 : ℝ), (21469585545751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1907969807/10000000000 : ℝ)|^4467 ≤ (11657425200543/100000000000000 : ℝ)^3443
        have hw : |(-1907969807/10000000000 : ℝ)|=(1907969807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5441220257/10000000000 : ℝ)|^4467 ≤ (45403403694007/100000000000000 : ℝ)^3443
        have hw : |(5441220257/10000000000 : ℝ)|=(5441220257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5212151669/10000000000 : ℝ)|^4467 ≤ (21469585545751/50000000000000 : ℝ)^3443
        have hw : |(5212151669/10000000000 : ℝ)|=(5212151669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s3_1 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677102991/5000000000 : ℝ)*x 0 + (-2025462223/10000000000 : ℝ)*x 1 + (162879741/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677102991/5000000000 : ℝ)^4467 ≤ (8892725855367/20000000000000 : ℝ)^3443 := by
    have hnat : (2677102991 : ℕ)^4467*20000000000000^3443 ≤ 8892725855367^3443*5000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677102991 5000000000 8892725855367 20000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2025462223/10000000000 : ℝ)^4467 ≤ (12597199163513/100000000000000 : ℝ)^3443 := by
    have hnat : (2025462223 : ℕ)^4467*100000000000000^3443 ≤ 12597199163513^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025462223 10000000000 12597199163513 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (162879741/312500000 : ℝ)^4467 ≤ (21469585775553/50000000000000 : ℝ)^3443 := by
    have hnat : (162879741 : ℕ)^4467*50000000000000^3443 ≤ 21469585775553^3443*312500000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162879741 312500000 21469585775553 50000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677102991/5000000000 : ℝ), (-2025462223/10000000000 : ℝ), (162879741/312500000 : ℝ)] ![(8892725855367/20000000000000 : ℝ), (12597199163513/100000000000000 : ℝ), (21469585775553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677102991/5000000000 : ℝ)|^4467 ≤ (8892725855367/20000000000000 : ℝ)^3443
        have hw : |(2677102991/5000000000 : ℝ)|=(2677102991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2025462223/10000000000 : ℝ)|^4467 ≤ (12597199163513/100000000000000 : ℝ)^3443
        have hw : |(-2025462223/10000000000 : ℝ)|=(2025462223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(162879741/312500000 : ℝ)|^4467 ≤ (21469585775553/50000000000000 : ℝ)^3443
        have hw : |(162879741/312500000 : ℝ)|=(162879741/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s3_2 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5354205891/10000000000 : ℝ)*x 0 + (2606075831/5000000000 : ℝ)*x 1 + (-2025462409/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5354205891/10000000000 : ℝ)^4467 ≤ (355709026371/800000000000 : ℝ)^3443 := by
    have hnat : (5354205891 : ℕ)^4467*800000000000^3443 ≤ 355709026371^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5354205891 10000000000 355709026371 800000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2606075831/5000000000 : ℝ)^4467 ≤ (42939171016683/100000000000000 : ℝ)^3443 := by
    have hnat : (2606075831 : ℕ)^4467*100000000000000^3443 ≤ 42939171016683^3443*5000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606075831 5000000000 42939171016683 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2025462409/10000000000 : ℝ)^4467 ≤ (6298600332189/50000000000000 : ℝ)^3443 := by
    have hnat : (2025462409 : ℕ)^4467*50000000000000^3443 ≤ 6298600332189^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2025462409 10000000000 6298600332189 50000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5354205891/10000000000 : ℝ), (2606075831/5000000000 : ℝ), (-2025462409/10000000000 : ℝ)] ![(355709026371/800000000000 : ℝ), (42939171016683/100000000000000 : ℝ), (6298600332189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5354205891/10000000000 : ℝ)|^4467 ≤ (355709026371/800000000000 : ℝ)^3443
        have hw : |(5354205891/10000000000 : ℝ)|=(5354205891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2606075831/5000000000 : ℝ)|^4467 ≤ (42939171016683/100000000000000 : ℝ)^3443
        have hw : |(2606075831/5000000000 : ℝ)|=(2606075831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2025462409/10000000000 : ℝ)|^4467 ≤ (6298600332189/50000000000000 : ℝ)^3443
        have hw : |(-2025462409/10000000000 : ℝ)|=(2025462409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s3_3 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535260937/1250000000 : ℝ)*x 0 + (2016943111/5000000000 : ℝ)*x 1 + (2271725717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535260937/1250000000 : ℝ)^4467 ≤ (1663697470431/5000000000000 : ℝ)^3443 := by
    have hnat : (535260937 : ℕ)^4467*5000000000000^3443 ≤ 1663697470431^3443*1250000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535260937 1250000000 1663697470431 5000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2016943111/5000000000 : ℝ)^4467 ≤ (7698390435067/25000000000000 : ℝ)^3443 := by
    have hnat : (2016943111 : ℕ)^4467*25000000000000^3443 ≤ 7698390435067^3443*5000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2016943111 5000000000 7698390435067 25000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2271725717/5000000000 : ℝ)^4467 ≤ (449156110361/1250000000000 : ℝ)^3443 := by
    have hnat : (2271725717 : ℕ)^4467*1250000000000^3443 ≤ 449156110361^3443*5000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2271725717 5000000000 449156110361 1250000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535260937/1250000000 : ℝ), (2016943111/5000000000 : ℝ), (2271725717/5000000000 : ℝ)] ![(1663697470431/5000000000000 : ℝ), (7698390435067/25000000000000 : ℝ), (449156110361/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535260937/1250000000 : ℝ)|^4467 ≤ (1663697470431/5000000000000 : ℝ)^3443
        have hw : |(535260937/1250000000 : ℝ)|=(535260937/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2016943111/5000000000 : ℝ)|^4467 ≤ (7698390435067/25000000000000 : ℝ)^3443
        have hw : |(2016943111/5000000000 : ℝ)|=(2016943111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2271725717/5000000000 : ℝ)|^4467 ≤ (449156110361/1250000000000 : ℝ)^3443
        have hw : |(2271725717/5000000000 : ℝ)|=(2271725717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s3_4 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-381600707/2000000000 : ℝ)*x 0 + (5213369197/10000000000 : ℝ)*x 1 + (2719996713/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (381600707/2000000000 : ℝ)^4467 ≤ (1457211570481/12500000000000 : ℝ)^3443 := by
    have hnat : (381600707 : ℕ)^4467*12500000000000^3443 ≤ 1457211570481^3443*2000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      381600707 2000000000 1457211570481 12500000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213369197/10000000000 : ℝ)^4467 ≤ (10738046263749/25000000000000 : ℝ)^3443 := by
    have hnat : (5213369197 : ℕ)^4467*25000000000000^3443 ≤ 10738046263749^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213369197 10000000000 10738046263749 25000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2719996713/5000000000 : ℝ)^4467 ≤ (9078024474967/20000000000000 : ℝ)^3443 := by
    have hnat : (2719996713 : ℕ)^4467*20000000000000^3443 ≤ 9078024474967^3443*5000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2719996713 5000000000 9078024474967 20000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-381600707/2000000000 : ℝ), (5213369197/10000000000 : ℝ), (2719996713/5000000000 : ℝ)] ![(1457211570481/12500000000000 : ℝ), (10738046263749/25000000000000 : ℝ), (9078024474967/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-381600707/2000000000 : ℝ)|^4467 ≤ (1457211570481/12500000000000 : ℝ)^3443
        have hw : |(-381600707/2000000000 : ℝ)|=(381600707/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213369197/10000000000 : ℝ)|^4467 ≤ (10738046263749/25000000000000 : ℝ)^3443
        have hw : |(5213369197/10000000000 : ℝ)|=(5213369197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2719996713/5000000000 : ℝ)|^4467 ≤ (9078024474967/20000000000000 : ℝ)^3443
        have hw : |(2719996713/5000000000 : ℝ)|=(2719996713/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s3_5 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264716407/500000000 : ℝ)*x 0 + (-449405171/2500000000 : ℝ)*x 1 + (679999189/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264716407/500000000 : ℝ)^4467 ≤ (2738722725811/6250000000000 : ℝ)^3443 := by
    have hnat : (264716407 : ℕ)^4467*6250000000000^3443 ≤ 2738722725811^3443*500000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264716407 500000000 2738722725811 6250000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (449405171/2500000000 : ℝ)^4467 ≤ (5395156535421/50000000000000 : ℝ)^3443 := by
    have hnat : (449405171 : ℕ)^4467*50000000000000^3443 ≤ 5395156535421^3443*2500000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449405171 2500000000 5395156535421 50000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (679999189/1250000000 : ℝ)^4467 ≤ (9078024661163/20000000000000 : ℝ)^3443 := by
    have hnat : (679999189 : ℕ)^4467*20000000000000^3443 ≤ 9078024661163^3443*1250000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679999189 1250000000 9078024661163 20000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264716407/500000000 : ℝ), (-449405171/2500000000 : ℝ), (679999189/1250000000 : ℝ)] ![(2738722725811/6250000000000 : ℝ), (5395156535421/50000000000000 : ℝ), (9078024661163/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264716407/500000000 : ℝ)|^4467 ≤ (2738722725811/6250000000000 : ℝ)^3443
        have hw : |(264716407/500000000 : ℝ)|=(264716407/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-449405171/2500000000 : ℝ)|^4467 ≤ (5395156535421/50000000000000 : ℝ)^3443
        have hw : |(-449405171/2500000000 : ℝ)|=(449405171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(679999189/1250000000 : ℝ)|^4467 ≤ (9078024661163/20000000000000 : ℝ)^3443
        have hw : |(679999189/1250000000 : ℝ)|=(679999189/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s3_6 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294328251/10000000000 : ℝ)*x 0 + (5439993353/10000000000 : ℝ)*x 1 + (-1797620751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294328251/10000000000 : ℝ)^4467 ≤ (684680700077/1562500000000 : ℝ)^3443 := by
    have hnat : (5294328251 : ℕ)^4467*1562500000000^3443 ≤ 684680700077^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294328251 10000000000 684680700077 1562500000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5439993353/10000000000 : ℝ)^4467 ≤ (9078024316917/20000000000000 : ℝ)^3443 := by
    have hnat : (5439993353 : ℕ)^4467*20000000000000^3443 ≤ 9078024316917^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5439993353 10000000000 9078024316917 20000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1797620751/10000000000 : ℝ)^4467 ≤ (86322508741/800000000000 : ℝ)^3443 := by
    have hnat : (1797620751 : ℕ)^4467*800000000000^3443 ≤ 86322508741^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1797620751 10000000000 86322508741 800000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294328251/10000000000 : ℝ), (5439993353/10000000000 : ℝ), (-1797620751/10000000000 : ℝ)] ![(684680700077/1562500000000 : ℝ), (9078024316917/20000000000000 : ℝ), (86322508741/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294328251/10000000000 : ℝ)|^4467 ≤ (684680700077/1562500000000 : ℝ)^3443
        have hw : |(5294328251/10000000000 : ℝ)|=(5294328251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5439993353/10000000000 : ℝ)|^4467 ≤ (9078024316917/20000000000000 : ℝ)^3443
        have hw : |(5439993353/10000000000 : ℝ)|=(5439993353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1797620751/10000000000 : ℝ)|^4467 ≤ (86322508741/800000000000 : ℝ)^3443
        have hw : |(-1797620751/10000000000 : ℝ)|=(1797620751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s3_7 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4282162667/10000000000 : ℝ)*x 0 + (181629717/400000000 : ℝ)*x 1 + (63072113/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282162667/10000000000 : ℝ)^4467 ≤ (6654941450311/20000000000000 : ℝ)^3443 := by
    have hnat : (4282162667 : ℕ)^4467*20000000000000^3443 ≤ 6654941450311^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282162667 10000000000 6654941450311 20000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181629717/400000000 : ℝ)^4467 ≤ (35904699880329/100000000000000 : ℝ)^3443 := by
    have hnat : (181629717 : ℕ)^4467*100000000000000^3443 ≤ 35904699880329^3443*400000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181629717 400000000 35904699880329 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (63072113/156250000 : ℝ)^4467 ≤ (30820592858953/100000000000000 : ℝ)^3443 := by
    have hnat : (63072113 : ℕ)^4467*100000000000000^3443 ≤ 30820592858953^3443*156250000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      63072113 156250000 30820592858953 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282162667/10000000000 : ℝ), (181629717/400000000 : ℝ), (63072113/156250000 : ℝ)] ![(6654941450311/20000000000000 : ℝ), (35904699880329/100000000000000 : ℝ), (30820592858953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282162667/10000000000 : ℝ)|^4467 ≤ (6654941450311/20000000000000 : ℝ)^3443
        have hw : |(4282162667/10000000000 : ℝ)|=(4282162667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(181629717/400000000 : ℝ)|^4467 ≤ (35904699880329/100000000000000 : ℝ)^3443
        have hw : |(181629717/400000000 : ℝ)|=(181629717/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(63072113/156250000 : ℝ)|^4467 ≤ (30820592858953/100000000000000 : ℝ)^3443
        have hw : |(63072113/156250000 : ℝ)|=(63072113/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1485_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80612767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4027/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10721/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1557/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4027/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10227/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4027/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10227/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4027/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10227/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4027/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10227/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4027/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10227/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4027/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10227/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10227/100000 : ℝ) ^ (4465/1024 : ℝ) ≤ (4810101719891981/100000000000000000000 : ℝ) := by
    have hpowers : (10227/100000 : ℝ)^4465 ≤ (4810101719891981/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10227 : ℕ)^4465*100000000000000000000^1024 ≤ 4810101719891981^1024*100000^4465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10227 100000 4810101719891981 100000000000000000000 4465 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10227/100000 : ℝ)) (X := (4810101719891981/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4027/25000 : ℝ) ^ (4465/1024 : ℝ) ≤ (544807049994663/1562500000000000000 : ℝ) := by
    have hpowers : (4027/25000 : ℝ)^4465 ≤ (544807049994663/1562500000000000000 : ℝ)^1024 := by
      have hnat : (4027 : ℕ)^4465*1562500000000000000^1024 ≤ 544807049994663^1024*25000^4465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4027 25000 544807049994663 1562500000000000000 4465 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4027/25000 : ℝ)) (X := (544807049994663/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004810101719891981/50000000000000000000 : ℝ) ≤ (10000220620899609/10000000000000000 : ℝ) ^ (4465/1024 : ℝ) := by
    have hpowers : (50004810101719891981/50000000000000000000 : ℝ)^1024 ≤ (10000220620899609/10000000000000000 : ℝ)^4465 := by
      have hnat : (50004810101719891981 : ℕ)^1024*10000000000000000^4465 ≤ 10000220620899609^4465*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004810101719891981 50000000000000000000 10000220620899609 10000000000000000 1024 4465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000220620899609/10000000000000000 : ℝ)) (X := (50004810101719891981/50000000000000000000 : ℝ)) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100039677752919550413/100000000000000000000 : ℝ) ≤ (5000454913869017/5000000000000000 : ℝ) ^ (4465/1024 : ℝ) := by
    have hpowers : (100039677752919550413/100000000000000000000 : ℝ)^1024 ≤ (5000454913869017/5000000000000000 : ℝ)^4465 := by
      have hnat : (100039677752919550413 : ℕ)^1024*5000000000000000^4465 ≤ 5000454913869017^4465*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100039677752919550413 100000000000000000000 5000454913869017 5000000000000000 1024 4465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000454913869017/5000000000000000 : ℝ)) (X := (100039677752919550413/100000000000000000000 : ℝ)) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (781794807049994663/781250000000000000 : ℝ) ≤ (10001599034576459/10000000000000000 : ℝ) ^ (4465/1024 : ℝ) := by
    have hpowers : (781794807049994663/781250000000000000 : ℝ)^1024 ≤ (10001599034576459/10000000000000000 : ℝ)^4465 := by
      have hnat : (781794807049994663 : ℕ)^1024*10000000000000000^4465 ≤ 10001599034576459^4465*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781794807049994663 781250000000000000 10001599034576459 10000000000000000 1024 4465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001599034576459/10000000000000000 : ℝ)) (X := (781794807049994663/781250000000000000 : ℝ)) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4810101719891981/100000000000000000000 : ℝ) ≤ ((58797200434837455579/58810000000000000000 : ℝ)+2*(27568273537/23524000000000 : ℝ)*(10227/100000 : ℝ))^(4465/1024 : ℝ) := by
    rw [show (58797200434837455579/58810000000000000000 : ℝ)+2*(27568273537/23524000000000 : ℝ)*(10227/100000 : ℝ)=(10000220620899609/10000000000000000 : ℝ) by norm_num, show 1+2*(4810101719891981/100000000000000000000 : ℝ)=(50004810101719891981/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(544807049994663/1562500000000000000 : ℝ)+(4810101719891981/100000000000000000000 : ℝ) ≤ ((58797200434837455579/58810000000000000000 : ℝ)+(27568273537/23524000000000 : ℝ)*((4027/25000 : ℝ)+(10227/100000 : ℝ)))^(4465/1024 : ℝ) := by
    rw [show (58797200434837455579/58810000000000000000 : ℝ)+(27568273537/23524000000000 : ℝ)*((4027/25000 : ℝ)+(10227/100000 : ℝ))=(5000454913869017/5000000000000000 : ℝ) by norm_num, show 1+(544807049994663/1562500000000000000 : ℝ)+(4810101719891981/100000000000000000000 : ℝ)=(100039677752919550413/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(544807049994663/1562500000000000000 : ℝ) ≤ ((58797200434837455579/58810000000000000000 : ℝ)+2*(27568273537/23524000000000 : ℝ)*(4027/25000 : ℝ))^(4465/1024 : ℝ) := by
    rw [show (58797200434837455579/58810000000000000000 : ℝ)+2*(27568273537/23524000000000 : ℝ)*(4027/25000 : ℝ)=(10001599034576459/10000000000000000 : ℝ) by norm_num, show 1+2*(544807049994663/1562500000000000000 : ℝ)=(781794807049994663/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (58797200434837455579/58810000000000000000 : ℝ)*(X 1 0+X 2 0)+(27568273537/23524000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4465/1024 : ℝ)) (lo := (10227/100000 : ℝ)) (hi := (4027/25000 : ℝ)) (c := (58797200434837455579/58810000000000000000 : ℝ)) (alpha := (27568273537/23524000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (58797200434837455579/58810000000000000000 : ℝ)*(X 0 1+X 2 1)+(27568273537/23524000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4465/1024 : ℝ)) (lo := (10227/100000 : ℝ)) (hi := (4027/25000 : ℝ)) (c := (58797200434837455579/58810000000000000000 : ℝ)) (alpha := (27568273537/23524000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (58797200434837455579/58810000000000000000 : ℝ)*(X 0 2+X 1 2)+(27568273537/23524000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4465/1024 : ℝ)) (lo := (10227/100000 : ℝ)) (hi := (4027/25000 : ℝ)) (c := (58797200434837455579/58810000000000000000 : ℝ)) (alpha := (27568273537/23524000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1907969807/10000000000 : ℝ)*X 0 0+(5441220257/10000000000 : ℝ)*X 0 1+(5212151669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677102991/5000000000 : ℝ)*X 1 0+(-2025462223/10000000000 : ℝ)*X 1 1+(162879741/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5354205891/10000000000 : ℝ)*X 2 0+(2606075831/5000000000 : ℝ)*X 2 1+(-2025462409/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((535260937/1250000000 : ℝ)*X 0 0+(2016943111/5000000000 : ℝ)*X 0 1+(2271725717/5000000000 : ℝ)*X 0 2+(535260937/1250000000 : ℝ)*X 1 0+(2016943111/5000000000 : ℝ)*X 1 1+(2271725717/5000000000 : ℝ)*X 1 2+(535260937/1250000000 : ℝ)*X 2 0+(2016943111/5000000000 : ℝ)*X 2 1+(2271725717/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-381600707/2000000000 : ℝ)*X 0 0+(5213369197/10000000000 : ℝ)*X 0 1+(2719996713/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((264716407/500000000 : ℝ)*X 1 0+(-449405171/2500000000 : ℝ)*X 1 1+(679999189/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294328251/10000000000 : ℝ)*X 2 0+(5439993353/10000000000 : ℝ)*X 2 1+(-1797620751/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4282162667/10000000000 : ℝ)*X 0 0+(181629717/400000000 : ℝ)*X 0 1+(63072113/156250000 : ℝ)*X 0 2+(4282162667/10000000000 : ℝ)*X 1 0+(181629717/400000000 : ℝ)*X 1 1+(63072113/156250000 : ℝ)*X 1 2+(4282162667/10000000000 : ℝ)*X 2 0+(181629717/400000000 : ℝ)*X 2 1+(63072113/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15814259566650217598270442519/1470250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (486719433/20000000000000 : ℝ)*(base19) + (2325921869/100000000000000 : ℝ)*(base23) + (74247709/20000000000000 : ℝ)*(upper3) + (17924801/100000000000000 : ℝ)*(upper4) + (20552701/12500000000000 : ℝ)*(upper5) + (1582018175517571/50000000000000 : ℝ)*(major0) + (1582018175517571/50000000000000 : ℝ)*(major1) + (1582018175517571/50000000000000 : ℝ)*(major2) + (68211653513933/1562500000000 : ℝ)*(sp0) + (4365579060913151/100000000000000 : ℝ)*(sp1) + (2182789584294223/50000000000000 : ℝ)*(sp2) + (1962472989954629/100000000000000 : ℝ)*(sp3) + (7133923721/20000000000000 : ℝ)*(sp4) + (17859066309/100000000000000 : ℝ)*(sp7) + (981245424510469/50000000000000 : ℝ)*(f.failure) + (1091395373627579/25000000000000 : ℝ)*(f.sum) + (11365218820401/2940500000000000000000000000 : ℝ)*base65 + (41109490015717978609/2940500000000000000000000000000000 : ℝ)*base67 + (26592802857167978609/2940500000000000000000000000000000 : ℝ)*base69 + (23932798219569478609/2940500000000000000000000000000000 : ℝ)*base71 + (796407872507/147025000000000000000000000 : ℝ)*base73 + (42190372079180978609/2940500000000000000000000000000000 : ℝ)*base75 + (40808133340757478609/2940500000000000000000000000000000 : ℝ)*base77 + (56394276403156478609/2940500000000000000000000000000000 : ℝ)*base79 + (2210914942279/588100000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (23442277/2500000000000000000000 : ℝ)*base90 + (23442277/2500000000000000000000 : ℝ)*base92 + (23442277/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8256341475681496264781513979/735125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56602667/2500000000000 : ℝ)*(base19) + (471990491/20000000000000 : ℝ)*(base23) + (274074323/100000000000000 : ℝ)*(upper3) + (6230471/50000000000000 : ℝ)*(lower4) + (323347241/100000000000000 : ℝ)*(upper5) + (799527096651711/25000000000000 : ℝ)*(major0) + (799527096651711/25000000000000 : ℝ)*(major1) + (799527096651711/25000000000000 : ℝ)*(major2) + (34950043697/100000000000000 : ℝ)*(sp1) + (2072732473/6250000000000 : ℝ)*(sp2) + (137893512462693/3125000000000 : ℝ)*(sp4) + (22062775923279/500000000000 : ℝ)*(sp5) + (2206278437567077/50000000000000 : ℝ)*(sp6) + (991812000016959/50000000000000 : ℝ)*(sp7) + (991812000016959/50000000000000 : ℝ)*(f.failure) + (137893512462693/3125000000000 : ℝ)*(f.sum) + (21709923044743/2940500000000000000000000000 : ℝ)*base66 + (3243642920068845669/1470250000000000000000000000000000 : ℝ)*base67 + (20559737052186345669/1470250000000000000000000000000000 : ℝ)*base69 + (1443386577224345669/1470250000000000000000000000000000 : ℝ)*base71 + (44241406340099/5881000000000000000000000000 : ℝ)*base74 + (11652477534354345669/1470250000000000000000000000000000 : ℝ)*base75 + (4969410275792345669/1470250000000000000000000000000000 : ℝ)*base77 + (9617706392322345669/1470250000000000000000000000000000 : ℝ)*base79 + (2206583431267/588100000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (11915553/2500000000000000000000 : ℝ)*base89 + (11915553/2500000000000000000000 : ℝ)*base91 + (11915553/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1485_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80612767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4027/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10721/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1557/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1485_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1485_s4_0 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-954281887/5000000000 : ℝ)*x 0 + (5437361287/10000000000 : ℝ)*x 1 + (5215619033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954281887/5000000000 : ℝ)^4467 ≤ (11662133808037/100000000000000 : ℝ)^3443 := by
    have hnat : (954281887 : ℕ)^4467*100000000000000^3443 ≤ 11662133808037^3443*5000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954281887 5000000000 11662133808037 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437361287/10000000000 : ℝ)^4467 ≤ (9072326120367/20000000000000 : ℝ)^3443 := by
    have hnat : (5437361287 : ℕ)^4467*20000000000000^3443 ≤ 9072326120367^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437361287 10000000000 9072326120367 20000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5215619033/10000000000 : ℝ)^4467 ≤ (42976235573241/100000000000000 : ℝ)^3443 := by
    have hnat : (5215619033 : ℕ)^4467*100000000000000^3443 ≤ 42976235573241^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5215619033 10000000000 42976235573241 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-954281887/5000000000 : ℝ), (5437361287/10000000000 : ℝ), (5215619033/10000000000 : ℝ)] ![(11662133808037/100000000000000 : ℝ), (9072326120367/20000000000000 : ℝ), (42976235573241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-954281887/5000000000 : ℝ)|^4467 ≤ (11662133808037/100000000000000 : ℝ)^3443
        have hw : |(-954281887/5000000000 : ℝ)|=(954281887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437361287/10000000000 : ℝ)|^4467 ≤ (9072326120367/20000000000000 : ℝ)^3443
        have hw : |(5437361287/10000000000 : ℝ)|=(5437361287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5215619033/10000000000 : ℝ)|^4467 ≤ (42976235573241/100000000000000 : ℝ)^3443
        have hw : |(5215619033/10000000000 : ℝ)|=(5215619033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s4_1 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338300779/2500000000 : ℝ)*x 0 + (-2022207569/10000000000 : ℝ)*x 1 + (1043123749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338300779/2500000000 : ℝ)^4467 ≤ (44452824406147/100000000000000 : ℝ)^3443 := by
    have hnat : (1338300779 : ℕ)^4467*100000000000000^3443 ≤ 44452824406147^3443*2500000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338300779 2500000000 44452824406147 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2022207569/10000000000 : ℝ)^4467 ≤ (12570943090223/100000000000000 : ℝ)^3443 := by
    have hnat : (2022207569 : ℕ)^4467*100000000000000^3443 ≤ 12570943090223^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2022207569 10000000000 12570943090223 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043123749/2000000000 : ℝ)^4467 ≤ (2686014530897/6250000000000 : ℝ)^3443 := by
    have hnat : (1043123749 : ℕ)^4467*6250000000000^3443 ≤ 2686014530897^3443*2000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043123749 2000000000 2686014530897 6250000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338300779/2500000000 : ℝ), (-2022207569/10000000000 : ℝ), (1043123749/2000000000 : ℝ)] ![(44452824406147/100000000000000 : ℝ), (12570943090223/100000000000000 : ℝ), (2686014530897/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338300779/2500000000 : ℝ)|^4467 ≤ (44452824406147/100000000000000 : ℝ)^3443
        have hw : |(1338300779/2500000000 : ℝ)|=(1338300779/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2022207569/10000000000 : ℝ)|^4467 ≤ (12570943090223/100000000000000 : ℝ)^3443
        have hw : |(-2022207569/10000000000 : ℝ)|=(2022207569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043123749/2000000000 : ℝ)|^4467 ≤ (2686014530897/6250000000000 : ℝ)^3443
        have hw : |(1043123749/2000000000 : ℝ)|=(1043123749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s4_2 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353203003/10000000000 : ℝ)*x 0 + (1043123811/2000000000 : ℝ)*x 1 + (-505551827/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353203003/10000000000 : ℝ)^4467 ≤ (555660289859/1250000000000 : ℝ)^3443 := by
    have hnat : (5353203003 : ℕ)^4467*1250000000000^3443 ≤ 555660289859^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353203003 10000000000 555660289859 1250000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043123811/2000000000 : ℝ)^4467 ≤ (42976235808433/100000000000000 : ℝ)^3443 := by
    have hnat : (1043123811 : ℕ)^4467*100000000000000^3443 ≤ 42976235808433^3443*2000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043123811 2000000000 42976235808433 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (505551827/2500000000 : ℝ)^4467 ≤ (12570940985177/100000000000000 : ℝ)^3443 := by
    have hnat : (505551827 : ℕ)^4467*100000000000000^3443 ≤ 12570940985177^3443*2500000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      505551827 2500000000 12570940985177 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353203003/10000000000 : ℝ), (1043123811/2000000000 : ℝ), (-505551827/2500000000 : ℝ)] ![(555660289859/1250000000000 : ℝ), (42976235808433/100000000000000 : ℝ), (12570940985177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353203003/10000000000 : ℝ)|^4467 ≤ (555660289859/1250000000000 : ℝ)^3443
        have hw : |(5353203003/10000000000 : ℝ)|=(5353203003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043123811/2000000000 : ℝ)|^4467 ≤ (42976235808433/100000000000000 : ℝ)^3443
        have hw : |(1043123811/2000000000 : ℝ)|=(1043123811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-505551827/2500000000 : ℝ)|^4467 ≤ (12570940985177/100000000000000 : ℝ)^3443
        have hw : |(-505551827/2500000000 : ℝ)|=(505551827/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s4_3 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (856491487/2000000000 : ℝ)*x 0 + (2020996007/5000000000 : ℝ)*x 1 + (17715857/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (856491487/2000000000 : ℝ)^4467 ≤ (16638839509403/50000000000000 : ℝ)^3443 := by
    have hnat : (856491487 : ℕ)^4467*50000000000000^3443 ≤ 16638839509403^3443*2000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      856491487 2000000000 16638839509403 50000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2020996007/5000000000 : ℝ)^4467 ≤ (7718466582101/25000000000000 : ℝ)^3443 := by
    have hnat : (2020996007 : ℕ)^4467*25000000000000^3443 ≤ 7718466582101^3443*5000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2020996007 5000000000 7718466582101 25000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17715857/39062500 : ℝ)^4467 ≤ (35848454642703/100000000000000 : ℝ)^3443 := by
    have hnat : (17715857 : ℕ)^4467*100000000000000^3443 ≤ 35848454642703^3443*39062500^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17715857 39062500 35848454642703 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(856491487/2000000000 : ℝ), (2020996007/5000000000 : ℝ), (17715857/39062500 : ℝ)] ![(16638839509403/50000000000000 : ℝ), (7718466582101/25000000000000 : ℝ), (35848454642703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(856491487/2000000000 : ℝ)|^4467 ≤ (16638839509403/50000000000000 : ℝ)^3443
        have hw : |(856491487/2000000000 : ℝ)|=(856491487/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2020996007/5000000000 : ℝ)|^4467 ≤ (7718466582101/25000000000000 : ℝ)^3443
        have hw : |(2020996007/5000000000 : ℝ)|=(2020996007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(17715857/39062500 : ℝ)|^4467 ≤ (35848454642703/100000000000000 : ℝ)^3443
        have hw : |(17715857/39062500 : ℝ)|=(17715857/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s4_4 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1908594589/10000000000 : ℝ)*x 0 + (5216760199/10000000000 : ℝ)*x 1 + (5436211523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1908594589/10000000000 : ℝ)^4467 ≤ (1457797262803/12500000000000 : ℝ)^3443 := by
    have hnat : (1908594589 : ℕ)^4467*12500000000000^3443 ≤ 1457797262803^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908594589 10000000000 1457797262803 12500000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216760199/10000000000 : ℝ)^4467 ≤ (42988435701411/100000000000000 : ℝ)^3443 := by
    have hnat : (5216760199 : ℕ)^4467*100000000000000^3443 ≤ 42988435701411^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216760199 10000000000 42988435701411 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436211523/10000000000 : ℝ)^4467 ≤ (2267459309399/5000000000000 : ℝ)^3443 := by
    have hnat : (5436211523 : ℕ)^4467*5000000000000^3443 ≤ 2267459309399^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436211523 10000000000 2267459309399 5000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1908594589/10000000000 : ℝ), (5216760199/10000000000 : ℝ), (5436211523/10000000000 : ℝ)] ![(1457797262803/12500000000000 : ℝ), (42988435701411/100000000000000 : ℝ), (2267459309399/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1908594589/10000000000 : ℝ)|^4467 ≤ (1457797262803/12500000000000 : ℝ)^3443
        have hw : |(-1908594589/10000000000 : ℝ)|=(1908594589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216760199/10000000000 : ℝ)|^4467 ≤ (42988435701411/100000000000000 : ℝ)^3443
        have hw : |(5216760199/10000000000 : ℝ)|=(5216760199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436211523/10000000000 : ℝ)|^4467 ≤ (2267459309399/5000000000000 : ℝ)^3443
        have hw : |(5436211523/10000000000 : ℝ)|=(5436211523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s4_5 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661905321/1250000000 : ℝ)*x 0 + (-450403777/2500000000 : ℝ)*x 1 + (2718105733/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661905321/1250000000 : ℝ)^4467 ≤ (684834113761/1562500000000 : ℝ)^3443 := by
    have hnat : (661905321 : ℕ)^4467*1562500000000^3443 ≤ 684834113761^3443*1250000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661905321 1250000000 684834113761 1562500000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (450403777/2500000000 : ℝ)^4467 ≤ (10821431129131/100000000000000 : ℝ)^3443 := by
    have hnat : (450403777 : ℕ)^4467*100000000000000^3443 ≤ 10821431129131^3443*2500000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450403777 2500000000 10821431129131 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2718105733/5000000000 : ℝ)^4467 ≤ (45349185571063/100000000000000 : ℝ)^3443 := by
    have hnat : (2718105733 : ℕ)^4467*100000000000000^3443 ≤ 45349185571063^3443*5000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2718105733 5000000000 45349185571063 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661905321/1250000000 : ℝ), (-450403777/2500000000 : ℝ), (2718105733/5000000000 : ℝ)] ![(684834113761/1562500000000 : ℝ), (10821431129131/100000000000000 : ℝ), (45349185571063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661905321/1250000000 : ℝ)|^4467 ≤ (684834113761/1562500000000 : ℝ)^3443
        have hw : |(661905321/1250000000 : ℝ)|=(661905321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-450403777/2500000000 : ℝ)|^4467 ≤ (10821431129131/100000000000000 : ℝ)^3443
        have hw : |(-450403777/2500000000 : ℝ)|=(450403777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2718105733/5000000000 : ℝ)|^4467 ≤ (45349185571063/100000000000000 : ℝ)^3443
        have hw : |(2718105733/5000000000 : ℝ)|=(2718105733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s4_6 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264762127/500000000 : ℝ)*x 0 + (5436211499/10000000000 : ℝ)*x 1 + (-1801615101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264762127/500000000 : ℝ)^4467 ≤ (2739336436251/6250000000000 : ℝ)^3443 := by
    have hnat : (264762127 : ℕ)^4467*6250000000000^3443 ≤ 2739336436251^3443*500000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264762127 500000000 2739336436251 6250000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436211499/10000000000 : ℝ)^4467 ≤ (22674592964113/50000000000000 : ℝ)^3443 := by
    have hnat : (5436211499 : ℕ)^4467*50000000000000^3443 ≤ 22674592964113^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436211499 10000000000 22674592964113 50000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1801615101/10000000000 : ℝ)^4467 ≤ (10821431074581/100000000000000 : ℝ)^3443 := by
    have hnat : (1801615101 : ℕ)^4467*100000000000000^3443 ≤ 10821431074581^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801615101 10000000000 10821431074581 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264762127/500000000 : ℝ), (5436211499/10000000000 : ℝ), (-1801615101/10000000000 : ℝ)] ![(2739336436251/6250000000000 : ℝ), (22674592964113/50000000000000 : ℝ), (10821431074581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264762127/500000000 : ℝ)|^4467 ≤ (2739336436251/6250000000000 : ℝ)^3443
        have hw : |(264762127/500000000 : ℝ)|=(264762127/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436211499/10000000000 : ℝ)|^4467 ≤ (22674592964113/50000000000000 : ℝ)^3443
        have hw : |(5436211499/10000000000 : ℝ)|=(5436211499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1801615101/10000000000 : ℝ)|^4467 ≤ (10821431074581/100000000000000 : ℝ)^3443
        have hw : |(-1801615101/10000000000 : ℝ)|=(1801615101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s4_7 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4282526077/10000000000 : ℝ)*x 0 + (4532720587/10000000000 : ℝ)*x 1 + (161781959/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282526077/10000000000 : ℝ)^4467 ≤ (16639185528343/50000000000000 : ℝ)^3443 := by
    have hnat : (4282526077 : ℕ)^4467*50000000000000^3443 ≤ 16639185528343^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282526077 10000000000 16639185528343 50000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4532720587/10000000000 : ℝ)^4467 ≤ (35822420671333/100000000000000 : ℝ)^3443 := by
    have hnat : (4532720587 : ℕ)^4467*100000000000000^3443 ≤ 35822420671333^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4532720587 10000000000 35822420671333 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (161781959/400000000 : ℝ)^4467 ≤ (30899208244533/100000000000000 : ℝ)^3443 := by
    have hnat : (161781959 : ℕ)^4467*100000000000000^3443 ≤ 30899208244533^3443*400000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161781959 400000000 30899208244533 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282526077/10000000000 : ℝ), (4532720587/10000000000 : ℝ), (161781959/400000000 : ℝ)] ![(16639185528343/50000000000000 : ℝ), (35822420671333/100000000000000 : ℝ), (30899208244533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282526077/10000000000 : ℝ)|^4467 ≤ (16639185528343/50000000000000 : ℝ)^3443
        have hw : |(4282526077/10000000000 : ℝ)|=(4282526077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4532720587/10000000000 : ℝ)|^4467 ≤ (35822420671333/100000000000000 : ℝ)^3443
        have hw : |(4532720587/10000000000 : ℝ)|=(4532720587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(161781959/400000000 : ℝ)|^4467 ≤ (30899208244533/100000000000000 : ℝ)^3443
        have hw : |(161781959/400000000 : ℝ)|=(161781959/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1485_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80612767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1557/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10721/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2699/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1557/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10721/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1557/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10721/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1557/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10721/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1557/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10721/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1557/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10721/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1557/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10721/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10721/100000 : ℝ) ^ (4465/1024 : ℝ) ≤ (1477151250213391/25000000000000000000 : ℝ) := by
    have hpowers : (10721/100000 : ℝ)^4465 ≤ (1477151250213391/25000000000000000000 : ℝ)^1024 := by
      have hnat : (10721 : ℕ)^4465*25000000000000000000^1024 ≤ 1477151250213391^1024*100000^4465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10721 100000 1477151250213391 25000000000000000000 4465 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10721/100000 : ℝ)) (X := (1477151250213391/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1557/10000 : ℝ) ^ (4465/1024 : ℝ) ≤ (30067297156378347/100000000000000000000 : ℝ) := by
    have hpowers : (1557/10000 : ℝ)^4465 ≤ (30067297156378347/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1557 : ℕ)^4465*100000000000000000000^1024 ≤ 30067297156378347^1024*10000^4465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1557 10000 30067297156378347 100000000000000000000 4465 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1557/10000 : ℝ)) (X := (30067297156378347/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501477151250213391/12500000000000000000 : ℝ) ≤ (10000271002733833/10000000000000000 : ℝ) ^ (4465/1024 : ℝ) := by
    have hpowers : (12501477151250213391/12500000000000000000 : ℝ)^1024 ≤ (10000271002733833/10000000000000000 : ℝ)^4465 := by
      have hnat : (12501477151250213391 : ℕ)^1024*10000000000000000^4465 ≤ 10000271002733833^4465*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501477151250213391 12500000000000000000 10000271002733833 10000000000000000 1024 4465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000271002733833/10000000000000000 : ℝ)) (X := (12501477151250213391/12500000000000000000 : ℝ)) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035975902157231911/100000000000000000000 : ℝ) ≤ (5000412477245269/5000000000000000 : ℝ) ^ (4465/1024 : ℝ) := by
    have hpowers : (100035975902157231911/100000000000000000000 : ℝ)^1024 ≤ (5000412477245269/5000000000000000 : ℝ)^4465 := by
      have hnat : (100035975902157231911 : ℕ)^1024*5000000000000000^4465 ≤ 5000412477245269^4465*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035975902157231911 100000000000000000000 5000412477245269 5000000000000000 1024 4465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000412477245269/5000000000000000 : ℝ)) (X := (100035975902157231911/100000000000000000000 : ℝ)) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030067297156378347/50000000000000000000 : ℝ) ≤ (10001378906247243/10000000000000000 : ℝ) ^ (4465/1024 : ℝ) := by
    have hpowers : (50030067297156378347/50000000000000000000 : ℝ)^1024 ≤ (10001378906247243/10000000000000000 : ℝ)^4465 := by
      have hnat : (50030067297156378347 : ℕ)^1024*10000000000000000^4465 ≤ 10001378906247243^4465*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030067297156378347 50000000000000000000 10001378906247243 10000000000000000 1024 4465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001378906247243/10000000000000000 : ℝ)) (X := (50030067297156378347/50000000000000000000 : ℝ)) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1477151250213391/25000000000000000000 : ℝ) ≤ ((48479436258689087607/48490000000000000000 : ℝ)+2*(110790351341/96980000000000 : ℝ)*(10721/100000 : ℝ))^(4465/1024 : ℝ) := by
    rw [show (48479436258689087607/48490000000000000000 : ℝ)+2*(110790351341/96980000000000 : ℝ)*(10721/100000 : ℝ)=(10000271002733833/10000000000000000 : ℝ) by norm_num, show 1+2*(1477151250213391/25000000000000000000 : ℝ)=(12501477151250213391/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30067297156378347/100000000000000000000 : ℝ)+(1477151250213391/25000000000000000000 : ℝ) ≤ ((48479436258689087607/48490000000000000000 : ℝ)+(110790351341/96980000000000 : ℝ)*((1557/10000 : ℝ)+(10721/100000 : ℝ)))^(4465/1024 : ℝ) := by
    rw [show (48479436258689087607/48490000000000000000 : ℝ)+(110790351341/96980000000000 : ℝ)*((1557/10000 : ℝ)+(10721/100000 : ℝ))=(5000412477245269/5000000000000000 : ℝ) by norm_num, show 1+(30067297156378347/100000000000000000000 : ℝ)+(1477151250213391/25000000000000000000 : ℝ)=(100035975902157231911/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30067297156378347/100000000000000000000 : ℝ) ≤ ((48479436258689087607/48490000000000000000 : ℝ)+2*(110790351341/96980000000000 : ℝ)*(1557/10000 : ℝ))^(4465/1024 : ℝ) := by
    rw [show (48479436258689087607/48490000000000000000 : ℝ)+2*(110790351341/96980000000000 : ℝ)*(1557/10000 : ℝ)=(10001378906247243/10000000000000000 : ℝ) by norm_num, show 1+2*(30067297156378347/100000000000000000000 : ℝ)=(50030067297156378347/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (48479436258689087607/48490000000000000000 : ℝ)*(X 1 0+X 2 0)+(110790351341/96980000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4465/1024 : ℝ)) (lo := (10721/100000 : ℝ)) (hi := (1557/10000 : ℝ)) (c := (48479436258689087607/48490000000000000000 : ℝ)) (alpha := (110790351341/96980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (48479436258689087607/48490000000000000000 : ℝ)*(X 0 1+X 2 1)+(110790351341/96980000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4465/1024 : ℝ)) (lo := (10721/100000 : ℝ)) (hi := (1557/10000 : ℝ)) (c := (48479436258689087607/48490000000000000000 : ℝ)) (alpha := (110790351341/96980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (48479436258689087607/48490000000000000000 : ℝ)*(X 0 2+X 1 2)+(110790351341/96980000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4465/1024 : ℝ)) (lo := (10721/100000 : ℝ)) (hi := (1557/10000 : ℝ)) (c := (48479436258689087607/48490000000000000000 : ℝ)) (alpha := (110790351341/96980000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-954281887/5000000000 : ℝ)*X 0 0+(5437361287/10000000000 : ℝ)*X 0 1+(5215619033/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338300779/2500000000 : ℝ)*X 1 0+(-2022207569/10000000000 : ℝ)*X 1 1+(1043123749/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353203003/10000000000 : ℝ)*X 2 0+(1043123811/2000000000 : ℝ)*X 2 1+(-505551827/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((856491487/2000000000 : ℝ)*X 0 0+(2020996007/5000000000 : ℝ)*X 0 1+(17715857/39062500 : ℝ)*X 0 2+(856491487/2000000000 : ℝ)*X 1 0+(2020996007/5000000000 : ℝ)*X 1 1+(17715857/39062500 : ℝ)*X 1 2+(856491487/2000000000 : ℝ)*X 2 0+(2020996007/5000000000 : ℝ)*X 2 1+(17715857/39062500 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1908594589/10000000000 : ℝ)*X 0 0+(5216760199/10000000000 : ℝ)*X 0 1+(5436211523/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661905321/1250000000 : ℝ)*X 1 0+(-450403777/2500000000 : ℝ)*X 1 1+(2718105733/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264762127/500000000 : ℝ)*X 2 0+(5436211499/10000000000 : ℝ)*X 2 1+(-1801615101/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4282526077/10000000000 : ℝ)*X 0 0+(4532720587/10000000000 : ℝ)*X 0 1+(161781959/400000000 : ℝ)*X 0 2+(4282526077/10000000000 : ℝ)*X 1 0+(4532720587/10000000000 : ℝ)*X 1 1+(161781959/400000000 : ℝ)*X 1 2+(4282526077/10000000000 : ℝ)*X 2 0+(4532720587/10000000000 : ℝ)*X 2 1+(161781959/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5327515852109697729584857611/1212250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (397419639/50000000000000 : ℝ)*(base19) + (21557071/3125000000000 : ℝ)*(base23) + (3328471/12500000000000 : ℝ)*(lower2) + (29346651/100000000000000 : ℝ)*(lower3) + (1634270472979003/50000000000000 : ℝ)*(major0) + (1634270472979003/50000000000000 : ℝ)*(major1) + (1634270472979003/50000000000000 : ℝ)*(major2) + (450975564146139/10000000000000 : ℝ)*(sp0) + (2254883764114343/50000000000000 : ℝ)*(sp1) + (180390852827163/4000000000000 : ℝ)*(sp2) + (2027304013583299/100000000000000 : ℝ)*(sp3) + (4092260989/25000000000000 : ℝ)*(sp4) + (3687437383/100000000000000 : ℝ)*(sp5) + (5721336237/100000000000000 : ℝ)*(sp7) + (126706858432471/6250000000000 : ℝ)*(f.failure) + (4509772010505347/100000000000000 : ℝ)*(f.sum) + (8647930754521/1212250000000000000000000000 : ℝ)*base66 + (23520123094014515821/2424500000000000000000000000000000 : ℝ)*base67 + (32374540958995515821/2424500000000000000000000000000000 : ℝ)*base69 + (12707740570117015821/2424500000000000000000000000000000 : ℝ)*base71 + (1589632420703/4849000000000000000000000000 : ℝ)*base73 + (34191432916590515821/2424500000000000000000000000000000 : ℝ)*base75 + (5101218269044515821/2424500000000000000000000000000000 : ℝ)*base77 + (24305035691815015821/2424500000000000000000000000000000 : ℝ)*base79 + (7926099169679/4849000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1207257/312500000000000000000 : ℝ)*base89 + (1207257/312500000000000000000 : ℝ)*base91 + (1207257/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144388150849323964437100581/23312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1072804273/100000000000000 : ℝ)*(base19) + (291731213/25000000000000 : ℝ)*(base23) + (59186983/50000000000000 : ℝ)*(upper3) + (57264693/100000000000000 : ℝ)*(lower4) + (77783117/50000000000000 : ℝ)*(upper5) + (412829909164569/12500000000000 : ℝ)*(major0) + (412829909164569/12500000000000 : ℝ)*(major1) + (412829909164569/12500000000000 : ℝ)*(major2) + (15651348307/100000000000000 : ℝ)*(sp1) + (8285786133/50000000000000 : ℝ)*(sp2) + (2278409573394543/50000000000000 : ℝ)*(sp4) + (911360484527301/20000000000000 : ℝ)*(sp5) + (4556801408291967/100000000000000 : ℝ)*(sp6) + (256057399173861/12500000000000 : ℝ)*(sp7) + (256057399173861/12500000000000 : ℝ)*(f.failure) + (2278409573394543/50000000000000 : ℝ)*(f.sum) + (103617806721/186500000000000000000000000 : ℝ)*base66 + (411970297507280491/46625000000000000000000000000000 : ℝ)*base67 + (327127791734280491/46625000000000000000000000000000 : ℝ)*base69 + (467526015153030491/46625000000000000000000000000000 : ℝ)*base71 + (388667400089/74600000000000000000000000 : ℝ)*base74 + (1577584971235405491/46625000000000000000000000000000 : ℝ)*base75 + (165353049003280491/46625000000000000000000000000000 : ℝ)*base77 + (210481803097655491/46625000000000000000000000000000 : ℝ)*base79 + (7641628601/373000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (716613/625000000000000000000 : ℝ)*base90 + (716613/625000000000000000000 : ℝ)*base92 + (716613/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1485_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80612767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1557/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10721/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2699/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1485_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1485_s5_0 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1908643729/10000000000 : ℝ)*x 0 + (5436836939/10000000000 : ℝ)*x 1 + (5216090609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1908643729/10000000000 : ℝ)^4467 ≤ (2332553535143/20000000000000 : ℝ)^3443 := by
    have hnat : (1908643729 : ℕ)^4467*20000000000000^3443 ≤ 2332553535143^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908643729 10000000000 2332553535143 20000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436836939/10000000000 : ℝ)^4467 ≤ (45355955250077/100000000000000 : ℝ)^3443 := by
    have hnat : (5436836939 : ℕ)^4467*100000000000000^3443 ≤ 45355955250077^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436836939 10000000000 45355955250077 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216090609/10000000000 : ℝ)^4467 ≤ (1719251082559/4000000000000 : ℝ)^3443 := by
    have hnat : (5216090609 : ℕ)^4467*4000000000000^3443 ≤ 1719251082559^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216090609 10000000000 1719251082559 4000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1908643729/10000000000 : ℝ), (5436836939/10000000000 : ℝ), (5216090609/10000000000 : ℝ)] ![(2332553535143/20000000000000 : ℝ), (45355955250077/100000000000000 : ℝ), (1719251082559/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1908643729/10000000000 : ℝ)|^4467 ≤ (2332553535143/20000000000000 : ℝ)^3443
        have hw : |(-1908643729/10000000000 : ℝ)|=(1908643729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436836939/10000000000 : ℝ)|^4467 ≤ (45355955250077/100000000000000 : ℝ)^3443
        have hw : |(5436836939/10000000000 : ℝ)|=(5436836939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216090609/10000000000 : ℝ)|^4467 ≤ (1719251082559/4000000000000 : ℝ)^3443
        have hw : |(5216090609/10000000000 : ℝ)|=(5216090609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s5_1 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338266623/2500000000 : ℝ)*x 0 + (-202176461/1000000000 : ℝ)*x 1 + (2608045297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338266623/2500000000 : ℝ)^4467 ≤ (44451352466797/100000000000000 : ℝ)^3443 := by
    have hnat : (1338266623 : ℕ)^4467*100000000000000^3443 ≤ 44451352466797^3443*2500000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338266623 2500000000 44451352466797 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (202176461/1000000000 : ℝ)^4467 ≤ (12567370605001/100000000000000 : ℝ)^3443 := by
    have hnat : (202176461 : ℕ)^4467*100000000000000^3443 ≤ 12567370605001^3443*1000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202176461 1000000000 12567370605001 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608045297/5000000000 : ℝ)^4467 ≤ (10745319225903/25000000000000 : ℝ)^3443 := by
    have hnat : (2608045297 : ℕ)^4467*25000000000000^3443 ≤ 10745319225903^3443*5000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608045297 5000000000 10745319225903 25000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338266623/2500000000 : ℝ), (-202176461/1000000000 : ℝ), (2608045297/5000000000 : ℝ)] ![(44451352466797/100000000000000 : ℝ), (12567370605001/100000000000000 : ℝ), (10745319225903/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338266623/2500000000 : ℝ)|^4467 ≤ (44451352466797/100000000000000 : ℝ)^3443
        have hw : |(1338266623/2500000000 : ℝ)|=(1338266623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-202176461/1000000000 : ℝ)|^4467 ≤ (12567370605001/100000000000000 : ℝ)^3443
        have hw : |(-202176461/1000000000 : ℝ)|=(202176461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608045297/5000000000 : ℝ)|^4467 ≤ (10745319225903/25000000000000 : ℝ)^3443
        have hw : |(2608045297/5000000000 : ℝ)|=(2608045297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s5_2 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353066491/10000000000 : ℝ)*x 0 + (2608045303/5000000000 : ℝ)*x 1 + (-2021764597/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353066491/10000000000 : ℝ)^4467 ≤ (44451352456023/100000000000000 : ℝ)^3443 := by
    have hnat : (5353066491 : ℕ)^4467*100000000000000^3443 ≤ 44451352456023^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353066491 10000000000 44451352456023 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608045303/5000000000 : ℝ)^4467 ≤ (42981277031903/100000000000000 : ℝ)^3443 := by
    have hnat : (2608045303 : ℕ)^4467*100000000000000^3443 ≤ 42981277031903^3443*5000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608045303 5000000000 42981277031903 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2021764597/10000000000 : ℝ)^4467 ≤ (12567370500159/100000000000000 : ℝ)^3443 := by
    have hnat : (2021764597 : ℕ)^4467*100000000000000^3443 ≤ 12567370500159^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2021764597 10000000000 12567370500159 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353066491/10000000000 : ℝ), (2608045303/5000000000 : ℝ), (-2021764597/10000000000 : ℝ)] ![(44451352456023/100000000000000 : ℝ), (42981277031903/100000000000000 : ℝ), (12567370500159/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353066491/10000000000 : ℝ)|^4467 ≤ (44451352456023/100000000000000 : ℝ)^3443
        have hw : |(5353066491/10000000000 : ℝ)|=(5353066491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608045303/5000000000 : ℝ)|^4467 ≤ (42981277031903/100000000000000 : ℝ)^3443
        have hw : |(2608045303/5000000000 : ℝ)|=(2608045303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2021764597/10000000000 : ℝ)|^4467 ≤ (12567370500159/100000000000000 : ℝ)^3443
        have hw : |(-2021764597/10000000000 : ℝ)|=(2021764597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s5_3 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4282507303/10000000000 : ℝ)*x 0 + (4043093433/10000000000 : ℝ)*x 1 + (566768243/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4282507303/10000000000 : ℝ)^4467 ≤ (16639090889917/50000000000000 : ℝ)^3443 := by
    have hnat : (4282507303 : ℕ)^4467*50000000000000^3443 ≤ 16639090889917^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4282507303 10000000000 16639090889917 50000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4043093433/10000000000 : ℝ)^4467 ≤ (30884781854169/100000000000000 : ℝ)^3443 := by
    have hnat : (4043093433 : ℕ)^4467*100000000000000^3443 ≤ 30884781854169^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4043093433 10000000000 30884781854169 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566768243/1250000000 : ℝ)^4467 ≤ (35837036346107/100000000000000 : ℝ)^3443 := by
    have hnat : (566768243 : ℕ)^4467*100000000000000^3443 ≤ 35837036346107^3443*1250000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566768243 1250000000 35837036346107 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4282507303/10000000000 : ℝ), (4043093433/10000000000 : ℝ), (566768243/1250000000 : ℝ)] ![(16639090889917/50000000000000 : ℝ), (30884781854169/100000000000000 : ℝ), (35837036346107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4282507303/10000000000 : ℝ)|^4467 ≤ (16639090889917/50000000000000 : ℝ)^3443
        have hw : |(4282507303/10000000000 : ℝ)|=(4282507303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4043093433/10000000000 : ℝ)|^4467 ≤ (30884781854169/100000000000000 : ℝ)^3443
        have hw : |(4043093433/10000000000 : ℝ)|=(4043093433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(566768243/1250000000 : ℝ)|^4467 ≤ (35837036346107/100000000000000 : ℝ)^3443
        have hw : |(566768243/1250000000 : ℝ)|=(566768243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s5_4 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1908673931/10000000000 : ℝ)*x 0 + (5217221599/10000000000 : ℝ)*x 1 + (1358924403/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1908673931/10000000000 : ℝ)^4467 ≤ (2915751778337/25000000000000 : ℝ)^3443 := by
    have hnat : (1908673931 : ℕ)^4467*25000000000000^3443 ≤ 2915751778337^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1908673931 10000000000 2915751778337 25000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217221599/10000000000 : ℝ)^4467 ≤ (42993368722817/100000000000000 : ℝ)^3443 := by
    have hnat : (5217221599 : ℕ)^4467*100000000000000^3443 ≤ 42993368722817^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217221599 10000000000 42993368722817 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358924403/2500000000 : ℝ)^4467 ≤ (45343624150783/100000000000000 : ℝ)^3443 := by
    have hnat : (1358924403 : ℕ)^4467*100000000000000^3443 ≤ 45343624150783^3443*2500000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358924403 2500000000 45343624150783 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1908673931/10000000000 : ℝ), (5217221599/10000000000 : ℝ), (1358924403/2500000000 : ℝ)] ![(2915751778337/25000000000000 : ℝ), (42993368722817/100000000000000 : ℝ), (45343624150783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1908673931/10000000000 : ℝ)|^4467 ≤ (2915751778337/25000000000000 : ℝ)^3443
        have hw : |(-1908673931/10000000000 : ℝ)|=(1908673931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217221599/10000000000 : ℝ)|^4467 ≤ (42993368722817/100000000000000 : ℝ)^3443
        have hw : |(5217221599/10000000000 : ℝ)|=(5217221599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358924403/2500000000 : ℝ)|^4467 ≤ (45343624150783/100000000000000 : ℝ)^3443
        have hw : |(1358924403/2500000000 : ℝ)|=(1358924403/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s5_5 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295366749/10000000000 : ℝ)*x 0 + (-901078801/5000000000 : ℝ)*x 1 + (339731101/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295366749/10000000000 : ℝ)^4467 ≤ (8766143369699/20000000000000 : ℝ)^3443 := by
    have hnat : (5295366749 : ℕ)^4467*20000000000000^3443 ≤ 8766143369699^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295366749 10000000000 8766143369699 20000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (901078801/5000000000 : ℝ)^4467 ≤ (270641473609/2500000000000 : ℝ)^3443 := by
    have hnat : (901078801 : ℕ)^4467*2500000000000^3443 ≤ 270641473609^3443*5000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901078801 5000000000 270641473609 2500000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339731101/625000000 : ℝ)^4467 ≤ (22671812097037/50000000000000 : ℝ)^3443 := by
    have hnat : (339731101 : ℕ)^4467*50000000000000^3443 ≤ 22671812097037^3443*625000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339731101 625000000 22671812097037 50000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295366749/10000000000 : ℝ), (-901078801/5000000000 : ℝ), (339731101/625000000 : ℝ)] ![(8766143369699/20000000000000 : ℝ), (270641473609/2500000000000 : ℝ), (22671812097037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295366749/10000000000 : ℝ)|^4467 ≤ (8766143369699/20000000000000 : ℝ)^3443
        have hw : |(5295366749/10000000000 : ℝ)|=(5295366749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-901078801/5000000000 : ℝ)|^4467 ≤ (270641473609/2500000000000 : ℝ)^3443
        have hw : |(-901078801/5000000000 : ℝ)|=(901078801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339731101/625000000 : ℝ)|^4467 ≤ (22671812097037/50000000000000 : ℝ)^3443
        have hw : |(339731101/625000000 : ℝ)|=(339731101/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s5_6 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165480211/312500000 : ℝ)*x 0 + (5435697613/10000000000 : ℝ)*x 1 + (-901078801/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165480211/312500000 : ℝ)^4467 ≤ (5478839610089/12500000000000 : ℝ)^3443 := by
    have hnat : (165480211 : ℕ)^4467*12500000000000^3443 ≤ 5478839610089^3443*312500000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165480211 312500000 5478839610089 12500000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5435697613/10000000000 : ℝ)^4467 ≤ (22671812080803/50000000000000 : ℝ)^3443 := by
    have hnat : (5435697613 : ℕ)^4467*50000000000000^3443 ≤ 22671812080803^3443*10000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5435697613 10000000000 22671812080803 50000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901078801/5000000000 : ℝ)^4467 ≤ (270641473609/2500000000000 : ℝ)^3443 := by
    have hnat : (901078801 : ℕ)^4467*2500000000000^3443 ≤ 270641473609^3443*5000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901078801 5000000000 270641473609 2500000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165480211/312500000 : ℝ), (5435697613/10000000000 : ℝ), (-901078801/5000000000 : ℝ)] ![(5478839610089/12500000000000 : ℝ), (22671812080803/50000000000000 : ℝ), (270641473609/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165480211/312500000 : ℝ)|^4467 ≤ (5478839610089/12500000000000 : ℝ)^3443
        have hw : |(165480211/312500000 : ℝ)|=(165480211/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5435697613/10000000000 : ℝ)|^4467 ≤ (22671812080803/50000000000000 : ℝ)^3443
        have hw : |(5435697613/10000000000 : ℝ)|=(5435697613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-901078801/5000000000 : ℝ)|^4467 ≤ (270641473609/2500000000000 : ℝ)^3443
        have hw : |(-901078801/5000000000 : ℝ)|=(901078801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1485_s5_7 (p : ℝ) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535321813/1250000000 : ℝ)*x 0 + (2265815011/5000000000 : ℝ)*x 1 + (809125559/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535321813/1250000000 : ℝ)^4467 ≤ (33278859292091/100000000000000 : ℝ)^3443 := by
    have hnat : (535321813 : ℕ)^4467*100000000000000^3443 ≤ 33278859292091^3443*1250000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535321813 1250000000 33278859292091 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265815011/5000000000 : ℝ)^4467 ≤ (17905619445879/50000000000000 : ℝ)^3443 := by
    have hnat : (2265815011 : ℕ)^4467*50000000000000^3443 ≤ 17905619445879^3443*5000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265815011 5000000000 17905619445879 50000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (809125559/2000000000 : ℝ)^4467 ≤ (30909901806653/100000000000000 : ℝ)^3443 := by
    have hnat : (809125559 : ℕ)^4467*100000000000000^3443 ≤ 30909901806653^3443*2000000000^4467 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      809125559 2000000000 30909901806653 100000000000000 4467 3443 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4467/1024 : ℝ)) 4467 3443 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535321813/1250000000 : ℝ), (2265815011/5000000000 : ℝ), (809125559/2000000000 : ℝ)] ![(33278859292091/100000000000000 : ℝ), (17905619445879/50000000000000 : ℝ), (30909901806653/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535321813/1250000000 : ℝ)|^4467 ≤ (33278859292091/100000000000000 : ℝ)^3443
        have hw : |(535321813/1250000000 : ℝ)|=(535321813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2265815011/5000000000 : ℝ)|^4467 ≤ (17905619445879/50000000000000 : ℝ)^3443
        have hw : |(2265815011/5000000000 : ℝ)|=(2265815011/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(809125559/2000000000 : ℝ)|^4467 ≤ (30909901806653/100000000000000 : ℝ)^3443
        have hw : |(809125559/2000000000 : ℝ)|=(809125559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1485_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80612767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2699/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5403/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7739/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2699/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2699/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2699/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2699/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2699/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have hpowlo : (2699/25000 : ℝ) ^ (4465/1024 : ℝ) ≤ (1522741833359433/25000000000000000000 : ℝ) := by
    have hpowers : (2699/25000 : ℝ)^4465 ≤ (1522741833359433/25000000000000000000 : ℝ)^1024 := by
      have hnat : (2699 : ℕ)^4465*25000000000000000000^1024 ≤ 1522741833359433^1024*25000^4465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2699 25000 1522741833359433 25000000000000000000 4465 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2699/25000 : ℝ)) (X := (1522741833359433/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4465/1024 : ℝ) ≤ (7347797636943977/25000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4465 ≤ (7347797636943977/25000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4465*25000000000000000000^1024 ≤ 7347797636943977^1024*100000^4465 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 7347797636943977 25000000000000000000 4465 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (7347797636943977/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501522741833359433/12500000000000000000 : ℝ) ≤ (5000139683265271/5000000000000000 : ℝ) ^ (4465/1024 : ℝ) := by
    have hpowers : (12501522741833359433/12500000000000000000 : ℝ)^1024 ≤ (5000139683265271/5000000000000000 : ℝ)^4465 := by
      have hnat : (12501522741833359433 : ℕ)^1024*5000000000000000^4465 ≤ 5000139683265271^4465*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501522741833359433 12500000000000000000 5000139683265271 5000000000000000 1024 4465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000139683265271/5000000000000000 : ℝ)) (X := (12501522741833359433/12500000000000000000 : ℝ)) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (2500887053947030341/2500000000000000000 : ℝ) ≤ (5000406817055263/5000000000000000 : ℝ) ^ (4465/1024 : ℝ) := by
    have hpowers : (2500887053947030341/2500000000000000000 : ℝ)^1024 ≤ (5000406817055263/5000000000000000 : ℝ)^4465 := by
      have hnat : (2500887053947030341 : ℕ)^1024*5000000000000000^4465 ≤ 5000406817055263^4465*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500887053947030341 2500000000000000000 5000406817055263 5000000000000000 1024 4465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000406817055263/5000000000000000 : ℝ)) (X := (2500887053947030341/2500000000000000000 : ℝ)) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507347797636943977/12500000000000000000 : ℝ) ≤ (1000134790169051/1000000000000000 : ℝ) ^ (4465/1024 : ℝ) := by
    have hpowers : (12507347797636943977/12500000000000000000 : ℝ)^1024 ≤ (1000134790169051/1000000000000000 : ℝ)^4465 := by
      have hnat : (12507347797636943977 : ℕ)^1024*1000000000000000^4465 ≤ 1000134790169051^4465*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507347797636943977 12500000000000000000 1000134790169051 1000000000000000 1024 4465 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000134790169051/1000000000000000 : ℝ)) (X := (12507347797636943977/12500000000000000000 : ℝ)) (by norm_num) 4465 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1522741833359433/25000000000000000000 : ℝ) ≤ ((23459887580770409539/23465000000000000000 : ℝ)+2*(33391723749/29331250000000 : ℝ)*(2699/25000 : ℝ))^(4465/1024 : ℝ) := by
    rw [show (23459887580770409539/23465000000000000000 : ℝ)+2*(33391723749/29331250000000 : ℝ)*(2699/25000 : ℝ)=(5000139683265271/5000000000000000 : ℝ) by norm_num, show 1+2*(1522741833359433/25000000000000000000 : ℝ)=(12501522741833359433/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7347797636943977/25000000000000000000 : ℝ)+(1522741833359433/25000000000000000000 : ℝ) ≤ ((23459887580770409539/23465000000000000000 : ℝ)+(33391723749/29331250000000 : ℝ)*((15489/100000 : ℝ)+(2699/25000 : ℝ)))^(4465/1024 : ℝ) := by
    rw [show (23459887580770409539/23465000000000000000 : ℝ)+(33391723749/29331250000000 : ℝ)*((15489/100000 : ℝ)+(2699/25000 : ℝ))=(5000406817055263/5000000000000000 : ℝ) by norm_num, show 1+(7347797636943977/25000000000000000000 : ℝ)+(1522741833359433/25000000000000000000 : ℝ)=(2500887053947030341/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7347797636943977/25000000000000000000 : ℝ) ≤ ((23459887580770409539/23465000000000000000 : ℝ)+2*(33391723749/29331250000000 : ℝ)*(15489/100000 : ℝ))^(4465/1024 : ℝ) := by
    rw [show (23459887580770409539/23465000000000000000 : ℝ)+2*(33391723749/29331250000000 : ℝ)*(15489/100000 : ℝ)=(1000134790169051/1000000000000000 : ℝ) by norm_num, show 1+2*(7347797636943977/25000000000000000000 : ℝ)=(12507347797636943977/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23459887580770409539/23465000000000000000 : ℝ)*(X 1 0+X 2 0)+(33391723749/29331250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4465/1024 : ℝ)) (lo := (2699/25000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (23459887580770409539/23465000000000000000 : ℝ)) (alpha := (33391723749/29331250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23459887580770409539/23465000000000000000 : ℝ)*(X 0 1+X 2 1)+(33391723749/29331250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4465/1024 : ℝ)) (lo := (2699/25000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (23459887580770409539/23465000000000000000 : ℝ)) (alpha := (33391723749/29331250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23459887580770409539/23465000000000000000 : ℝ)*(X 0 2+X 1 2)+(33391723749/29331250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4465/1024 : ℝ)) (lo := (2699/25000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (23459887580770409539/23465000000000000000 : ℝ)) (alpha := (33391723749/29331250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1908643729/10000000000 : ℝ)*X 0 0+(5436836939/10000000000 : ℝ)*X 0 1+(5216090609/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338266623/2500000000 : ℝ)*X 1 0+(-202176461/1000000000 : ℝ)*X 1 1+(2608045297/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353066491/10000000000 : ℝ)*X 2 0+(2608045303/5000000000 : ℝ)*X 2 1+(-2021764597/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4282507303/10000000000 : ℝ)*X 0 0+(4043093433/10000000000 : ℝ)*X 0 1+(566768243/1250000000 : ℝ)*X 0 2+(4282507303/10000000000 : ℝ)*X 1 0+(4043093433/10000000000 : ℝ)*X 1 1+(566768243/1250000000 : ℝ)*X 1 2+(4282507303/10000000000 : ℝ)*X 2 0+(4043093433/10000000000 : ℝ)*X 2 1+(566768243/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1908673931/10000000000 : ℝ)*X 0 0+(5217221599/10000000000 : ℝ)*X 0 1+(1358924403/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295366749/10000000000 : ℝ)*X 1 0+(-901078801/5000000000 : ℝ)*X 1 1+(339731101/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165480211/312500000 : ℝ)*X 2 0+(5435697613/10000000000 : ℝ)*X 2 1+(-901078801/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((535321813/1250000000 : ℝ)*X 0 0+(2265815011/5000000000 : ℝ)*X 0 1+(809125559/2000000000 : ℝ)*X 0 2+(535321813/1250000000 : ℝ)*X 1 0+(2265815011/5000000000 : ℝ)*X 1 1+(809125559/2000000000 : ℝ)*X 1 2+(535321813/1250000000 : ℝ)*X 2 0+(2265815011/5000000000 : ℝ)*X 2 1+(809125559/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1485_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3141530111215953955963088973/586625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (462744649/50000000000000 : ℝ)*(base19) + (867461607/100000000000000 : ℝ)*(base23) + (15304799/50000000000000 : ℝ)*(lower2) + (113375439/100000000000000 : ℝ)*(upper3) + (83956957/100000000000000 : ℝ)*(upper5) + (1641642893748269/50000000000000 : ℝ)*(major0) + (1641642893748269/50000000000000 : ℝ)*(major1) + (1641642893748269/50000000000000 : ℝ)*(major2) + (453010149742923/10000000000000 : ℝ)*(sp0) + (2265057630341473/50000000000000 : ℝ)*(sp1) + (4530115318710637/100000000000000 : ℝ)*(sp2) + (2036448373109941/100000000000000 : ℝ)*(sp3) + (7344371507/50000000000000 : ℝ)*(sp4) + (6837202179/100000000000000 : ℝ)*(sp7) + (50911380257803/2500000000000 : ℝ)*(f.failure) + (1132529046543061/25000000000000 : ℝ)*(f.sum) + (95705959855117/23465000000000000000000000000 : ℝ)*base65 + (2208800187380612009/1173250000000000000000000000000000 : ℝ)*base68 + (6263501151005612009/1173250000000000000000000000000000 : ℝ)*base70 + (10750021498288612009/1173250000000000000000000000000000 : ℝ)*base72 + (90099756118477/23465000000000000000000000000 : ℝ)*base73 + (869593358944887991/1173250000000000000000000000000000 : ℝ)*base75 + (2515589058077362009/1173250000000000000000000000000000 : ℝ)*base78 + (16933372311984887991/1173250000000000000000000000000000 : ℝ)*base79 + (292017878853/366640625000000000000000000 : ℝ)*base81 + (670901/125000000000000000000 : ℝ)*base89 + (670901/125000000000000000000 : ℝ)*base91 + (670901/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6529797256735514491489797021/1173250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (922744481/100000000000000 : ℝ)*(base19) + (200714393/20000000000000 : ℝ)*(base23) + (115888317/100000000000000 : ℝ)*(upper3) + (35270331/100000000000000 : ℝ)*(lower4) + (115184547/100000000000000 : ℝ)*(upper5) + (3317382346774987/100000000000000 : ℝ)*(major0) + (3317382346774987/100000000000000 : ℝ)*(major1) + (3317382346774987/100000000000000 : ℝ)*(major2) + (699228623/5000000000000 : ℝ)*(sp1) + (94073499/625000000000 : ℝ)*(sp2) + (4577160935897889/100000000000000 : ℝ)*(sp4) + (4577146028580947/100000000000000 : ℝ)*(sp5) + (1144286220141521/25000000000000 : ℝ)*(sp6) + (2057603572133299/100000000000000 : ℝ)*(sp7) + (2057603572133299/100000000000000 : ℝ)*(f.failure) + (4577160935897889/100000000000000 : ℝ)*(f.sum) + (19167977112997/23465000000000000000000000000 : ℝ)*base66 + (3343632815456699007/2346500000000000000000000000000000 : ℝ)*base68 + (2427511543962699007/2346500000000000000000000000000000 : ℝ)*base70 + (8212308945348300993/2346500000000000000000000000000000 : ℝ)*base71 + (24987591465713/5866250000000000000000000000 : ℝ)*base74 + (18983778803471300993/2346500000000000000000000000000000 : ℝ)*base75 + (5243472597045800993/2346500000000000000000000000000000 : ℝ)*base77 + (3390080641266800993/2346500000000000000000000000000000 : ℝ)*base79 + (72286540793703/23465000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (24771667/5000000000000000000000 : ℝ)*base90 + (24771667/5000000000000000000000 : ℝ)*base92 + (24771667/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1485_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80612767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2699/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5403/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1485_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1485_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80612767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4027/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5403/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1485_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1485_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1485_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4465/1024 : ℝ) ≤ p) (hpb : p ≤ (4467/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (80612767/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4027/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10227/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5403/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7739/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1485_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
