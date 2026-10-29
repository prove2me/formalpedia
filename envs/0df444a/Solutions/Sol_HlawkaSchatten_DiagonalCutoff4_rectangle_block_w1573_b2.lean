-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1573_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:28:30.083986+00:00
-- url     : https://prove2.me/submissions/52435304-0804-4213-b92c-81c4e7b74026

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
theorem support_rectangle_w1573_s6_0 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (267400151/500000000 : ℝ)*x 0 + (1044034029/2000000000 : ℝ)*x 1 + (-471628623/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267400151/500000000 : ℝ)^4643 ≤ (22400266081227/50000000000000 : ℝ)^3619 := by
    have hnat : (267400151 : ℕ)^4643*50000000000000^3619 ≤ 22400266081227^3619*500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267400151 500000000 22400266081227 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044034029/2000000000 : ℝ)^4643 ≤ (43431339553323/100000000000000 : ℝ)^3619 := by
    have hnat : (1044034029 : ℕ)^4643*100000000000000^3619 ≤ 43431339553323^3619*2000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044034029 2000000000 43431339553323 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (471628623/2500000000 : ℝ)^4643 ≤ (11768128268519/100000000000000 : ℝ)^3619 := by
    have hnat : (471628623 : ℕ)^4643*100000000000000^3619 ≤ 11768128268519^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      471628623 2500000000 11768128268519 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267400151/500000000 : ℝ), (1044034029/2000000000 : ℝ), (-471628623/2500000000 : ℝ)] ![(22400266081227/50000000000000 : ℝ), (43431339553323/100000000000000 : ℝ), (11768128268519/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267400151/500000000 : ℝ)|^4643 ≤ (22400266081227/50000000000000 : ℝ)^3619
        have hw : |(267400151/500000000 : ℝ)|=(267400151/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044034029/2000000000 : ℝ)|^4643 ≤ (43431339553323/100000000000000 : ℝ)^3619
        have hw : |(1044034029/2000000000 : ℝ)|=(1044034029/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-471628623/2500000000 : ℝ)|^4643 ≤ (11768128268519/100000000000000 : ℝ)^3619
        have hw : |(-471628623/2500000000 : ℝ)|=(471628623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s6_1 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1781550451/10000000000 : ℝ)*x 0 + (5221237547/10000000000 : ℝ)*x 1 + (5424327751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1781550451/10000000000 : ℝ)^4643 ≤ (10934794794263/100000000000000 : ℝ)^3619 := by
    have hnat : (1781550451 : ℕ)^4643*100000000000000^3619 ≤ 10934794794263^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781550451 10000000000 10934794794263 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221237547/10000000000 : ℝ)^4643 ≤ (8688546674073/20000000000000 : ℝ)^3619 := by
    have hnat : (5221237547 : ℕ)^4643*20000000000000^3619 ≤ 8688546674073^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221237547 10000000000 8688546674073 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424327751/10000000000 : ℝ)^4643 ≤ (45622471827557/100000000000000 : ℝ)^3619 := by
    have hnat : (5424327751 : ℕ)^4643*100000000000000^3619 ≤ 45622471827557^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424327751 10000000000 45622471827557 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1781550451/10000000000 : ℝ), (5221237547/10000000000 : ℝ), (5424327751/10000000000 : ℝ)] ![(10934794794263/100000000000000 : ℝ), (8688546674073/20000000000000 : ℝ), (45622471827557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1781550451/10000000000 : ℝ)|^4643 ≤ (10934794794263/100000000000000 : ℝ)^3619
        have hw : |(-1781550451/10000000000 : ℝ)|=(1781550451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221237547/10000000000 : ℝ)|^4643 ≤ (8688546674073/20000000000000 : ℝ)^3619
        have hw : |(5221237547/10000000000 : ℝ)|=(5221237547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424327751/10000000000 : ℝ)|^4643 ≤ (45622471827557/100000000000000 : ℝ)^3619
        have hw : |(5424327751/10000000000 : ℝ)|=(5424327751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s6_2 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323421597/2500000000 : ℝ)*x 0 + (-841177341/5000000000 : ℝ)*x 1 + (5424327747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323421597/2500000000 : ℝ)^4643 ≤ (22108806415647/50000000000000 : ℝ)^3619 := by
    have hnat : (1323421597 : ℕ)^4643*50000000000000^3619 ≤ 22108806415647^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323421597 2500000000 22108806415647 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (841177341/5000000000 : ℝ)^4643 ≤ (507995768269/5000000000000 : ℝ)^3619 := by
    have hnat : (841177341 : ℕ)^4643*5000000000000^3619 ≤ 507995768269^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      841177341 5000000000 507995768269 5000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5424327747/10000000000 : ℝ)^4643 ≤ (22811235892197/50000000000000 : ℝ)^3619 := by
    have hnat : (5424327747 : ℕ)^4643*50000000000000^3619 ≤ 22811235892197^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424327747 10000000000 22811235892197 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323421597/2500000000 : ℝ), (-841177341/5000000000 : ℝ), (5424327747/10000000000 : ℝ)] ![(22108806415647/50000000000000 : ℝ), (507995768269/5000000000000 : ℝ), (22811235892197/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323421597/2500000000 : ℝ)|^4643 ≤ (22108806415647/50000000000000 : ℝ)^3619
        have hw : |(1323421597/2500000000 : ℝ)|=(1323421597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-841177341/5000000000 : ℝ)|^4643 ≤ (507995768269/5000000000000 : ℝ)^3619
        have hw : |(-841177341/5000000000 : ℝ)|=(841177341/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5424327747/10000000000 : ℝ)|^4643 ≤ (22811235892197/50000000000000 : ℝ)^3619
        have hw : |(5424327747/10000000000 : ℝ)|=(5424327747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s6_3 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646843171/5000000000 : ℝ)*x 0 + (339020487/625000000 : ℝ)*x 1 + (-420588671/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646843171/5000000000 : ℝ)^4643 ≤ (44217612338341/100000000000000 : ℝ)^3619 := by
    have hnat : (2646843171 : ℕ)^4643*100000000000000^3619 ≤ 44217612338341^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646843171 5000000000 44217612338341 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339020487/625000000 : ℝ)^4643 ≤ (45622472269969/100000000000000 : ℝ)^3619 := by
    have hnat : (339020487 : ℕ)^4643*100000000000000^3619 ≤ 45622472269969^3619*625000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339020487 625000000 45622472269969 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (420588671/2500000000 : ℝ)^4643 ≤ (81279323047/800000000000 : ℝ)^3619 := by
    have hnat : (420588671 : ℕ)^4643*800000000000^3619 ≤ 81279323047^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      420588671 2500000000 81279323047 800000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646843171/5000000000 : ℝ), (339020487/625000000 : ℝ), (-420588671/2500000000 : ℝ)] ![(44217612338341/100000000000000 : ℝ), (45622472269969/100000000000000 : ℝ), (81279323047/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646843171/5000000000 : ℝ)|^4643 ≤ (44217612338341/100000000000000 : ℝ)^3619
        have hw : |(2646843171/5000000000 : ℝ)|=(2646843171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339020487/625000000 : ℝ)|^4643 ≤ (45622472269969/100000000000000 : ℝ)^3619
        have hw : |(339020487/625000000 : ℝ)|=(339020487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-420588671/2500000000 : ℝ)|^4643 ≤ (81279323047/800000000000 : ℝ)^3619
        have hw : |(-420588671/2500000000 : ℝ)|=(420588671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_s6_4 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2121125013/5000000000 : ℝ)*x 0 + (2244000279/5000000000 : ℝ)*x 1 + (4007613393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121125013/5000000000 : ℝ)^4643 ≤ (33283134236807/100000000000000 : ℝ)^3619 := by
    have hnat : (2121125013 : ℕ)^4643*100000000000000^3619 ≤ 33283134236807^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121125013 5000000000 33283134236807 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244000279/5000000000 : ℝ)^4643 ≤ (4472093800841/12500000000000 : ℝ)^3619 := by
    have hnat : (2244000279 : ℕ)^4643*12500000000000^3619 ≤ 4472093800841^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244000279 5000000000 4472093800841 12500000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4007613393/10000000000 : ℝ)^4643 ≤ (6188023069233/20000000000000 : ℝ)^3619 := by
    have hnat : (4007613393 : ℕ)^4643*20000000000000^3619 ≤ 6188023069233^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007613393 10000000000 6188023069233 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2121125013/5000000000 : ℝ), (2244000279/5000000000 : ℝ), (4007613393/10000000000 : ℝ)] ![(33283134236807/100000000000000 : ℝ), (4472093800841/12500000000000 : ℝ), (6188023069233/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2121125013/5000000000 : ℝ)|^4643 ≤ (33283134236807/100000000000000 : ℝ)^3619
        have hw : |(2121125013/5000000000 : ℝ)|=(2121125013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244000279/5000000000 : ℝ)|^4643 ≤ (4472093800841/12500000000000 : ℝ)^3619
        have hw : |(2244000279/5000000000 : ℝ)|=(2244000279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4007613393/10000000000 : ℝ)|^4643 ≤ (6188023069233/20000000000000 : ℝ)^3619
        have hw : |(4007613393/10000000000 : ℝ)|=(4007613393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1573_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11131/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3097/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3097/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11131/100000 : ℝ) ^ (4641/1024 : ℝ) ≤ (4771741368902807/100000000000000000000 : ℝ) := by
    have hpowers : (11131/100000 : ℝ)^4641 ≤ (4771741368902807/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11131 : ℕ)^4641*100000000000000000000^1024 ≤ 4771741368902807^1024*100000^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11131 100000 4771741368902807 100000000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11131/100000 : ℝ)) (X := (4771741368902807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3097/20000 : ℝ) ^ (4641/1024 : ℝ) ≤ (852224583683307/4000000000000000000 : ℝ) := by
    have hpowers : (3097/20000 : ℝ)^4641 ≤ (852224583683307/4000000000000000000 : ℝ)^1024 := by
      have hnat : (3097 : ℕ)^4641*4000000000000000000^1024 ≤ 852224583683307^1024*20000^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3097 20000 852224583683307 4000000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3097/20000 : ℝ)) (X := (852224583683307/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004771741368902807/50000000000000000000 : ℝ) ≤ (10000210561579707/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (50004771741368902807/50000000000000000000 : ℝ)^1024 ≤ (10000210561579707/10000000000000000 : ℝ)^4641 := by
      have hnat : (50004771741368902807 : ℕ)^1024*10000000000000000^4641 ≤ 10000210561579707^4641*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004771741368902807 50000000000000000000 10000210561579707 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000210561579707/10000000000000000 : ℝ)) (X := (50004771741368902807/50000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013038677980492741/50000000000000000000 : ℝ) ≤ (5000287658903227/5000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (50013038677980492741/50000000000000000000 : ℝ)^1024 ≤ (5000287658903227/5000000000000000 : ℝ)^4641 := by
      have hnat : (50013038677980492741 : ℕ)^1024*5000000000000000^4641 ≤ 5000287658903227^4641*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013038677980492741 50000000000000000000 5000287658903227 5000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000287658903227/5000000000000000 : ℝ)) (X := (50013038677980492741/50000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000852224583683307/2000000000000000000 : ℝ) ≤ (10000940074033201/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (2000852224583683307/2000000000000000000 : ℝ)^1024 ≤ (10000940074033201/10000000000000000 : ℝ)^4641 := by
      have hnat : (2000852224583683307 : ℕ)^1024*10000000000000000^4641 ≤ 10000940074033201^4641*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000852224583683307 2000000000000000000 10000940074033201 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000940074033201/10000000000000000 : ℝ)) (X := (2000852224583683307/2000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4771741368902807/100000000000000000000 : ℝ) ≤ ((10883199145499550641/10885000000000000000 : ℝ)+2*(364756226747/435400000000000 : ℝ)*(11131/100000 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (10883199145499550641/10885000000000000000 : ℝ)+2*(364756226747/435400000000000 : ℝ)*(11131/100000 : ℝ)=(10000210561579707/10000000000000000 : ℝ) by norm_num, show 1+2*(4771741368902807/100000000000000000000 : ℝ)=(50004771741368902807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(852224583683307/4000000000000000000 : ℝ)+(4771741368902807/100000000000000000000 : ℝ) ≤ ((10883199145499550641/10885000000000000000 : ℝ)+(364756226747/435400000000000 : ℝ)*((3097/20000 : ℝ)+(11131/100000 : ℝ)))^(4641/1024 : ℝ) := by
    rw [show (10883199145499550641/10885000000000000000 : ℝ)+(364756226747/435400000000000 : ℝ)*((3097/20000 : ℝ)+(11131/100000 : ℝ))=(5000287658903227/5000000000000000 : ℝ) by norm_num, show 1+(852224583683307/4000000000000000000 : ℝ)+(4771741368902807/100000000000000000000 : ℝ)=(50013038677980492741/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(852224583683307/4000000000000000000 : ℝ) ≤ ((10883199145499550641/10885000000000000000 : ℝ)+2*(364756226747/435400000000000 : ℝ)*(3097/20000 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (10883199145499550641/10885000000000000000 : ℝ)+2*(364756226747/435400000000000 : ℝ)*(3097/20000 : ℝ)=(10000940074033201/10000000000000000 : ℝ) by norm_num, show 1+2*(852224583683307/4000000000000000000 : ℝ)=(2000852224583683307/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10883199145499550641/10885000000000000000 : ℝ)*(X 1 0+X 2 0)+(364756226747/435400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (10883199145499550641/10885000000000000000 : ℝ)) (alpha := (364756226747/435400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10883199145499550641/10885000000000000000 : ℝ)*(X 0 1+X 2 1)+(364756226747/435400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (10883199145499550641/10885000000000000000 : ℝ)) (alpha := (364756226747/435400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10883199145499550641/10885000000000000000 : ℝ)*(X 0 2+X 1 2)+(364756226747/435400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (3097/20000 : ℝ)) (c := (10883199145499550641/10885000000000000000 : ℝ)) (alpha := (364756226747/435400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((267400151/500000000 : ℝ)*X 2 0+(1044034029/2000000000 : ℝ)*X 2 1+(-471628623/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s6_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-1781550451/10000000000 : ℝ)*X 0 0+(5221237547/10000000000 : ℝ)*X 0 1+(5424327751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s6_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1323421597/2500000000 : ℝ)*X 1 0+(-841177341/5000000000 : ℝ)*X 1 1+(5424327747/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s6_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2646843171/5000000000 : ℝ)*X 2 0+(339020487/625000000 : ℝ)*X 2 1+(-420588671/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s6_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2121125013/5000000000 : ℝ)*X 0 0+(2244000279/5000000000 : ℝ)*X 0 1+(4007613393/10000000000 : ℝ)*X 0 2+(2121125013/5000000000 : ℝ)*X 1 0+(2244000279/5000000000 : ℝ)*X 1 1+(4007613393/10000000000 : ℝ)*X 1 2+(2121125013/5000000000 : ℝ)*X 2 0+(2244000279/5000000000 : ℝ)*X 2 1+(4007613393/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_s6_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (698336976447502314649389477/136062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (719789303/100000000000000 : ℝ)*(base19) + (206183759/25000000000000 : ℝ)*(base23) + (13107089/6250000000000 : ℝ)*(lower1) + (58834501/50000000000000 : ℝ)*(upper3) + (7913289/12500000000000 : ℝ)*(lower4) + (2486657/3125000000000 : ℝ)*(upper5) + (1751389392786799/50000000000000 : ℝ)*(major0) + (1751389392786799/50000000000000 : ℝ)*(major1) + (1751389392786799/50000000000000 : ℝ)*(major2) + (2742922559/100000000000000 : ℝ)*(sp0) + (984781501446971/20000000000000 : ℝ)*(sp1) + (307744174215347/6250000000000 : ℝ)*(sp2) + (246195196978863/5000000000000 : ℝ)*(sp3) + (2081649892829919/100000000000000 : ℝ)*(sp4) + (2081649892829919/100000000000000 : ℝ)*(f.failure) + (984781501446971/20000000000000 : ℝ)*(f.sum) + (168767275983/170078125000000000000000000 : ℝ)*base66 + (12125160234761636841/544250000000000000000000000000000 : ℝ)*base68 + (10700569959497886841/544250000000000000000000000000000 : ℝ)*base70 + (23190090996440613159/544250000000000000000000000000000 : ℝ)*base71 + (54066287933723/10885000000000000000000000000 : ℝ)*base73 + (38846115962073636841/544250000000000000000000000000000 : ℝ)*base76 + (7157487613446386841/544250000000000000000000000000000 : ℝ)*base78 + (8650075160094136841/544250000000000000000000000000000 : ℝ)*base80 + (28935207315881/5442500000000000000000000000 : ℝ)*base82 + (14542811/1250000000000000000000 : ℝ)*base89 + (14542811/1250000000000000000000 : ℝ)*base91 + (14542811/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1573_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1573_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1573_box_0 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1578201183/10000000000 : ℝ)*x 0 + (2698135133/5000000000 : ℝ)*x 1 + (5396270339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1578201183/10000000000 : ℝ)^4643 ≤ (9360122454669/100000000000000 : ℝ)^3619 := by
    have hnat : (1578201183 : ℕ)^4643*100000000000000^3619 ≤ 9360122454669^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1578201183 10000000000 9360122454669 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698135133/5000000000 : ℝ)^4643 ≤ (45319938372137/100000000000000 : ℝ)^3619 := by
    have hnat : (2698135133 : ℕ)^4643*100000000000000^3619 ≤ 45319938372137^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698135133 5000000000 45319938372137 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396270339/10000000000 : ℝ)^4643 ≤ (45319939158691/100000000000000 : ℝ)^3619 := by
    have hnat : (5396270339 : ℕ)^4643*100000000000000^3619 ≤ 45319939158691^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396270339 10000000000 45319939158691 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1578201183/10000000000 : ℝ), (2698135133/5000000000 : ℝ), (5396270339/10000000000 : ℝ)] ![(9360122454669/100000000000000 : ℝ), (45319938372137/100000000000000 : ℝ), (45319939158691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1578201183/10000000000 : ℝ)|^4643 ≤ (9360122454669/100000000000000 : ℝ)^3619
        have hw : |(-1578201183/10000000000 : ℝ)|=(1578201183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698135133/5000000000 : ℝ)|^4643 ≤ (45319938372137/100000000000000 : ℝ)^3619
        have hw : |(2698135133/5000000000 : ℝ)|=(2698135133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396270339/10000000000 : ℝ)|^4643 ≤ (45319939158691/100000000000000 : ℝ)^3619
        have hw : |(5396270339/10000000000 : ℝ)|=(5396270339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_1 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635571333/5000000000 : ℝ)*x 0 + (-876078627/5000000000 : ℝ)*x 1 + (5396271101/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635571333/5000000000 : ℝ)^4643 ≤ (4397617195357/10000000000000 : ℝ)^3619 := by
    have hnat : (2635571333 : ℕ)^4643*10000000000000^3619 ≤ 4397617195357^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635571333 5000000000 4397617195357 10000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (876078627/5000000000 : ℝ)^4643 ≤ (5351940332941/50000000000000 : ℝ)^3619 := by
    have hnat : (876078627 : ℕ)^4643*50000000000000^3619 ≤ 5351940332941^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      876078627 5000000000 5351940332941 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5396271101/10000000000 : ℝ)^4643 ≤ (45319947369023/100000000000000 : ℝ)^3619 := by
    have hnat : (5396271101 : ℕ)^4643*100000000000000^3619 ≤ 45319947369023^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396271101 10000000000 45319947369023 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635571333/5000000000 : ℝ), (-876078627/5000000000 : ℝ), (5396271101/10000000000 : ℝ)] ![(4397617195357/10000000000000 : ℝ), (5351940332941/50000000000000 : ℝ), (45319947369023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635571333/5000000000 : ℝ)|^4643 ≤ (4397617195357/10000000000000 : ℝ)^3619
        have hw : |(2635571333/5000000000 : ℝ)|=(2635571333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-876078627/5000000000 : ℝ)|^4643 ≤ (5351940332941/50000000000000 : ℝ)^3619
        have hw : |(-876078627/5000000000 : ℝ)|=(876078627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5396271101/10000000000 : ℝ)|^4643 ≤ (45319947369023/100000000000000 : ℝ)^3619
        have hw : |(5396271101/10000000000 : ℝ)|=(5396271101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_2 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5271143149/10000000000 : ℝ)*x 0 + (674533871/1250000000 : ℝ)*x 1 + (-1752156777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5271143149/10000000000 : ℝ)^4643 ≤ (1759047084933/4000000000000 : ℝ)^3619 := by
    have hnat : (5271143149 : ℕ)^4643*4000000000000^3619 ≤ 1759047084933^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5271143149 10000000000 1759047084933 4000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674533871/1250000000 : ℝ)^4643 ≤ (22659972967993/50000000000000 : ℝ)^3619 := by
    have hnat : (674533871 : ℕ)^4643*50000000000000^3619 ≤ 22659972967993^3619*1250000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674533871 1250000000 22659972967993 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1752156777/10000000000 : ℝ)^4643 ≤ (2675969231847/25000000000000 : ℝ)^3619 := by
    have hnat : (1752156777 : ℕ)^4643*25000000000000^3619 ≤ 2675969231847^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1752156777 10000000000 2675969231847 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5271143149/10000000000 : ℝ), (674533871/1250000000 : ℝ), (-1752156777/10000000000 : ℝ)] ![(1759047084933/4000000000000 : ℝ), (22659972967993/50000000000000 : ℝ), (2675969231847/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5271143149/10000000000 : ℝ)|^4643 ≤ (1759047084933/4000000000000 : ℝ)^3619
        have hw : |(5271143149/10000000000 : ℝ)|=(5271143149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674533871/1250000000 : ℝ)|^4643 ≤ (22659972967993/50000000000000 : ℝ)^3619
        have hw : |(674533871/1250000000 : ℝ)|=(674533871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1752156777/10000000000 : ℝ)|^4643 ≤ (2675969231847/25000000000000 : ℝ)^3619
        have hw : |(-1752156777/10000000000 : ℝ)|=(1752156777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_3 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4442760381/10000000000 : ℝ)*x 0 + (1037129419/2500000000 : ℝ)*x 1 + (2074259303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4442760381/10000000000 : ℝ)^4643 ≤ (35314730071773/100000000000000 : ℝ)^3619 := by
    have hnat : (4442760381 : ℕ)^4643*100000000000000^3619 ≤ 35314730071773^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4442760381 10000000000 35314730071773 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037129419/2500000000 : ℝ)^4643 ≤ (16171315153203/50000000000000 : ℝ)^3619 := by
    have hnat : (1037129419 : ℕ)^4643*50000000000000^3619 ≤ 16171315153203^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037129419 2500000000 16171315153203 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074259303/5000000000 : ℝ)^4643 ≤ (32342639608387/100000000000000 : ℝ)^3619 := by
    have hnat : (2074259303 : ℕ)^4643*100000000000000^3619 ≤ 32342639608387^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074259303 5000000000 32342639608387 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4442760381/10000000000 : ℝ), (1037129419/2500000000 : ℝ), (2074259303/5000000000 : ℝ)] ![(35314730071773/100000000000000 : ℝ), (16171315153203/50000000000000 : ℝ), (32342639608387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4442760381/10000000000 : ℝ)|^4643 ≤ (35314730071773/100000000000000 : ℝ)^3619
        have hw : |(4442760381/10000000000 : ℝ)|=(4442760381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037129419/2500000000 : ℝ)|^4643 ≤ (16171315153203/50000000000000 : ℝ)^3619
        have hw : |(1037129419/2500000000 : ℝ)|=(1037129419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2074259303/5000000000 : ℝ)|^4643 ≤ (32342639608387/100000000000000 : ℝ)^3619
        have hw : |(2074259303/5000000000 : ℝ)|=(2074259303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_4 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1990237909/10000000000 : ℝ)*x 0 + (5245107053/10000000000 : ℝ)*x 1 + (5245106777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1990237909/10000000000 : ℝ)^4643 ≤ (6302304773531/50000000000000 : ℝ)^3619 := by
    have hnat : (1990237909 : ℕ)^4643*50000000000000^3619 ≤ 6302304773531^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1990237909 10000000000 6302304773531 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245107053/10000000000 : ℝ)^4643 ≤ (43697696695597/100000000000000 : ℝ)^3619 := by
    have hnat : (5245107053 : ℕ)^4643*100000000000000^3619 ≤ 43697696695597^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245107053 10000000000 43697696695597 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5245106777/10000000000 : ℝ)^4643 ≤ (10924423436397/25000000000000 : ℝ)^3619 := by
    have hnat : (5245106777 : ℕ)^4643*25000000000000^3619 ≤ 10924423436397^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245106777 10000000000 10924423436397 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1990237909/10000000000 : ℝ), (5245107053/10000000000 : ℝ), (5245106777/10000000000 : ℝ)] ![(6302304773531/50000000000000 : ℝ), (43697696695597/100000000000000 : ℝ), (10924423436397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1990237909/10000000000 : ℝ)|^4643 ≤ (6302304773531/50000000000000 : ℝ)^3619
        have hw : |(-1990237909/10000000000 : ℝ)|=(1990237909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245107053/10000000000 : ℝ)|^4643 ≤ (43697696695597/100000000000000 : ℝ)^3619
        have hw : |(5245107053/10000000000 : ℝ)|=(5245107053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5245106777/10000000000 : ℝ)|^4643 ≤ (10924423436397/25000000000000 : ℝ)^3619
        have hw : |(5245106777/10000000000 : ℝ)|=(5245106777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_5 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268795159/500000000 : ℝ)*x 0 + (-907677649/5000000000 : ℝ)*x 1 + (2622553289/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268795159/500000000 : ℝ)^4643 ≤ (45100606147279/100000000000000 : ℝ)^3619 := by
    have hnat : (268795159 : ℕ)^4643*100000000000000^3619 ≤ 45100606147279^3619*500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268795159 500000000 45100606147279 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (907677649/5000000000 : ℝ)^4643 ≤ (448068088747/4000000000000 : ℝ)^3619 := by
    have hnat : (907677649 : ℕ)^4643*4000000000000^3619 ≤ 448068088747^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907677649 5000000000 448068088747 4000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622553289/5000000000 : ℝ)^4643 ≤ (43697691618589/100000000000000 : ℝ)^3619 := by
    have hnat : (2622553289 : ℕ)^4643*100000000000000^3619 ≤ 43697691618589^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622553289 5000000000 43697691618589 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268795159/500000000 : ℝ), (-907677649/5000000000 : ℝ), (2622553289/5000000000 : ℝ)] ![(45100606147279/100000000000000 : ℝ), (448068088747/4000000000000 : ℝ), (43697691618589/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268795159/500000000 : ℝ)|^4643 ≤ (45100606147279/100000000000000 : ℝ)^3619
        have hw : |(268795159/500000000 : ℝ)|=(268795159/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-907677649/5000000000 : ℝ)|^4643 ≤ (448068088747/4000000000000 : ℝ)^3619
        have hw : |(-907677649/5000000000 : ℝ)|=(907677649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622553289/5000000000 : ℝ)|^4643 ≤ (43697691618589/100000000000000 : ℝ)^3619
        have hw : |(2622553289/5000000000 : ℝ)|=(2622553289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_6 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2687951493/5000000000 : ℝ)*x 0 + (2622553749/5000000000 : ℝ)*x 1 + (-22691929/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2687951493/5000000000 : ℝ)^4643 ≤ (2255030202961/5000000000000 : ℝ)^3619 := by
    have hnat : (2687951493 : ℕ)^4643*5000000000000^3619 ≤ 2255030202961^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687951493 5000000000 2255030202961 5000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622553749/5000000000 : ℝ)^4643 ≤ (43697701451953/100000000000000 : ℝ)^3619 := by
    have hnat : (2622553749 : ℕ)^4643*100000000000000^3619 ≤ 43697701451953^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622553749 5000000000 43697701451953 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (22691929/125000000 : ℝ)^4643 ≤ (11201694476351/100000000000000 : ℝ)^3619 := by
    have hnat : (22691929 : ℕ)^4643*100000000000000^3619 ≤ 11201694476351^3619*125000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      22691929 125000000 11201694476351 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2687951493/5000000000 : ℝ), (2622553749/5000000000 : ℝ), (-22691929/125000000 : ℝ)] ![(2255030202961/5000000000000 : ℝ), (43697701451953/100000000000000 : ℝ), (11201694476351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2687951493/5000000000 : ℝ)|^4643 ≤ (2255030202961/5000000000000 : ℝ)^3619
        have hw : |(2687951493/5000000000 : ℝ)|=(2687951493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622553749/5000000000 : ℝ)|^4643 ≤ (43697701451953/100000000000000 : ℝ)^3619
        have hw : |(2622553749/5000000000 : ℝ)|=(2622553749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-22691929/125000000 : ℝ)|^4643 ≤ (11201694476351/100000000000000 : ℝ)^3619
        have hw : |(-22691929/125000000 : ℝ)|=(22691929/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_7 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2019453809/5000000000 : ℝ)*x 0 + (4350316929/10000000000 : ℝ)*x 1 + (217515893/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2019453809/5000000000 : ℝ)^4643 ≤ (15625210266949/50000000000000 : ℝ)^3619 := by
    have hnat : (2019453809 : ℕ)^4643*50000000000000^3619 ≤ 15625210266949^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019453809 5000000000 15625210266949 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4350316929/10000000000 : ℝ)^4643 ≤ (17187392505347/50000000000000 : ℝ)^3619 := by
    have hnat : (4350316929 : ℕ)^4643*50000000000000^3619 ≤ 17187392505347^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350316929 10000000000 17187392505347 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217515893/500000000 : ℝ)^4643 ≤ (3437479444867/10000000000000 : ℝ)^3619 := by
    have hnat : (217515893 : ℕ)^4643*10000000000000^3619 ≤ 3437479444867^3619*500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217515893 500000000 3437479444867 10000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2019453809/5000000000 : ℝ), (4350316929/10000000000 : ℝ), (217515893/500000000 : ℝ)] ![(15625210266949/50000000000000 : ℝ), (17187392505347/50000000000000 : ℝ), (3437479444867/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2019453809/5000000000 : ℝ)|^4643 ≤ (15625210266949/50000000000000 : ℝ)^3619
        have hw : |(2019453809/5000000000 : ℝ)|=(2019453809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4350316929/10000000000 : ℝ)|^4643 ≤ (17187392505347/50000000000000 : ℝ)^3619
        have hw : |(4350316929/10000000000 : ℝ)|=(4350316929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217515893/500000000 : ℝ)|^4643 ≤ (3437479444867/10000000000000 : ℝ)^3619
        have hw : |(217515893/500000000 : ℝ)|=(217515893/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_8 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-475722027/2500000000 : ℝ)*x 0 + (256928741/500000000 : ℝ)*x 1 + (5416530309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (475722027/2500000000 : ℝ)^4643 ≤ (11899328256383/100000000000000 : ℝ)^3619 := by
    have hnat : (475722027 : ℕ)^4643*100000000000000^3619 ≤ 11899328256383^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      475722027 2500000000 11899328256383 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256928741/500000000 : ℝ)^4643 ≤ (8512464270569/20000000000000 : ℝ)^3619 := by
    have hnat : (256928741 : ℕ)^4643*20000000000000^3619 ≤ 8512464270569^3619*500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256928741 500000000 8512464270569 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416530309/10000000000 : ℝ)^4643 ≤ (910767007433/2000000000000 : ℝ)^3619 := by
    have hnat : (5416530309 : ℕ)^4643*2000000000000^3619 ≤ 910767007433^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416530309 10000000000 910767007433 2000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-475722027/2500000000 : ℝ), (256928741/500000000 : ℝ), (5416530309/10000000000 : ℝ)] ![(11899328256383/100000000000000 : ℝ), (8512464270569/20000000000000 : ℝ), (910767007433/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-475722027/2500000000 : ℝ)|^4643 ≤ (11899328256383/100000000000000 : ℝ)^3619
        have hw : |(-475722027/2500000000 : ℝ)|=(475722027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256928741/500000000 : ℝ)|^4643 ≤ (8512464270569/20000000000000 : ℝ)^3619
        have hw : |(256928741/500000000 : ℝ)|=(256928741/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416530309/10000000000 : ℝ)|^4643 ≤ (910767007433/2000000000000 : ℝ)^3619
        have hw : |(5416530309/10000000000 : ℝ)|=(5416530309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_9 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525709911/1000000000 : ℝ)*x 0 + (-871727761/5000000000 : ℝ)*x 1 + (5416530903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525709911/1000000000 : ℝ)^4643 ≤ (43825914504657/100000000000000 : ℝ)^3619 := by
    have hnat : (525709911 : ℕ)^4643*100000000000000^3619 ≤ 43825914504657^3619*1000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525709911 1000000000 43825914504657 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (871727761/5000000000 : ℝ)^4643 ≤ (10635728702503/100000000000000 : ℝ)^3619 := by
    have hnat : (871727761 : ℕ)^4643*100000000000000^3619 ≤ 10635728702503^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871727761 5000000000 10635728702503 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416530903/10000000000 : ℝ)^4643 ≤ (2276917838931/5000000000000 : ℝ)^3619 := by
    have hnat : (5416530903 : ℕ)^4643*5000000000000^3619 ≤ 2276917838931^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416530903 10000000000 2276917838931 5000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525709911/1000000000 : ℝ), (-871727761/5000000000 : ℝ), (5416530903/10000000000 : ℝ)] ![(43825914504657/100000000000000 : ℝ), (10635728702503/100000000000000 : ℝ), (2276917838931/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525709911/1000000000 : ℝ)|^4643 ≤ (43825914504657/100000000000000 : ℝ)^3619
        have hw : |(525709911/1000000000 : ℝ)|=(525709911/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-871727761/5000000000 : ℝ)|^4643 ≤ (10635728702503/100000000000000 : ℝ)^3619
        have hw : |(-871727761/5000000000 : ℝ)|=(871727761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416530903/10000000000 : ℝ)|^4643 ≤ (2276917838931/5000000000000 : ℝ)^3619
        have hw : |(5416530903/10000000000 : ℝ)|=(5416530903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_10 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051419793/2000000000 : ℝ)*x 0 + (5416530791/10000000000 : ℝ)*x 1 + (-13947647/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051419793/2000000000 : ℝ)^4643 ≤ (5478239119229/12500000000000 : ℝ)^3619 := by
    have hnat : (1051419793 : ℕ)^4643*12500000000000^3619 ≤ 5478239119229^3619*2000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051419793 2000000000 5478239119229 12500000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416530791/10000000000 : ℝ)^4643 ≤ (45538355570571/100000000000000 : ℝ)^3619 := by
    have hnat : (5416530791 : ℕ)^4643*100000000000000^3619 ≤ 45538355570571^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416530791 10000000000 45538355570571 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13947647/80000000 : ℝ)^4643 ≤ (10635731465251/100000000000000 : ℝ)^3619 := by
    have hnat : (13947647 : ℕ)^4643*100000000000000^3619 ≤ 10635731465251^3619*80000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13947647 80000000 10635731465251 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051419793/2000000000 : ℝ), (5416530791/10000000000 : ℝ), (-13947647/80000000 : ℝ)] ![(5478239119229/12500000000000 : ℝ), (45538355570571/100000000000000 : ℝ), (10635731465251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051419793/2000000000 : ℝ)|^4643 ≤ (5478239119229/12500000000000 : ℝ)^3619
        have hw : |(1051419793/2000000000 : ℝ)|=(1051419793/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416530791/10000000000 : ℝ)|^4643 ≤ (45538355570571/100000000000000 : ℝ)^3619
        have hw : |(5416530791/10000000000 : ℝ)|=(5416530791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-13947647/80000000 : ℝ)|^4643 ≤ (10635731465251/100000000000000 : ℝ)^3619
        have hw : |(-13947647/80000000 : ℝ)|=(13947647/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_11 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (44957459/100000000 : ℝ)*x 0 + (1030358949/2500000000 : ℝ)*x 1 + (1030359151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44957459/100000000 : ℝ)^4643 ≤ (7171196629093/20000000000000 : ℝ)^3619 := by
    have hnat : (44957459 : ℕ)^4643*20000000000000^3619 ≤ 7171196629093^3619*100000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44957459 100000000 7171196629093 20000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1030358949/2500000000 : ℝ)^4643 ≤ (32072004386991/100000000000000 : ℝ)^3619 := by
    have hnat : (1030358949 : ℕ)^4643*100000000000000^3619 ≤ 32072004386991^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030358949 2500000000 32072004386991 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1030359151/2500000000 : ℝ)^4643 ≤ (32072012453749/100000000000000 : ℝ)^3619 := by
    have hnat : (1030359151 : ℕ)^4643*100000000000000^3619 ≤ 32072012453749^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1030359151 2500000000 32072012453749 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(44957459/100000000 : ℝ), (1030358949/2500000000 : ℝ), (1030359151/2500000000 : ℝ)] ![(7171196629093/20000000000000 : ℝ), (32072004386991/100000000000000 : ℝ), (32072012453749/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(44957459/100000000 : ℝ)|^4643 ≤ (7171196629093/20000000000000 : ℝ)^3619
        have hw : |(44957459/100000000 : ℝ)|=(44957459/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1030358949/2500000000 : ℝ)|^4643 ≤ (32072004386991/100000000000000 : ℝ)^3619
        have hw : |(1030358949/2500000000 : ℝ)|=(1030358949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1030359151/2500000000 : ℝ)|^4643 ≤ (32072012453749/100000000000000 : ℝ)^3619
        have hw : |(1030359151/2500000000 : ℝ)|=(1030359151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_12 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1665199759/10000000000 : ℝ)*x 0 + (5499564157/10000000000 : ℝ)*x 1 + (5230057507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1665199759/10000000000 : ℝ)^4643 ≤ (5013596686653/50000000000000 : ℝ)^3619 := by
    have hnat : (1665199759 : ℕ)^4643*50000000000000^3619 ≤ 5013596686653^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665199759 10000000000 5013596686653 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5499564157/10000000000 : ℝ)^4643 ≤ (46435900740309/100000000000000 : ℝ)^3619 := by
    have hnat : (5499564157 : ℕ)^4643*100000000000000^3619 ≤ 46435900740309^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499564157 10000000000 46435900740309 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230057507/10000000000 : ℝ)^4643 ≤ (43536905879723/100000000000000 : ℝ)^3619 := by
    have hnat : (5230057507 : ℕ)^4643*100000000000000^3619 ≤ 43536905879723^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230057507 10000000000 43536905879723 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1665199759/10000000000 : ℝ), (5499564157/10000000000 : ℝ), (5230057507/10000000000 : ℝ)] ![(5013596686653/50000000000000 : ℝ), (46435900740309/100000000000000 : ℝ), (43536905879723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1665199759/10000000000 : ℝ)|^4643 ≤ (5013596686653/50000000000000 : ℝ)^3619
        have hw : |(-1665199759/10000000000 : ℝ)|=(1665199759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5499564157/10000000000 : ℝ)|^4643 ≤ (46435900740309/100000000000000 : ℝ)^3619
        have hw : |(5499564157/10000000000 : ℝ)|=(5499564157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230057507/10000000000 : ℝ)|^4643 ≤ (43536905879723/100000000000000 : ℝ)^3619
        have hw : |(5230057507/10000000000 : ℝ)|=(5230057507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_13 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (538633447/1000000000 : ℝ)*x 0 + (-910738147/5000000000 : ℝ)*x 1 + (5230057609/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (538633447/1000000000 : ℝ)^4643 ≤ (45212910919031/100000000000000 : ℝ)^3619 := by
    have hnat : (538633447 : ℕ)^4643*100000000000000^3619 ≤ 45212910919031^3619*1000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538633447 1000000000 45212910919031 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (910738147/5000000000 : ℝ)^4643 ≤ (11250182098683/100000000000000 : ℝ)^3619 := by
    have hnat : (910738147 : ℕ)^4643*100000000000000^3619 ≤ 11250182098683^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910738147 5000000000 11250182098683 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230057609/10000000000 : ℝ)^4643 ≤ (21768453484529/50000000000000 : ℝ)^3619 := by
    have hnat : (5230057609 : ℕ)^4643*50000000000000^3619 ≤ 21768453484529^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230057609 10000000000 21768453484529 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(538633447/1000000000 : ℝ), (-910738147/5000000000 : ℝ), (5230057609/10000000000 : ℝ)] ![(45212910919031/100000000000000 : ℝ), (11250182098683/100000000000000 : ℝ), (21768453484529/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(538633447/1000000000 : ℝ)|^4643 ≤ (45212910919031/100000000000000 : ℝ)^3619
        have hw : |(538633447/1000000000 : ℝ)|=(538633447/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-910738147/5000000000 : ℝ)|^4643 ≤ (11250182098683/100000000000000 : ℝ)^3619
        have hw : |(-910738147/5000000000 : ℝ)|=(910738147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230057609/10000000000 : ℝ)|^4643 ≤ (21768453484529/50000000000000 : ℝ)^3619
        have hw : |(5230057609/10000000000 : ℝ)|=(5230057609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_14 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386334467/10000000000 : ℝ)*x 0 + (5230057261/10000000000 : ℝ)*x 1 + (-910738383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386334467/10000000000 : ℝ)^4643 ≤ (11303227721681/25000000000000 : ℝ)^3619 := by
    have hnat : (5386334467 : ℕ)^4643*25000000000000^3619 ≤ 11303227721681^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386334467 10000000000 11303227721681 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230057261/10000000000 : ℝ)^4643 ≤ (5442112906563/12500000000000 : ℝ)^3619 := by
    have hnat : (5230057261 : ℕ)^4643*12500000000000^3619 ≤ 5442112906563^3619*10000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230057261 10000000000 5442112906563 12500000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (910738383/5000000000 : ℝ)^4643 ≤ (5625092919413/50000000000000 : ℝ)^3619 := by
    have hnat : (910738383 : ℕ)^4643*50000000000000^3619 ≤ 5625092919413^3619*5000000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910738383 5000000000 5625092919413 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386334467/10000000000 : ℝ), (5230057261/10000000000 : ℝ), (-910738383/5000000000 : ℝ)] ![(11303227721681/25000000000000 : ℝ), (5442112906563/12500000000000 : ℝ), (5625092919413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386334467/10000000000 : ℝ)|^4643 ≤ (11303227721681/25000000000000 : ℝ)^3619
        have hw : |(5386334467/10000000000 : ℝ)|=(5386334467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230057261/10000000000 : ℝ)|^4643 ≤ (5442112906563/12500000000000 : ℝ)^3619
        have hw : |(5230057261/10000000000 : ℝ)|=(5230057261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-910738383/5000000000 : ℝ)|^4643 ≤ (5625092919413/50000000000000 : ℝ)^3619
        have hw : |(-910738383/5000000000 : ℝ)|=(910738383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1573_box_15 (p : ℝ) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (999459297/2500000000 : ℝ)*x 0 + (1092595851/2500000000 : ℝ)*x 1 + (174815341/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (999459297/2500000000 : ℝ)^4643 ≤ (7710829329313/25000000000000 : ℝ)^3619 := by
    have hnat : (999459297 : ℕ)^4643*25000000000000^3619 ≤ 7710829329313^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999459297 2500000000 7710829329313 25000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1092595851/2500000000 : ℝ)^4643 ≤ (17289170360171/50000000000000 : ℝ)^3619 := by
    have hnat : (1092595851 : ℕ)^4643*50000000000000^3619 ≤ 17289170360171^3619*2500000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1092595851 2500000000 17289170360171 50000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (174815341/400000000 : ℝ)^4643 ≤ (34578341948573/100000000000000 : ℝ)^3619 := by
    have hnat : (174815341 : ℕ)^4643*100000000000000^3619 ≤ 34578341948573^3619*400000000^4643 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174815341 400000000 34578341948573 100000000000000 4643 3619 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4643/1024 : ℝ)) 4643 3619 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(999459297/2500000000 : ℝ), (1092595851/2500000000 : ℝ), (174815341/400000000 : ℝ)] ![(7710829329313/25000000000000 : ℝ), (17289170360171/50000000000000 : ℝ), (34578341948573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(999459297/2500000000 : ℝ)|^4643 ≤ (7710829329313/25000000000000 : ℝ)^3619
        have hw : |(999459297/2500000000 : ℝ)|=(999459297/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1092595851/2500000000 : ℝ)|^4643 ≤ (17289170360171/50000000000000 : ℝ)^3619
        have hw : |(1092595851/2500000000 : ℝ)|=(1092595851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(174815341/400000000 : ℝ)|^4643 ≤ (34578341948573/100000000000000 : ℝ)^3619
        have hw : |(174815341/400000000 : ℝ)|=(174815341/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1573_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31917/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58917/100000 : ℝ) ∧ (1619/2000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (17277/20000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11131/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11131/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11131/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11131/100000 : ℝ) ^ (4641/1024 : ℝ) ≤ (4771741368902807/100000000000000000000 : ℝ) := by
    have hpowers : (11131/100000 : ℝ)^4641 ≤ (4771741368902807/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11131 : ℕ)^4641*100000000000000000000^1024 ≤ 4771741368902807^1024*100000^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11131 100000 4771741368902807 100000000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11131/100000 : ℝ)) (X := (4771741368902807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4641/1024 : ℝ) ≤ (5324844867591259/25000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4641 ≤ (5324844867591259/25000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4641*25000000000000000000^1024 ≤ 5324844867591259^1024*25000^4641 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 5324844867591259 25000000000000000000 4641 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (5324844867591259/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004771741368902807/50000000000000000000 : ℝ) ≤ (10000210561579707/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (50004771741368902807/50000000000000000000 : ℝ)^1024 ≤ (10000210561579707/10000000000000000 : ℝ)^4641 := by
      have hnat : (50004771741368902807 : ℕ)^1024*10000000000000000^4641 ≤ 10000210561579707^4641*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004771741368902807 50000000000000000000 10000210561579707 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000210561579707/10000000000000000 : ℝ)) (X := (50004771741368902807/50000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100026071120839267843/100000000000000000000 : ℝ) ≤ (10000575180261367/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (100026071120839267843/100000000000000000000 : ℝ)^1024 ≤ (10000575180261367/10000000000000000 : ℝ)^4641 := by
      have hnat : (100026071120839267843 : ℕ)^1024*10000000000000000^4641 ≤ 10000575180261367^4641*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100026071120839267843 100000000000000000000 10000575180261367 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000575180261367/10000000000000000 : ℝ)) (X := (100026071120839267843/100000000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505324844867591259/12500000000000000000 : ℝ) ≤ (10000939798943027/10000000000000000 : ℝ) ^ (4641/1024 : ℝ) := by
    have hpowers : (12505324844867591259/12500000000000000000 : ℝ)^1024 ≤ (10000939798943027/10000000000000000 : ℝ)^4641 := by
      have hnat : (12505324844867591259 : ℕ)^1024*10000000000000000^4641 ≤ 10000939798943027^4641*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505324844867591259 12500000000000000000 10000939798943027 10000000000000000 1024 4641 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000939798943027/10000000000000000 : ℝ)) (X := (12505324844867591259/12500000000000000000 : ℝ)) (by norm_num) 4641 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4771741368902807/100000000000000000000 : ℝ) ≤ ((43522799433465349651/43530000000000000000 : ℝ)+2*(18230934083/21765000000000 : ℝ)*(11131/100000 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (43522799433465349651/43530000000000000000 : ℝ)+2*(18230934083/21765000000000 : ℝ)*(11131/100000 : ℝ)=(10000210561579707/10000000000000000 : ℝ) by norm_num, show 1+2*(4771741368902807/100000000000000000000 : ℝ)=(50004771741368902807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5324844867591259/25000000000000000000 : ℝ)+(4771741368902807/100000000000000000000 : ℝ) ≤ ((43522799433465349651/43530000000000000000 : ℝ)+(18230934083/21765000000000 : ℝ)*((3871/25000 : ℝ)+(11131/100000 : ℝ)))^(4641/1024 : ℝ) := by
    rw [show (43522799433465349651/43530000000000000000 : ℝ)+(18230934083/21765000000000 : ℝ)*((3871/25000 : ℝ)+(11131/100000 : ℝ))=(10000575180261367/10000000000000000 : ℝ) by norm_num, show 1+(5324844867591259/25000000000000000000 : ℝ)+(4771741368902807/100000000000000000000 : ℝ)=(100026071120839267843/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5324844867591259/25000000000000000000 : ℝ) ≤ ((43522799433465349651/43530000000000000000 : ℝ)+2*(18230934083/21765000000000 : ℝ)*(3871/25000 : ℝ))^(4641/1024 : ℝ) := by
    rw [show (43522799433465349651/43530000000000000000 : ℝ)+2*(18230934083/21765000000000 : ℝ)*(3871/25000 : ℝ)=(10000939798943027/10000000000000000 : ℝ) by norm_num, show 1+2*(5324844867591259/25000000000000000000 : ℝ)=(12505324844867591259/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43522799433465349651/43530000000000000000 : ℝ)*(X 1 0+X 2 0)+(18230934083/21765000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (43522799433465349651/43530000000000000000 : ℝ)) (alpha := (18230934083/21765000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43522799433465349651/43530000000000000000 : ℝ)*(X 0 1+X 2 1)+(18230934083/21765000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (43522799433465349651/43530000000000000000 : ℝ)) (alpha := (18230934083/21765000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43522799433465349651/43530000000000000000 : ℝ)*(X 0 2+X 1 2)+(18230934083/21765000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4641/1024 : ℝ)) (lo := (11131/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (43522799433465349651/43530000000000000000 : ℝ)) (alpha := (18230934083/21765000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1578201183/10000000000 : ℝ)*X 0 0+(2698135133/5000000000 : ℝ)*X 0 1+(5396270339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635571333/5000000000 : ℝ)*X 1 0+(-876078627/5000000000 : ℝ)*X 1 1+(5396271101/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5271143149/10000000000 : ℝ)*X 2 0+(674533871/1250000000 : ℝ)*X 2 1+(-1752156777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4442760381/10000000000 : ℝ)*X 0 0+(1037129419/2500000000 : ℝ)*X 0 1+(2074259303/5000000000 : ℝ)*X 0 2+(4442760381/10000000000 : ℝ)*X 1 0+(1037129419/2500000000 : ℝ)*X 1 1+(2074259303/5000000000 : ℝ)*X 1 2+(4442760381/10000000000 : ℝ)*X 2 0+(1037129419/2500000000 : ℝ)*X 2 1+(2074259303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1990237909/10000000000 : ℝ)*X 0 0+(5245107053/10000000000 : ℝ)*X 0 1+(5245106777/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((268795159/500000000 : ℝ)*X 1 0+(-907677649/5000000000 : ℝ)*X 1 1+(2622553289/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2687951493/5000000000 : ℝ)*X 2 0+(2622553749/5000000000 : ℝ)*X 2 1+(-22691929/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2019453809/5000000000 : ℝ)*X 0 0+(4350316929/10000000000 : ℝ)*X 0 1+(217515893/500000000 : ℝ)*X 0 2+(2019453809/5000000000 : ℝ)*X 1 0+(4350316929/10000000000 : ℝ)*X 1 1+(217515893/500000000 : ℝ)*X 1 2+(2019453809/5000000000 : ℝ)*X 2 0+(4350316929/10000000000 : ℝ)*X 2 1+(217515893/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-475722027/2500000000 : ℝ)*X 0 0+(256928741/500000000 : ℝ)*X 0 1+(5416530309/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((525709911/1000000000 : ℝ)*X 1 0+(-871727761/5000000000 : ℝ)*X 1 1+(5416530903/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1051419793/2000000000 : ℝ)*X 2 0+(5416530791/10000000000 : ℝ)*X 2 1+(-13947647/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((44957459/100000000 : ℝ)*X 0 0+(1030358949/2500000000 : ℝ)*X 0 1+(1030359151/2500000000 : ℝ)*X 0 2+(44957459/100000000 : ℝ)*X 1 0+(1030358949/2500000000 : ℝ)*X 1 1+(1030359151/2500000000 : ℝ)*X 1 2+(44957459/100000000 : ℝ)*X 2 0+(1030358949/2500000000 : ℝ)*X 2 1+(1030359151/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1665199759/10000000000 : ℝ)*X 0 0+(5499564157/10000000000 : ℝ)*X 0 1+(5230057507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((538633447/1000000000 : ℝ)*X 1 0+(-910738147/5000000000 : ℝ)*X 1 1+(5230057609/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5386334467/10000000000 : ℝ)*X 2 0+(5230057261/10000000000 : ℝ)*X 2 1+(-910738383/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((999459297/2500000000 : ℝ)*X 0 0+(1092595851/2500000000 : ℝ)*X 0 1+(174815341/400000000 : ℝ)*X 0 2+(999459297/2500000000 : ℝ)*X 1 0+(1092595851/2500000000 : ℝ)*X 1 1+(174815341/400000000 : ℝ)*X 1 2+(999459297/2500000000 : ℝ)*X 2 0+(1092595851/2500000000 : ℝ)*X 2 1+(174815341/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1573_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31917/50000 : ℝ) ≤ (-23154863427693634982329424402709/36275000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2291347/1000000000000 : ℝ)*(upper0) + (118397629/50000000000000 : ℝ)*(lower2) + (1679699/4000000000000 : ℝ)*(lower3) + (115603774359453/5000000000000 : ℝ)*(major0) + (115603774359453/5000000000000 : ℝ)*(major1) + (115603774359453/5000000000000 : ℝ)*(major2) + (297264601/10000000000000 : ℝ)*(sp1) + (2396426859/100000000000000 : ℝ)*(sp3) + (1635697206575311/50000000000000 : ℝ)*(sp4) + (204462044613533/6250000000000 : ℝ)*(sp5) + (3271137699373031/100000000000000 : ℝ)*(sp6) + (274806009205659/20000000000000 : ℝ)*(sp7) + (318327979/25000000000000 : ℝ)*(sp8) + (257987089507/100000000000000 : ℝ)*(sp14) + (687016221227577/50000000000000 : ℝ)*(f.failure) + (1635697843231269/50000000000000 : ℝ)*(f.sum) + (6177439838973/1451000000000000000000000000 : ℝ)*base66 + (367550705262950301/72550000000000000000000000000000 : ℝ)*base67 + (65832901817100301/72550000000000000000000000000000 : ℝ)*base69 + (318043422199750301/72550000000000000000000000000000 : ℝ)*base71 + (2735138138193/290200000000000000000000000 : ℝ)*base74 + (169938462214300301/72550000000000000000000000000000 : ℝ)*base75 + (85050066830500301/72550000000000000000000000000000 : ℝ)*base77 + (209953628301500301/72550000000000000000000000000000 : ℝ)*base79 + (1731955653933/362750000000000000000000000 : ℝ)*base82 + (3290013/625000000000000000000 : ℝ)*base89 + (3290013/625000000000000000000 : ℝ)*base91 + (3290013/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58917/100000 : ℝ) ≤ (106864957440740038583704064641291/181375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33076491/20000000000000 : ℝ)*(lower1) + (9248207/20000000000000 : ℝ)*(lower3) + (92052249/50000000000000 : ℝ)*(upper4) + (4153337/6250000000000 : ℝ)*(upper5) + (1196255327765641/50000000000000 : ℝ)*(major0) + (1196255327765641/50000000000000 : ℝ)*(major1) + (1196255327765641/50000000000000 : ℝ)*(major2) + (1671773825372217/50000000000000 : ℝ)*(sp0) + (1671769338971959/50000000000000 : ℝ)*(sp1) + (1671768259753309/50000000000000 : ℝ)*(sp2) + (710894476547441/50000000000000 : ℝ)*(sp3) + (2243200129/25000000000000 : ℝ)*(sp5) + (11131237817/100000000000000 : ℝ)*(sp6) + (8985278667/20000000000000 : ℝ)*(sp11) + (177729234936027/12500000000000 : ℝ)*(f.failure) + (1671773825372217/50000000000000 : ℝ)*(f.sum) + (3029926834717/544125000000000000000000000 : ℝ)*base66 + (5642587316748858709/2176500000000000000000000000000000 : ℝ)*base68 + (11027027667531858709/2176500000000000000000000000000000 : ℝ)*base70 + (434332418090141291/2176500000000000000000000000000000 : ℝ)*base71 + (1094016845027/272062500000000000000000000 : ℝ)*base74 + (10791889141791858709/2176500000000000000000000000000000 : ℝ)*base76 + (12237762877773858709/2176500000000000000000000000000000 : ℝ)*base78 + (10879069249767858709/2176500000000000000000000000000000 : ℝ)*base80 + (416806236953/2176500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (31937/156250000000000000000 : ℝ)*base90 + (31937/156250000000000000000 : ℝ)*base92 + (31937/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (1619/2000 : ℝ) ≤ (146827560490395560850264320326683/181375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7892369/10000000000000 : ℝ)*(lower1) + (25528293/20000000000000 : ℝ)*(upper2) + (35336883/100000000000000 : ℝ)*(lower5) + (644633709530589/25000000000000 : ℝ)*(major0) + (644633709530589/25000000000000 : ℝ)*(major1) + (644633709530589/25000000000000 : ℝ)*(major2) + (844556231/10000000000000 : ℝ)*(sp0) + (18742827111/25000000000000 : ℝ)*(sp1) + (21226982513/100000000000000 : ℝ)*(sp2) + (21028712337/100000000000000 : ℝ)*(sp3) + (449711469579543/12500000000000 : ℝ)*(sp8) + (359762523089021/10000000000000 : ℝ)*(sp9) + (3597678975216141/100000000000000 : ℝ)*(sp10) + (1532364285353861/100000000000000 : ℝ)*(sp11) + (766192657033099/50000000000000 : ℝ)*(f.failure) + (1798850101099327/50000000000000 : ℝ)*(f.sum) + (7825883586101/1451000000000000000000000000 : ℝ)*base66 + (454400190669324813/362750000000000000000000000000000 : ℝ)*base67 + (940690527483324813/362750000000000000000000000000000 : ℝ)*base69 + (1153377581858574813/362750000000000000000000000000000 : ℝ)*base71 + (183516735473/362750000000000000000000000 : ℝ)*base73 + (2978125567311324813/362750000000000000000000000000000 : ℝ)*base75 + (1032958113159074813/362750000000000000000000000000000 : ℝ)*base77 + (1008048257838074813/362750000000000000000000000000000 : ℝ)*base79 + (2500027762137/725500000000000000000000000 : ℝ)*base81 + (1410231/625000000000000000000 : ℝ)*base89 + (1410231/625000000000000000000 : ℝ)*base91 + (1410231/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-17277/20000 : ℝ) ≤ (-313351402918662373355064633/362750000000000000000000000 : ℝ) := by norm_num
    linear_combination (184796869/100000000000000 : ℝ)*(lower0) + (11695789/12500000000000 : ℝ)*(lower1) + (38532887/100000000000000 : ℝ)*(lower3) + (11101813/6250000000000 : ℝ)*(lower4) + (2619087162489759/100000000000000 : ℝ)*(major0) + (2619087162489759/100000000000000 : ℝ)*(major1) + (2619087162489759/100000000000000 : ℝ)*(major2) + (1142037997/10000000000000 : ℝ)*(sp5) + (180634746071/100000000000000 : ℝ)*(sp6) + (8904966647/50000000000000 : ℝ)*(sp7) + (74209668507113/2000000000000 : ℝ)*(sp12) + (11595225015549/312500000000 : ℝ)*(sp13) + (1855151395304789/50000000000000 : ℝ)*(sp14) + (97279197113923/6250000000000 : ℝ)*(sp15) + (1556484963756061/100000000000000 : ℝ)*(f.failure) + (74209668507113/2000000000000 : ℝ)*(f.sum) + (350938573643/145100000000000000000000000 : ℝ)*base66 + (1470469130169425297/1451000000000000000000000000000000 : ℝ)*base68 + (5323569365211425297/1451000000000000000000000000000000 : ℝ)*base70 + (608217758402574703/1451000000000000000000000000000000 : ℝ)*base71 + (1014015593239/725500000000000000000000000 : ℝ)*base73 + (10435481875941425297/1451000000000000000000000000000000 : ℝ)*base76 + (3313754198270574703/1451000000000000000000000000000000 : ℝ)*base77 + (6298548829964574703/1451000000000000000000000000000000 : ℝ)*base79 + (1586114013497/181375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (3682191/1250000000000000000000 : ℝ)*base90 + (3682191/1250000000000000000000 : ℝ)*base92 + (3682191/1250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1573_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31917/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58917/100000 : ℝ) else (1619/2000 : ℝ) ≤ X j i ∧ X j i ≤ (17277/20000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1573_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1573_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31917/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58917/100000 : ℝ) else (1619/2000 : ℝ) ≤ X j i ∧ X j i ≤ (17277/20000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1573_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1573_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4641/1024 : ℝ) ≤ p) (hpb : p ≤ (4643/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (21033669/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11131/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31917/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58917/100000 : ℝ) else (1619/2000 : ℝ) ≤ X j i ∧ X j i ≤ (17277/20000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1573_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
