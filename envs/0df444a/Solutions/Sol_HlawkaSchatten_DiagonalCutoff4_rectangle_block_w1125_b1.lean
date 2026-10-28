-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1125_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:11:07.279487+00:00
-- url     : https://prove2.me/submissions/ab7494e4-52c1-4c8d-b120-8954b3cfa729

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
theorem support_rectangle_w1125_s3_0 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2171048379/10000000000 : ℝ)*x 0 + (5430965881/10000000000 : ℝ)*x 1 + (5230448419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171048379/10000000000 : ℝ)^4159 ≤ (13182649256439/100000000000000 : ℝ)^3135 := by
    have hnat : (2171048379 : ℕ)^4159*100000000000000^3135 ≤ 13182649256439^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171048379 10000000000 13182649256439 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430965881/10000000000 : ℝ)^4159 ≤ (44491670163949/100000000000000 : ℝ)^3135 := by
    have hnat : (5430965881 : ℕ)^4159*100000000000000^3135 ≤ 44491670163949^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430965881 10000000000 44491670163949 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230448419/10000000000 : ℝ)^4159 ≤ (21162840282987/50000000000000 : ℝ)^3135 := by
    have hnat : (5230448419 : ℕ)^4159*50000000000000^3135 ≤ 21162840282987^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230448419 10000000000 21162840282987 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2171048379/10000000000 : ℝ), (5430965881/10000000000 : ℝ), (5230448419/10000000000 : ℝ)] ![(13182649256439/100000000000000 : ℝ), (44491670163949/100000000000000 : ℝ), (21162840282987/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2171048379/10000000000 : ℝ)|^4159 ≤ (13182649256439/100000000000000 : ℝ)^3135
        have hw : |(-2171048379/10000000000 : ℝ)|=(2171048379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430965881/10000000000 : ℝ)|^4159 ≤ (44491670163949/100000000000000 : ℝ)^3135
        have hw : |(5430965881/10000000000 : ℝ)|=(5430965881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230448419/10000000000 : ℝ)|^4159 ≤ (21162840282987/50000000000000 : ℝ)^3135
        have hw : |(5230448419/10000000000 : ℝ)|=(5230448419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s3_1 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677104297/5000000000 : ℝ)*x 0 + (-2273585059/10000000000 : ℝ)*x 1 + (5230448339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677104297/5000000000 : ℝ)^4159 ≤ (6821780803/15625000000 : ℝ)^3135 := by
    have hnat : (2677104297 : ℕ)^4159*15625000000^3135 ≤ 6821780803^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677104297 5000000000 6821780803 15625000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2273585059/10000000000 : ℝ)^4159 ≤ (7007461569527/50000000000000 : ℝ)^3135 := by
    have hnat : (2273585059 : ℕ)^4159*50000000000000^3135 ≤ 7007461569527^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273585059 10000000000 7007461569527 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230448339/10000000000 : ℝ)^4159 ≤ (8465135941429/20000000000000 : ℝ)^3135 := by
    have hnat : (5230448339 : ℕ)^4159*20000000000000^3135 ≤ 8465135941429^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230448339 10000000000 8465135941429 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677104297/5000000000 : ℝ), (-2273585059/10000000000 : ℝ), (5230448339/10000000000 : ℝ)] ![(6821780803/15625000000 : ℝ), (7007461569527/50000000000000 : ℝ), (8465135941429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677104297/5000000000 : ℝ)|^4159 ≤ (6821780803/15625000000 : ℝ)^3135
        have hw : |(2677104297/5000000000 : ℝ)|=(2677104297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2273585059/10000000000 : ℝ)|^4159 ≤ (7007461569527/50000000000000 : ℝ)^3135
        have hw : |(-2273585059/10000000000 : ℝ)|=(2273585059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230448339/10000000000 : ℝ)|^4159 ≤ (8465135941429/20000000000000 : ℝ)^3135
        have hw : |(5230448339/10000000000 : ℝ)|=(5230448339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s3_2 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2677104347/5000000000 : ℝ)*x 0 + (5230448441/10000000000 : ℝ)*x 1 + (-2273584793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2677104347/5000000000 : ℝ)^4159 ≤ (43659398220967/100000000000000 : ℝ)^3135 := by
    have hnat : (2677104347 : ℕ)^4159*100000000000000^3135 ≤ 43659398220967^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677104347 5000000000 43659398220967 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230448441/10000000000 : ℝ)^4159 ≤ (5290710100269/12500000000000 : ℝ)^3135 := by
    have hnat : (5230448441 : ℕ)^4159*12500000000000^3135 ≤ 5290710100269^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230448441 10000000000 5290710100269 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273584793/10000000000 : ℝ)^4159 ≤ (3503730240947/25000000000000 : ℝ)^3135 := by
    have hnat : (2273584793 : ℕ)^4159*25000000000000^3135 ≤ 3503730240947^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273584793 10000000000 3503730240947 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2677104347/5000000000 : ℝ), (5230448441/10000000000 : ℝ), (-2273584793/10000000000 : ℝ)] ![(43659398220967/100000000000000 : ℝ), (5290710100269/12500000000000 : ℝ), (3503730240947/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2677104347/5000000000 : ℝ)|^4159 ≤ (43659398220967/100000000000000 : ℝ)^3135
        have hw : |(2677104347/5000000000 : ℝ)|=(2677104347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230448441/10000000000 : ℝ)|^4159 ≤ (5290710100269/12500000000000 : ℝ)^3135
        have hw : |(5230448441/10000000000 : ℝ)|=(5230448441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2273584793/10000000000 : ℝ)|^4159 ≤ (3503730240947/25000000000000 : ℝ)^3135
        have hw : |(-2273584793/10000000000 : ℝ)|=(2273584793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s3_3 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4364703661/10000000000 : ℝ)*x 0 + (166816927/400000000 : ℝ)*x 1 + (1142004299/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364703661/10000000000 : ℝ)^4159 ≤ (16646444012741/50000000000000 : ℝ)^3135 := by
    have hnat : (4364703661 : ℕ)^4159*50000000000000^3135 ≤ 16646444012741^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364703661 10000000000 16646444012741 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166816927/400000000 : ℝ)^4159 ≤ (244854324493/781250000000 : ℝ)^3135 := by
    have hnat : (166816927 : ℕ)^4159*781250000000^3135 ≤ 244854324493^3135*400000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166816927 400000000 244854324493 781250000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1142004299/2500000000 : ℝ)^4159 ≤ (35365758416039/100000000000000 : ℝ)^3135 := by
    have hnat : (1142004299 : ℕ)^4159*100000000000000^3135 ≤ 35365758416039^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1142004299 2500000000 35365758416039 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364703661/10000000000 : ℝ), (166816927/400000000 : ℝ), (1142004299/2500000000 : ℝ)] ![(16646444012741/50000000000000 : ℝ), (244854324493/781250000000 : ℝ), (35365758416039/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364703661/10000000000 : ℝ)|^4159 ≤ (16646444012741/50000000000000 : ℝ)^3135
        have hw : |(4364703661/10000000000 : ℝ)|=(4364703661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166816927/400000000 : ℝ)|^4159 ≤ (244854324493/781250000000 : ℝ)^3135
        have hw : |(166816927/400000000 : ℝ)|=(166816927/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1142004299/2500000000 : ℝ)|^4159 ≤ (35365758416039/100000000000000 : ℝ)^3135
        have hw : |(1142004299/2500000000 : ℝ)|=(1142004299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s3_4 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-108553369/500000000 : ℝ)*x 0 + (209249429/400000000 : ℝ)*x 1 + (1357543517/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108553369/500000000 : ℝ)^4159 ≤ (6591401158209/50000000000000 : ℝ)^3135 := by
    have hnat : (108553369 : ℕ)^4159*50000000000000^3135 ≤ 6591401158209^3135*500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108553369 500000000 6591401158209 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209249429/400000000 : ℝ)^4159 ≤ (330735412367/781250000000 : ℝ)^3135 := by
    have hnat : (209249429 : ℕ)^4159*781250000000^3135 ≤ 330735412367^3135*400000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209249429 400000000 330735412367 781250000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357543517/2500000000 : ℝ)^4159 ≤ (11120766219551/25000000000000 : ℝ)^3135 := by
    have hnat : (1357543517 : ℕ)^4159*25000000000000^3135 ≤ 11120766219551^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357543517 2500000000 11120766219551 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-108553369/500000000 : ℝ), (209249429/400000000 : ℝ), (1357543517/2500000000 : ℝ)] ![(6591401158209/50000000000000 : ℝ), (330735412367/781250000000 : ℝ), (11120766219551/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-108553369/500000000 : ℝ)|^4159 ≤ (6591401158209/50000000000000 : ℝ)^3135
        have hw : |(-108553369/500000000 : ℝ)|=(108553369/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209249429/400000000 : ℝ)|^4159 ≤ (330735412367/781250000000 : ℝ)^3135
        have hw : |(209249429/400000000 : ℝ)|=(209249429/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357543517/2500000000 : ℝ)|^4159 ≤ (11120766219551/25000000000000 : ℝ)^3135
        have hw : |(1357543517/2500000000 : ℝ)|=(1357543517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s3_5 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060694361/2000000000 : ℝ)*x 0 + (-518464929/2500000000 : ℝ)*x 1 + (1357543473/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060694361/2000000000 : ℝ)^4159 ≤ (21555697201499/50000000000000 : ℝ)^3135 := by
    have hnat : (1060694361 : ℕ)^4159*50000000000000^3135 ≤ 21555697201499^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060694361 2000000000 21555697201499 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518464929/2500000000 : ℝ)^4159 ≤ (1550692827209/12500000000000 : ℝ)^3135 := by
    have hnat : (518464929 : ℕ)^4159*12500000000000^3135 ≤ 1550692827209^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518464929 2500000000 1550692827209 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1357543473/2500000000 : ℝ)^4159 ≤ (5560382870689/12500000000000 : ℝ)^3135 := by
    have hnat : (1357543473 : ℕ)^4159*12500000000000^3135 ≤ 5560382870689^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357543473 2500000000 5560382870689 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060694361/2000000000 : ℝ), (-518464929/2500000000 : ℝ), (1357543473/2500000000 : ℝ)] ![(21555697201499/50000000000000 : ℝ), (1550692827209/12500000000000 : ℝ), (5560382870689/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060694361/2000000000 : ℝ)|^4159 ≤ (21555697201499/50000000000000 : ℝ)^3135
        have hw : |(1060694361/2000000000 : ℝ)|=(1060694361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-518464929/2500000000 : ℝ)|^4159 ≤ (1550692827209/12500000000000 : ℝ)^3135
        have hw : |(-518464929/2500000000 : ℝ)|=(518464929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1357543473/2500000000 : ℝ)|^4159 ≤ (5560382870689/12500000000000 : ℝ)^3135
        have hw : |(1357543473/2500000000 : ℝ)|=(1357543473/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s3_6 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (165733499/312500000 : ℝ)*x 0 + (5430173851/10000000000 : ℝ)*x 1 + (-41477191/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165733499/312500000 : ℝ)^4159 ≤ (10777849040201/25000000000000 : ℝ)^3135 := by
    have hnat : (165733499 : ℕ)^4159*25000000000000^3135 ≤ 10777849040201^3135*312500000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165733499 312500000 10777849040201 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430173851/10000000000 : ℝ)^4159 ≤ (22241531259971/50000000000000 : ℝ)^3135 := by
    have hnat : (5430173851 : ℕ)^4159*50000000000000^3135 ≤ 22241531259971^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430173851 10000000000 22241531259971 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41477191/200000000 : ℝ)^4159 ≤ (6202770650169/50000000000000 : ℝ)^3135 := by
    have hnat : (41477191 : ℕ)^4159*50000000000000^3135 ≤ 6202770650169^3135*200000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41477191 200000000 6202770650169 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165733499/312500000 : ℝ), (5430173851/10000000000 : ℝ), (-41477191/200000000 : ℝ)] ![(10777849040201/25000000000000 : ℝ), (22241531259971/50000000000000 : ℝ), (6202770650169/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165733499/312500000 : ℝ)|^4159 ≤ (10777849040201/25000000000000 : ℝ)^3135
        have hw : |(165733499/312500000 : ℝ)|=(165733499/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430173851/10000000000 : ℝ)|^4159 ≤ (22241531259971/50000000000000 : ℝ)^3135
        have hw : |(5430173851/10000000000 : ℝ)|=(5430173851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-41477191/200000000 : ℝ)|^4159 ≤ (6202770650169/50000000000000 : ℝ)^3135
        have hw : |(-41477191/200000000 : ℝ)|=(41477191/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s3_7 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4364740983/10000000000 : ℝ)*x 0 + (4566456213/10000000000 : ℝ)*x 1 + (2085996609/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4364740983/10000000000 : ℝ)^4159 ≤ (33293265696447/100000000000000 : ℝ)^3135 := by
    have hnat : (4364740983 : ℕ)^4159*100000000000000^3135 ≤ 33293265696447^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4364740983 10000000000 33293265696447 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4566456213/10000000000 : ℝ)^4159 ≤ (8837431669993/25000000000000 : ℝ)^3135 := by
    have hnat : (4566456213 : ℕ)^4159*25000000000000^3135 ≤ 8837431669993^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4566456213 10000000000 8837431669993 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2085996609/5000000000 : ℝ)^4159 ≤ (15678503802063/50000000000000 : ℝ)^3135 := by
    have hnat : (2085996609 : ℕ)^4159*50000000000000^3135 ≤ 15678503802063^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2085996609 5000000000 15678503802063 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4364740983/10000000000 : ℝ), (4566456213/10000000000 : ℝ), (2085996609/5000000000 : ℝ)] ![(33293265696447/100000000000000 : ℝ), (8837431669993/25000000000000 : ℝ), (15678503802063/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4364740983/10000000000 : ℝ)|^4159 ≤ (33293265696447/100000000000000 : ℝ)^3135
        have hw : |(4364740983/10000000000 : ℝ)|=(4364740983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4566456213/10000000000 : ℝ)|^4159 ≤ (8837431669993/25000000000000 : ℝ)^3135
        have hw : |(4566456213/10000000000 : ℝ)|=(4566456213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2085996609/5000000000 : ℝ)|^4159 ≤ (15678503802063/50000000000000 : ℝ)^3135
        have hw : |(2085996609/5000000000 : ℝ)|=(2085996609/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1125_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8277/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (1323/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14827/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8277/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (281/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8277/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (281/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8277/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (281/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8277/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (281/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8277/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (281/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8277/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (281/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (281/3125 : ℝ) ^ (8317/2048 : ℝ) ≤ (1410956606163577/25000000000000000000 : ℝ) := by
    have hpowers : (281/3125 : ℝ)^8317 ≤ (1410956606163577/25000000000000000000 : ℝ)^2048 := by
      have hnat : (281 : ℕ)^8317*25000000000000000000^2048 ≤ 1410956606163577^2048*3125^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        281 3125 1410956606163577 25000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (281/3125 : ℝ)) (X := (1410956606163577/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (8277/50000 : ℝ) ^ (8317/2048 : ℝ) ≤ (33643984742130449/50000000000000000000 : ℝ) := by
    have hpowers : (8277/50000 : ℝ)^8317 ≤ (33643984742130449/50000000000000000000 : ℝ)^2048 := by
      have hnat : (8277 : ℕ)^8317*50000000000000000000^2048 ≤ 33643984742130449^2048*50000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8277 50000 33643984742130449 50000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8277/50000 : ℝ)) (X := (33643984742130449/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12501410956606163577/12500000000000000000 : ℝ) ≤ (2500069484578817/2500000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (12501410956606163577/12500000000000000000 : ℝ)^2048 ≤ (2500069484578817/2500000000000000 : ℝ)^8317 := by
      have hnat : (12501410956606163577 : ℕ)^2048*2500000000000000^8317 ≤ 2500069484578817^8317*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12501410956606163577 12500000000000000000 2500069484578817 2500000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500069484578817/2500000000000000 : ℝ)) (X := (12501410956606163577/12500000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50036465897954457603/50000000000000000000 : ℝ) ≤ (10001795398347771/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (50036465897954457603/50000000000000000000 : ℝ)^2048 ≤ (10001795398347771/10000000000000000 : ℝ)^8317 := by
      have hnat : (50036465897954457603 : ℕ)^2048*10000000000000000^8317 ≤ 10001795398347771^8317*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036465897954457603 50000000000000000000 10001795398347771 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001795398347771/10000000000000000 : ℝ)) (X := (50036465897954457603/50000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25033643984742130449/25000000000000000000 : ℝ) ≤ (5001656429190137/5000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (25033643984742130449/25000000000000000000 : ℝ)^2048 ≤ (5001656429190137/5000000000000000 : ℝ)^8317 := by
      have hnat : (25033643984742130449 : ℕ)^2048*5000000000000000^8317 ≤ 5001656429190137^8317*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25033643984742130449 25000000000000000000 5001656429190137 5000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001656429190137/5000000000000000 : ℝ)) (X := (25033643984742130449/25000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1410956606163577/25000000000000000000 : ℝ) ≤ ((9449351471039440333/9452500000000000000 : ℝ)+2*(1517460032503/756200000000000 : ℝ)*(281/3125 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (9449351471039440333/9452500000000000000 : ℝ)+2*(1517460032503/756200000000000 : ℝ)*(281/3125 : ℝ)=(2500069484578817/2500000000000000 : ℝ) by norm_num, show 1+2*(1410956606163577/25000000000000000000 : ℝ)=(12501410956606163577/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33643984742130449/50000000000000000000 : ℝ)+(1410956606163577/25000000000000000000 : ℝ) ≤ ((9449351471039440333/9452500000000000000 : ℝ)+(1517460032503/756200000000000 : ℝ)*((8277/50000 : ℝ)+(281/3125 : ℝ)))^(8317/2048 : ℝ) := by
    rw [show (9449351471039440333/9452500000000000000 : ℝ)+(1517460032503/756200000000000 : ℝ)*((8277/50000 : ℝ)+(281/3125 : ℝ))=(10001795398347771/10000000000000000 : ℝ) by norm_num, show 1+(33643984742130449/50000000000000000000 : ℝ)+(1410956606163577/25000000000000000000 : ℝ)=(50036465897954457603/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33643984742130449/50000000000000000000 : ℝ) ≤ ((9449351471039440333/9452500000000000000 : ℝ)+2*(1517460032503/756200000000000 : ℝ)*(8277/50000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (9449351471039440333/9452500000000000000 : ℝ)+2*(1517460032503/756200000000000 : ℝ)*(8277/50000 : ℝ)=(5001656429190137/5000000000000000 : ℝ) by norm_num, show 1+2*(33643984742130449/50000000000000000000 : ℝ)=(25033643984742130449/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9449351471039440333/9452500000000000000 : ℝ)*(X 1 0+X 2 0)+(1517460032503/756200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (281/3125 : ℝ)) (hi := (8277/50000 : ℝ)) (c := (9449351471039440333/9452500000000000000 : ℝ)) (alpha := (1517460032503/756200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9449351471039440333/9452500000000000000 : ℝ)*(X 0 1+X 2 1)+(1517460032503/756200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (281/3125 : ℝ)) (hi := (8277/50000 : ℝ)) (c := (9449351471039440333/9452500000000000000 : ℝ)) (alpha := (1517460032503/756200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9449351471039440333/9452500000000000000 : ℝ)*(X 0 2+X 1 2)+(1517460032503/756200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (281/3125 : ℝ)) (hi := (8277/50000 : ℝ)) (c := (9449351471039440333/9452500000000000000 : ℝ)) (alpha := (1517460032503/756200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2171048379/10000000000 : ℝ)*X 0 0+(5430965881/10000000000 : ℝ)*X 0 1+(5230448419/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2677104297/5000000000 : ℝ)*X 1 0+(-2273585059/10000000000 : ℝ)*X 1 1+(5230448339/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2677104347/5000000000 : ℝ)*X 2 0+(5230448441/10000000000 : ℝ)*X 2 1+(-2273584793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4364703661/10000000000 : ℝ)*X 0 0+(166816927/400000000 : ℝ)*X 0 1+(1142004299/2500000000 : ℝ)*X 0 2+(4364703661/10000000000 : ℝ)*X 1 0+(166816927/400000000 : ℝ)*X 1 1+(1142004299/2500000000 : ℝ)*X 1 2+(4364703661/10000000000 : ℝ)*X 2 0+(166816927/400000000 : ℝ)*X 2 1+(1142004299/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-108553369/500000000 : ℝ)*X 0 0+(209249429/400000000 : ℝ)*X 0 1+(1357543517/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060694361/2000000000 : ℝ)*X 1 0+(-518464929/2500000000 : ℝ)*X 1 1+(1357543473/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((165733499/312500000 : ℝ)*X 2 0+(5430173851/10000000000 : ℝ)*X 2 1+(-41477191/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4364740983/10000000000 : ℝ)*X 0 0+(4566456213/10000000000 : ℝ)*X 0 1+(2085996609/5000000000 : ℝ)*X 0 2+(4364740983/10000000000 : ℝ)*X 1 0+(4566456213/10000000000 : ℝ)*X 1 1+(2085996609/5000000000 : ℝ)*X 1 2+(4364740983/10000000000 : ℝ)*X 2 0+(4566456213/10000000000 : ℝ)*X 2 1+(2085996609/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38253230653309575133881/18905000000000000000000000000 : ℝ) := by norm_num
    linear_combination (411644579/50000000000000 : ℝ)*(base19) + (400864041/50000000000000 : ℝ)*(base23) + (14083329/20000000000000 : ℝ)*(lower2) + (124399869/100000000000000 : ℝ)*(upper5) + (1875567821262129/50000000000000 : ℝ)*(major0) + (1875567821262129/50000000000000 : ℝ)*(major1) + (1875567821262129/50000000000000 : ℝ)*(major2) + (498711017147557/10000000000000 : ℝ)*(sp0) + (4987127011163891/100000000000000 : ℝ)*(sp1) + (4987128806803551/100000000000000 : ℝ)*(sp2) + (628783841469749/25000000000000 : ℝ)*(sp3) + (303704001/1562500000000 : ℝ)*(sp4) + (221759823/12500000000000 : ℝ)*(sp5) + (6243189709/100000000000000 : ℝ)*(sp7) + (78598175283397/3125000000000 : ℝ)*(f.failure) + (4987129608531633/100000000000000 : ℝ)*(f.sum) + (33102116796211/9452500000000000000000000000 : ℝ)*base65 + (822259537740761457/472625000000000000000000000000000 : ℝ)*base67 + (1543712117135863543/472625000000000000000000000000000 : ℝ)*base70 + (4946031127257988543/472625000000000000000000000000000 : ℝ)*base72 + (6369464824733/18905000000000000000000000000 : ℝ)*base74 + (4915992254252261457/472625000000000000000000000000000 : ℝ)*base75 + (4562584102164511457/472625000000000000000000000000000 : ℝ)*base77 + (407274598734363543/472625000000000000000000000000000 : ℝ)*base80 + (20098429261697/4726250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (3611/2500000000000000000 : ℝ)*base90 + (3611/2500000000000000000 : ℝ)*base92 + (3611/2500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2517925893595819945984645719/236312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (486206483/25000000000000 : ℝ)*(base19) + (2222730293/100000000000000 : ℝ)*(base23) + (46511931/25000000000000 : ℝ)*(upper3) + (21799617/50000000000000 : ℝ)*(lower4) + (27173831/10000000000000 : ℝ)*(upper5) + (1890444492930281/50000000000000 : ℝ)*(major0) + (1890444492930281/50000000000000 : ℝ)*(major1) + (1890444492930281/50000000000000 : ℝ)*(major2) + (30753913027/100000000000000 : ℝ)*(sp1) + (35060813349/100000000000000 : ℝ)*(sp2) + (628335793730283/12500000000000 : ℝ)*(sp4) + (2513326825551653/50000000000000 : ℝ)*(sp5) + (2513324533149311/50000000000000 : ℝ)*(sp6) + (25350912667099/1000000000000 : ℝ)*(sp7) + (25350912667099/1000000000000 : ℝ)*(f.failure) + (628335793730283/12500000000000 : ℝ)*(f.sum) + (39599933375557/18905000000000000000000000000 : ℝ)*base66 + (7263197084542288927/472625000000000000000000000000000 : ℝ)*base68 + (1003119063631211073/472625000000000000000000000000000 : ℝ)*base69 + (8558843209793288927/472625000000000000000000000000000 : ℝ)*base72 + (3820128373847/4726250000000000000000000000 : ℝ)*base73 + (438101002694586073/472625000000000000000000000000000 : ℝ)*base75 + (3083880976475038927/472625000000000000000000000000000 : ℝ)*base78 + (4644424888543663927/472625000000000000000000000000000 : ℝ)*base80 + (4020014278683/1181562500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (3563/800000000000000000 : ℝ)*base89 + (3563/800000000000000000 : ℝ)*base91 + (3563/800000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1125_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8277/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1323/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14827/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1125_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1125_s4_0 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2174187007/10000000000 : ℝ)*x 0 + (2701363031/5000000000 : ℝ)*x 1 + (1314159011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174187007/10000000000 : ℝ)^4159 ≤ (2641587596001/20000000000000 : ℝ)^3135 := by
    have hnat : (2174187007 : ℕ)^4159*20000000000000^3135 ≤ 2641587596001^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174187007 10000000000 2641587596001 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2701363031/5000000000 : ℝ)^4159 ≤ (2209250918099/5000000000000 : ℝ)^3135 := by
    have hnat : (2701363031 : ℕ)^4159*5000000000000^3135 ≤ 2209250918099^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701363031 5000000000 2209250918099 5000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1314159011/2500000000 : ℝ)^4159 ≤ (21303521816977/50000000000000 : ℝ)^3135 := by
    have hnat : (1314159011 : ℕ)^4159*50000000000000^3135 ≤ 21303521816977^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314159011 2500000000 21303521816977 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2174187007/10000000000 : ℝ), (2701363031/5000000000 : ℝ), (1314159011/2500000000 : ℝ)] ![(2641587596001/20000000000000 : ℝ), (2209250918099/5000000000000 : ℝ), (21303521816977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2174187007/10000000000 : ℝ)|^4159 ≤ (2641587596001/20000000000000 : ℝ)^3135
        have hw : |(-2174187007/10000000000 : ℝ)|=(2174187007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2701363031/5000000000 : ℝ)|^4159 ≤ (2209250918099/5000000000000 : ℝ)^3135
        have hw : |(2701363031/5000000000 : ℝ)|=(2701363031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1314159011/2500000000 : ℝ)|^4159 ≤ (21303521816977/50000000000000 : ℝ)^3135
        have hw : |(1314159011/2500000000 : ℝ)|=(1314159011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s4_1 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069433889/2000000000 : ℝ)*x 0 + (-1124221353/5000000000 : ℝ)*x 1 + (5256636151/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069433889/2000000000 : ℝ)^4159 ≤ (21791633143163/50000000000000 : ℝ)^3135 := by
    have hnat : (1069433889 : ℕ)^4159*50000000000000^3135 ≤ 21791633143163^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069433889 2000000000 21791633143163 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124221353/5000000000 : ℝ)^4159 ≤ (431552778543/3125000000000 : ℝ)^3135 := by
    have hnat : (1124221353 : ℕ)^4159*3125000000000^3135 ≤ 431552778543^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124221353 5000000000 431552778543 3125000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5256636151/10000000000 : ℝ)^4159 ≤ (332867537379/781250000000 : ℝ)^3135 := by
    have hnat : (5256636151 : ℕ)^4159*781250000000^3135 ≤ 332867537379^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256636151 10000000000 332867537379 781250000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069433889/2000000000 : ℝ), (-1124221353/5000000000 : ℝ), (5256636151/10000000000 : ℝ)] ![(21791633143163/50000000000000 : ℝ), (431552778543/3125000000000 : ℝ), (332867537379/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069433889/2000000000 : ℝ)|^4159 ≤ (21791633143163/50000000000000 : ℝ)^3135
        have hw : |(1069433889/2000000000 : ℝ)|=(1069433889/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1124221353/5000000000 : ℝ)|^4159 ≤ (431552778543/3125000000000 : ℝ)^3135
        have hw : |(-1124221353/5000000000 : ℝ)|=(1124221353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5256636151/10000000000 : ℝ)|^4159 ≤ (332867537379/781250000000 : ℝ)^3135
        have hw : |(5256636151/10000000000 : ℝ)|=(5256636151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s4_2 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106943399/200000000 : ℝ)*x 0 + (164269863/312500000 : ℝ)*x 1 + (-2248442741/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106943399/200000000 : ℝ)^4159 ≤ (43583271746903/100000000000000 : ℝ)^3135 := by
    have hnat : (106943399 : ℕ)^4159*100000000000000^3135 ≤ 43583271746903^3135*200000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106943399 200000000 43583271746903 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164269863/312500000 : ℝ)^4159 ≤ (42607039031721/100000000000000 : ℝ)^3135 := by
    have hnat : (164269863 : ℕ)^4159*100000000000000^3135 ≤ 42607039031721^3135*312500000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164269863 312500000 42607039031721 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248442741/10000000000 : ℝ)^4159 ≤ (13809689198557/100000000000000 : ℝ)^3135 := by
    have hnat : (2248442741 : ℕ)^4159*100000000000000^3135 ≤ 13809689198557^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248442741 10000000000 13809689198557 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106943399/200000000 : ℝ), (164269863/312500000 : ℝ), (-2248442741/10000000000 : ℝ)] ![(43583271746903/100000000000000 : ℝ), (42607039031721/100000000000000 : ℝ), (13809689198557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106943399/200000000 : ℝ)|^4159 ≤ (43583271746903/100000000000000 : ℝ)^3135
        have hw : |(106943399/200000000 : ℝ)|=(106943399/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164269863/312500000 : ℝ)|^4159 ≤ (42607039031721/100000000000000 : ℝ)^3135
        have hw : |(164269863/312500000 : ℝ)|=(164269863/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2248442741/10000000000 : ℝ)|^4159 ≤ (13809689198557/100000000000000 : ℝ)^3135
        have hw : |(-2248442741/10000000000 : ℝ)|=(2248442741/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s4_3 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1091644481/2500000000 : ℝ)*x 0 + (1056034829/2500000000 : ℝ)*x 1 + (56422673/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091644481/2500000000 : ℝ)^4159 ≤ (33311855480711/100000000000000 : ℝ)^3135 := by
    have hnat : (1091644481 : ℕ)^4159*100000000000000^3135 ≤ 33311855480711^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091644481 2500000000 33311855480711 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056034829/2500000000 : ℝ)^4159 ≤ (31878019176299/100000000000000 : ℝ)^3135 := by
    have hnat : (1056034829 : ℕ)^4159*100000000000000^3135 ≤ 31878019176299^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056034829 2500000000 31878019176299 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56422673/125000000 : ℝ)^4159 ≤ (4351265665099/12500000000000 : ℝ)^3135 := by
    have hnat : (56422673 : ℕ)^4159*12500000000000^3135 ≤ 4351265665099^3135*125000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56422673 125000000 4351265665099 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091644481/2500000000 : ℝ), (1056034829/2500000000 : ℝ), (56422673/125000000 : ℝ)] ![(33311855480711/100000000000000 : ℝ), (31878019176299/100000000000000 : ℝ), (4351265665099/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091644481/2500000000 : ℝ)|^4159 ≤ (33311855480711/100000000000000 : ℝ)^3135
        have hw : |(1091644481/2500000000 : ℝ)|=(1091644481/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056034829/2500000000 : ℝ)|^4159 ≤ (31878019176299/100000000000000 : ℝ)^3135
        have hw : |(1056034829/2500000000 : ℝ)|=(1056034829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56422673/125000000 : ℝ)|^4159 ≤ (4351265665099/12500000000000 : ℝ)^3135
        have hw : |(56422673/125000000 : ℝ)|=(56422673/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s4_4 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2174194747/10000000000 : ℝ)*x 0 + (131426361/250000000 : ℝ)*x 1 + (1350576409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2174194747/10000000000 : ℝ)^4159 ≤ (132080003579/1000000000000 : ℝ)^3135 := by
    have hnat : (2174194747 : ℕ)^4159*1000000000000^3135 ≤ 132080003579^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2174194747 10000000000 132080003579 1000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131426361/250000000 : ℝ)^4159 ≤ (42611542655123/100000000000000 : ℝ)^3135 := by
    have hnat : (131426361 : ℕ)^4159*100000000000000^3135 ≤ 42611542655123^3135*250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131426361 250000000 42611542655123 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350576409/2500000000 : ℝ)^4159 ≤ (44180456968751/100000000000000 : ℝ)^3135 := by
    have hnat : (1350576409 : ℕ)^4159*100000000000000^3135 ≤ 44180456968751^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350576409 2500000000 44180456968751 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2174194747/10000000000 : ℝ), (131426361/250000000 : ℝ), (1350576409/2500000000 : ℝ)] ![(132080003579/1000000000000 : ℝ), (42611542655123/100000000000000 : ℝ), (44180456968751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2174194747/10000000000 : ℝ)|^4159 ≤ (132080003579/1000000000000 : ℝ)^3135
        have hw : |(-2174194747/10000000000 : ℝ)|=(2174194747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131426361/250000000 : ℝ)|^4159 ≤ (42611542655123/100000000000000 : ℝ)^3135
        have hw : |(131426361/250000000 : ℝ)|=(131426361/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350576409/2500000000 : ℝ)|^4159 ≤ (44180456968751/100000000000000 : ℝ)^3135
        have hw : |(1350576409/2500000000 : ℝ)|=(1350576409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s4_5 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82971973/156250000 : ℝ)*x 0 + (-2102772563/10000000000 : ℝ)*x 1 + (1350576411/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82971973/156250000 : ℝ)^4159 ≤ (4318403450423/10000000000000 : ℝ)^3135 := by
    have hnat : (82971973 : ℕ)^4159*10000000000000^3135 ≤ 4318403450423^3135*156250000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82971973 156250000 4318403450423 10000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2102772563/10000000000 : ℝ)^4159 ≤ (12635508428559/100000000000000 : ℝ)^3135 := by
    have hnat : (2102772563 : ℕ)^4159*100000000000000^3135 ≤ 12635508428559^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2102772563 10000000000 12635508428559 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350576411/2500000000 : ℝ)^4159 ≤ (22090228527773/50000000000000 : ℝ)^3135 := by
    have hnat : (1350576411 : ℕ)^4159*50000000000000^3135 ≤ 22090228527773^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350576411 2500000000 22090228527773 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82971973/156250000 : ℝ), (-2102772563/10000000000 : ℝ), (1350576411/2500000000 : ℝ)] ![(4318403450423/10000000000000 : ℝ), (12635508428559/100000000000000 : ℝ), (22090228527773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82971973/156250000 : ℝ)|^4159 ≤ (4318403450423/10000000000000 : ℝ)^3135
        have hw : |(82971973/156250000 : ℝ)|=(82971973/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2102772563/10000000000 : ℝ)|^4159 ≤ (12635508428559/100000000000000 : ℝ)^3135
        have hw : |(-2102772563/10000000000 : ℝ)|=(2102772563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350576411/2500000000 : ℝ)|^4159 ≤ (22090228527773/50000000000000 : ℝ)^3135
        have hw : |(1350576411/2500000000 : ℝ)|=(1350576411/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s4_6 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5310206303/10000000000 : ℝ)*x 0 + (1080461117/2000000000 : ℝ)*x 1 + (-1051386301/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310206303/10000000000 : ℝ)^4159 ≤ (1727361393547/4000000000000 : ℝ)^3135 := by
    have hnat : (5310206303 : ℕ)^4159*4000000000000^3135 ≤ 1727361393547^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310206303 10000000000 1727361393547 4000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1080461117/2000000000 : ℝ)^4159 ≤ (11045114103859/25000000000000 : ℝ)^3135 := by
    have hnat : (1080461117 : ℕ)^4159*25000000000000^3135 ≤ 11045114103859^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1080461117 2000000000 11045114103859 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1051386301/5000000000 : ℝ)^4159 ≤ (2527101747891/20000000000000 : ℝ)^3135 := by
    have hnat : (1051386301 : ℕ)^4159*20000000000000^3135 ≤ 2527101747891^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051386301 5000000000 2527101747891 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310206303/10000000000 : ℝ), (1080461117/2000000000 : ℝ), (-1051386301/5000000000 : ℝ)] ![(1727361393547/4000000000000 : ℝ), (11045114103859/25000000000000 : ℝ), (2527101747891/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310206303/10000000000 : ℝ)|^4159 ≤ (1727361393547/4000000000000 : ℝ)^3135
        have hw : |(5310206303/10000000000 : ℝ)|=(5310206303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1080461117/2000000000 : ℝ)|^4159 ≤ (11045114103859/25000000000000 : ℝ)^3135
        have hw : |(1080461117/2000000000 : ℝ)|=(1080461117/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1051386301/5000000000 : ℝ)|^4159 ≤ (2527101747891/20000000000000 : ℝ)^3135
        have hw : |(-1051386301/5000000000 : ℝ)|=(1051386301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s4_7 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1091648037/2500000000 : ℝ)*x 0 + (4512983529/10000000000 : ℝ)*x 1 + (4224973381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1091648037/2500000000 : ℝ)^4159 ≤ (6662399887421/20000000000000 : ℝ)^3135 := by
    have hnat : (1091648037 : ℕ)^4159*20000000000000^3135 ≤ 6662399887421^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091648037 2500000000 6662399887421 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4512983529/10000000000 : ℝ)^4159 ≤ (8700407689349/25000000000000 : ℝ)^3135 := by
    have hnat : (4512983529 : ℕ)^4159*25000000000000^3135 ≤ 8700407689349^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4512983529 10000000000 8700407689349 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4224973381/10000000000 : ℝ)^4159 ≤ (31886369789559/100000000000000 : ℝ)^3135 := by
    have hnat : (4224973381 : ℕ)^4159*100000000000000^3135 ≤ 31886369789559^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4224973381 10000000000 31886369789559 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1091648037/2500000000 : ℝ), (4512983529/10000000000 : ℝ), (4224973381/10000000000 : ℝ)] ![(6662399887421/20000000000000 : ℝ), (8700407689349/25000000000000 : ℝ), (31886369789559/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1091648037/2500000000 : ℝ)|^4159 ≤ (6662399887421/20000000000000 : ℝ)^3135
        have hw : |(1091648037/2500000000 : ℝ)|=(1091648037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4512983529/10000000000 : ℝ)|^4159 ≤ (8700407689349/25000000000000 : ℝ)^3135
        have hw : |(4512983529/10000000000 : ℝ)|=(4512983529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4224973381/10000000000 : ℝ)|^4159 ≤ (31886369789559/100000000000000 : ℝ)^3135
        have hw : |(4224973381/10000000000 : ℝ)|=(4224973381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1125_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14827/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1323/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11143/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14827/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1323/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14827/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1323/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14827/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1323/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14827/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1323/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14827/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1323/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14827/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1323/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (1323/12500 : ℝ) ^ (8317/2048 : ℝ) ≤ (2188258733426609/20000000000000000000 : ℝ) := by
    have hpowers : (1323/12500 : ℝ)^8317 ≤ (2188258733426609/20000000000000000000 : ℝ)^2048 := by
      have hnat : (1323 : ℕ)^8317*20000000000000000000^2048 ≤ 2188258733426609^2048*12500^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1323 12500 2188258733426609 20000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1323/12500 : ℝ)) (X := (2188258733426609/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14827/100000 : ℝ) ^ (8317/2048 : ℝ) ≤ (8602966936312503/20000000000000000000 : ℝ) := by
    have hpowers : (14827/100000 : ℝ)^8317 ≤ (8602966936312503/20000000000000000000 : ℝ)^2048 := by
      have hnat : (14827 : ℕ)^8317*20000000000000000000^2048 ≤ 8602966936312503^2048*100000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14827 100000 8602966936312503 20000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14827/100000 : ℝ)) (X := (8602966936312503/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002188258733426609/10000000000000000000 : ℝ) ≤ (10000538798164719/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (10002188258733426609/10000000000000000000 : ℝ)^2048 ≤ (10000538798164719/10000000000000000 : ℝ)^8317 := by
      have hnat : (10002188258733426609 : ℕ)^2048*10000000000000000^8317 ≤ 10000538798164719^8317*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002188258733426609 10000000000000000000 10000538798164719 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000538798164719/10000000000000000 : ℝ)) (X := (10002188258733426609/10000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (2501348903208717389/2500000000000000000 : ℝ) ≤ (5000664179917189/5000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (2501348903208717389/2500000000000000000 : ℝ)^2048 ≤ (5000664179917189/5000000000000000 : ℝ)^8317 := by
      have hnat : (2501348903208717389 : ℕ)^2048*5000000000000000^8317 ≤ 5000664179917189^8317*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501348903208717389 2500000000000000000 5000664179917189 5000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000664179917189/5000000000000000 : ℝ)) (X := (2501348903208717389/2500000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10008602966936312503/10000000000000000000 : ℝ) ≤ (10002117921504037/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (10008602966936312503/10000000000000000000 : ℝ)^2048 ≤ (10002117921504037/10000000000000000 : ℝ)^8317 := by
      have hnat : (10008602966936312503 : ℕ)^2048*10000000000000000^8317 ≤ 10002117921504037^8317*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10008602966936312503 10000000000000000000 10002117921504037 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002117921504037/10000000000000000 : ℝ)) (X := (10008602966936312503/10000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2188258733426609/20000000000000000000 : ℝ) ≤ ((8483114535837912201/8486000000000000000 : ℝ)+2*(789561669659/424300000000000 : ℝ)*(1323/12500 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (8483114535837912201/8486000000000000000 : ℝ)+2*(789561669659/424300000000000 : ℝ)*(1323/12500 : ℝ)=(10000538798164719/10000000000000000 : ℝ) by norm_num, show 1+2*(2188258733426609/20000000000000000000 : ℝ)=(10002188258733426609/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8602966936312503/20000000000000000000 : ℝ)+(2188258733426609/20000000000000000000 : ℝ) ≤ ((8483114535837912201/8486000000000000000 : ℝ)+(789561669659/424300000000000 : ℝ)*((14827/100000 : ℝ)+(1323/12500 : ℝ)))^(8317/2048 : ℝ) := by
    rw [show (8483114535837912201/8486000000000000000 : ℝ)+(789561669659/424300000000000 : ℝ)*((14827/100000 : ℝ)+(1323/12500 : ℝ))=(5000664179917189/5000000000000000 : ℝ) by norm_num, show 1+(8602966936312503/20000000000000000000 : ℝ)+(2188258733426609/20000000000000000000 : ℝ)=(2501348903208717389/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8602966936312503/20000000000000000000 : ℝ) ≤ ((8483114535837912201/8486000000000000000 : ℝ)+2*(789561669659/424300000000000 : ℝ)*(14827/100000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (8483114535837912201/8486000000000000000 : ℝ)+2*(789561669659/424300000000000 : ℝ)*(14827/100000 : ℝ)=(10002117921504037/10000000000000000 : ℝ) by norm_num, show 1+2*(8602966936312503/20000000000000000000 : ℝ)=(10008602966936312503/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8483114535837912201/8486000000000000000 : ℝ)*(X 1 0+X 2 0)+(789561669659/424300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (1323/12500 : ℝ)) (hi := (14827/100000 : ℝ)) (c := (8483114535837912201/8486000000000000000 : ℝ)) (alpha := (789561669659/424300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8483114535837912201/8486000000000000000 : ℝ)*(X 0 1+X 2 1)+(789561669659/424300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (1323/12500 : ℝ)) (hi := (14827/100000 : ℝ)) (c := (8483114535837912201/8486000000000000000 : ℝ)) (alpha := (789561669659/424300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8483114535837912201/8486000000000000000 : ℝ)*(X 0 2+X 1 2)+(789561669659/424300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (1323/12500 : ℝ)) (hi := (14827/100000 : ℝ)) (c := (8483114535837912201/8486000000000000000 : ℝ)) (alpha := (789561669659/424300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2174187007/10000000000 : ℝ)*X 0 0+(2701363031/5000000000 : ℝ)*X 0 1+(1314159011/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069433889/2000000000 : ℝ)*X 1 0+(-1124221353/5000000000 : ℝ)*X 1 1+(5256636151/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((106943399/200000000 : ℝ)*X 2 0+(164269863/312500000 : ℝ)*X 2 1+(-2248442741/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1091644481/2500000000 : ℝ)*X 0 0+(1056034829/2500000000 : ℝ)*X 0 1+(56422673/125000000 : ℝ)*X 0 2+(1091644481/2500000000 : ℝ)*X 1 0+(1056034829/2500000000 : ℝ)*X 1 1+(56422673/125000000 : ℝ)*X 1 2+(1091644481/2500000000 : ℝ)*X 2 0+(1056034829/2500000000 : ℝ)*X 2 1+(56422673/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2174194747/10000000000 : ℝ)*X 0 0+(131426361/250000000 : ℝ)*X 0 1+(1350576409/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((82971973/156250000 : ℝ)*X 1 0+(-2102772563/10000000000 : ℝ)*X 1 1+(1350576411/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310206303/10000000000 : ℝ)*X 2 0+(1080461117/2000000000 : ℝ)*X 2 1+(-1051386301/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1091648037/2500000000 : ℝ)*X 0 0+(4512983529/10000000000 : ℝ)*X 0 1+(4224973381/10000000000 : ℝ)*X 0 2+(1091648037/2500000000 : ℝ)*X 1 0+(4512983529/10000000000 : ℝ)*X 1 1+(4224973381/10000000000 : ℝ)*X 1 2+(1091648037/2500000000 : ℝ)*X 2 0+(4512983529/10000000000 : ℝ)*X 2 1+(4224973381/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (640392510268405098656237313/212150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (56621181/100000000000000 : ℝ)*(base8) + (41292713/25000000000000 : ℝ)*(base21) + (98325201/50000000000000 : ℝ)*(base29) + (22643129/6250000000000 : ℝ)*(lower2) + (9474199/100000000000000 : ℝ)*(upper4) + (1029723100106091/20000000000000 : ℝ)*(major0) + (2574307848590429/50000000000000 : ℝ)*(major1) + (2574307848590429/50000000000000 : ℝ)*(major2) + (3422538664386501/50000000000000 : ℝ)*(sp0) + (6845077188743781/100000000000000 : ℝ)*(sp1) + (3422531645130499/50000000000000 : ℝ)*(sp2) + (1726074208291557/50000000000000 : ℝ)*(sp3) + (13733311929/100000000000000 : ℝ)*(sp6) + (686470619/12500000000000 : ℝ)*(sp7) + (1726076954174033/50000000000000 : ℝ)*(f.failure) + (6845077385394183/100000000000000 : ℝ)*(f.sum) + (26849724290153/1325937500000000000000000000 : ℝ)*base66 + (1744388663685655771/424300000000000000000000000000000 : ℝ)*base68 + (1534321357177144229/424300000000000000000000000000000 : ℝ)*base69 + (1322215926039435709/169720000000000000000000000000000 : ℝ)*base72 + (183746243105513/42430000000000000000000000000 : ℝ)*base74 + (4983874316666474229/424300000000000000000000000000000 : ℝ)*base75 + (7349368304392324291/169720000000000000000000000000000 : ℝ)*base77 + (4528792852839874229/424300000000000000000000000000000 : ℝ)*base79 + (55114228970987/42430000000000000000000000000 : ℝ)*base81 + (1/50000000000000 : ℝ)*base88 + (411521/40000000000000000000 : ℝ)*base89 + (11521/40000000000000000000 : ℝ)*base91 + (11521/40000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (544234987694877684119269023/106075000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (912622313/100000000000000 : ℝ)*(base19) + (494305973/50000000000000 : ℝ)*(base23) + (3447593/5000000000000 : ℝ)*(upper3) + (6151803/25000000000000 : ℝ)*(lower4) + (98267611/100000000000000 : ℝ)*(upper5) + (2589181301533859/50000000000000 : ℝ)*(major0) + (2589181301533859/50000000000000 : ℝ)*(major1) + (2589181301533859/50000000000000 : ℝ)*(major2) + (12224649091/50000000000000 : ℝ)*(sp1) + (2293466269/10000000000000 : ℝ)*(sp2) + (3442312892721399/50000000000000 : ℝ)*(sp4) + (3442300211761151/50000000000000 : ℝ)*(sp5) + (6884601862168161/100000000000000 : ℝ)*(sp6) + (434012406208819/12500000000000 : ℝ)*(sp7) + (434012406208819/12500000000000 : ℝ)*(f.failure) + (3442312892721399/50000000000000 : ℝ)*(f.sum) + (11561909650789/2651875000000000000000000000 : ℝ)*base65 + (7166678541933659/424300000000000000000000000000000 : ℝ)*base67 + (136851226759666341/424300000000000000000000000000000 : ℝ)*base70 + (7125014849383333659/424300000000000000000000000000000 : ℝ)*base71 + (7541051870547/5303750000000000000000000000 : ℝ)*base74 + (4893971853699733659/424300000000000000000000000000000 : ℝ)*base75 + (7020824951062633659/424300000000000000000000000000000 : ℝ)*base77 + (2133790905090433659/424300000000000000000000000000000 : ℝ)*base79 + (47641734488331/10607500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (124797/10000000000000000000 : ℝ)*base90 + (124797/10000000000000000000 : ℝ)*base92 + (124797/10000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1125_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14827/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1323/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1125_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1125_s5_0 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-217486571/1000000000 : ℝ)*x 0 + (5395362227/10000000000 : ℝ)*x 1 + (657944283/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (217486571/1000000000 : ℝ)^4159 ≤ (6606704015707/50000000000000 : ℝ)^3135 := by
    have hnat : (217486571 : ℕ)^4159*50000000000000^3135 ≤ 6606704015707^3135*1000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217486571 1000000000 6606704015707 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395362227/10000000000 : ℝ)^4159 ≤ (11026285383869/25000000000000 : ℝ)^3135 := by
    have hnat : (5395362227 : ℕ)^4159*25000000000000^3135 ≤ 11026285383869^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395362227 10000000000 11026285383869 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657944283/1250000000 : ℝ)^4159 ≤ (4268145042003/10000000000000 : ℝ)^3135 := by
    have hnat : (657944283 : ℕ)^4159*10000000000000^3135 ≤ 4268145042003^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657944283 1250000000 4268145042003 10000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-217486571/1000000000 : ℝ), (5395362227/10000000000 : ℝ), (657944283/1250000000 : ℝ)] ![(6606704015707/50000000000000 : ℝ), (11026285383869/25000000000000 : ℝ), (4268145042003/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-217486571/1000000000 : ℝ)|^4159 ≤ (6606704015707/50000000000000 : ℝ)^3135
        have hw : |(-217486571/1000000000 : ℝ)|=(217486571/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395362227/10000000000 : ℝ)|^4159 ≤ (11026285383869/25000000000000 : ℝ)^3135
        have hw : |(5395362227/10000000000 : ℝ)|=(5395362227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657944283/1250000000 : ℝ)|^4159 ≤ (4268145042003/10000000000000 : ℝ)^3135
        have hw : |(657944283/1250000000 : ℝ)|=(657944283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s5_1 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345325803/10000000000 : ℝ)*x 0 + (-1120877227/5000000000 : ℝ)*x 1 + (657944263/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345325803/10000000000 : ℝ)^4159 ≤ (8712666412421/20000000000000 : ℝ)^3135 := by
    have hnat : (5345325803 : ℕ)^4159*20000000000000^3135 ≤ 8712666412421^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345325803 10000000000 8712666412421 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1120877227/5000000000 : ℝ)^4159 ≤ (13755219224099/100000000000000 : ℝ)^3135 := by
    have hnat : (1120877227 : ℕ)^4159*100000000000000^3135 ≤ 13755219224099^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120877227 5000000000 13755219224099 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (657944263/1250000000 : ℝ)^4159 ≤ (42681448698829/100000000000000 : ℝ)^3135 := by
    have hnat : (657944263 : ℕ)^4159*100000000000000^3135 ≤ 42681448698829^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657944263 1250000000 42681448698829 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345325803/10000000000 : ℝ), (-1120877227/5000000000 : ℝ), (657944263/1250000000 : ℝ)] ![(8712666412421/20000000000000 : ℝ), (13755219224099/100000000000000 : ℝ), (42681448698829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345325803/10000000000 : ℝ)|^4159 ≤ (8712666412421/20000000000000 : ℝ)^3135
        have hw : |(5345325803/10000000000 : ℝ)|=(5345325803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1120877227/5000000000 : ℝ)|^4159 ≤ (13755219224099/100000000000000 : ℝ)^3135
        have hw : |(-1120877227/5000000000 : ℝ)|=(1120877227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(657944263/1250000000 : ℝ)|^4159 ≤ (42681448698829/100000000000000 : ℝ)^3135
        have hw : |(657944263/1250000000 : ℝ)|=(657944263/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s5_2 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672662673/5000000000 : ℝ)*x 0 + (2631777231/5000000000 : ℝ)*x 1 + (-560438647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672662673/5000000000 : ℝ)^4159 ≤ (43563327121109/100000000000000 : ℝ)^3135 := by
    have hnat : (2672662673 : ℕ)^4159*100000000000000^3135 ≤ 43563327121109^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672662673 5000000000 43563327121109 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2631777231/5000000000 : ℝ)^4159 ≤ (8536290510003/20000000000000 : ℝ)^3135 := by
    have hnat : (2631777231 : ℕ)^4159*20000000000000^3135 ≤ 8536290510003^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2631777231 5000000000 8536290510003 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (560438647/2500000000 : ℝ)^4159 ≤ (110041762519/800000000000 : ℝ)^3135 := by
    have hnat : (560438647 : ℕ)^4159*800000000000^3135 ≤ 110041762519^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      560438647 2500000000 110041762519 800000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672662673/5000000000 : ℝ), (2631777231/5000000000 : ℝ), (-560438647/2500000000 : ℝ)] ![(43563327121109/100000000000000 : ℝ), (8536290510003/20000000000000 : ℝ), (110041762519/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672662673/5000000000 : ℝ)|^4159 ≤ (43563327121109/100000000000000 : ℝ)^3135
        have hw : |(2672662673/5000000000 : ℝ)|=(2672662673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2631777231/5000000000 : ℝ)|^4159 ≤ (8536290510003/20000000000000 : ℝ)^3135
        have hw : |(2631777231/5000000000 : ℝ)|=(2631777231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-560438647/2500000000 : ℝ)|^4159 ≤ (110041762519/800000000000 : ℝ)^3135
        have hw : |(-560438647/2500000000 : ℝ)|=(560438647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s5_3 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (436697193/1000000000 : ℝ)*x 0 + (105956207/250000000 : ℝ)*x 1 + (4499602651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436697193/1000000000 : ℝ)^4159 ≤ (6663168628321/20000000000000 : ℝ)^3135 := by
    have hnat : (436697193 : ℕ)^4159*20000000000000^3135 ≤ 6663168628321^3135*1000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436697193 1000000000 6663168628321 20000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105956207/250000000 : ℝ)^4159 ≤ (32019349794197/100000000000000 : ℝ)^3135 := by
    have hnat : (105956207 : ℕ)^4159*100000000000000^3135 ≤ 32019349794197^3135*250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105956207 250000000 32019349794197 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4499602651/10000000000 : ℝ)^4159 ≤ (17332403526833/50000000000000 : ℝ)^3135 := by
    have hnat : (4499602651 : ℕ)^4159*50000000000000^3135 ≤ 17332403526833^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499602651 10000000000 17332403526833 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436697193/1000000000 : ℝ), (105956207/250000000 : ℝ), (4499602651/10000000000 : ℝ)] ![(6663168628321/20000000000000 : ℝ), (32019349794197/100000000000000 : ℝ), (17332403526833/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436697193/1000000000 : ℝ)|^4159 ≤ (6663168628321/20000000000000 : ℝ)^3135
        have hw : |(436697193/1000000000 : ℝ)|=(436697193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(105956207/250000000 : ℝ)|^4159 ≤ (32019349794197/100000000000000 : ℝ)^3135
        have hw : |(105956207/250000000 : ℝ)|=(105956207/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4499602651/10000000000 : ℝ)|^4159 ≤ (17332403526833/50000000000000 : ℝ)^3135
        have hw : |(4499602651/10000000000 : ℝ)|=(4499602651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s5_4 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-434974101/2000000000 : ℝ)*x 0 + (5263895581/10000000000 : ℝ)*x 1 + (1079004017/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434974101/2000000000 : ℝ)^4159 ≤ (1651680834877/12500000000000 : ℝ)^3135 := by
    have hnat : (434974101 : ℕ)^4159*12500000000000^3135 ≤ 1651680834877^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434974101 2000000000 1651680834877 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5263895581/10000000000 : ℝ)^4159 ≤ (21342561088631/50000000000000 : ℝ)^3135 := by
    have hnat : (5263895581 : ℕ)^4159*50000000000000^3135 ≤ 21342561088631^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5263895581 10000000000 21342561088631 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079004017/2000000000 : ℝ)^4159 ≤ (22050715562831/50000000000000 : ℝ)^3135 := by
    have hnat : (1079004017 : ℕ)^4159*50000000000000^3135 ≤ 22050715562831^3135*2000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079004017 2000000000 22050715562831 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-434974101/2000000000 : ℝ), (5263895581/10000000000 : ℝ), (1079004017/2000000000 : ℝ)] ![(1651680834877/12500000000000 : ℝ), (21342561088631/50000000000000 : ℝ), (22050715562831/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-434974101/2000000000 : ℝ)|^4159 ≤ (1651680834877/12500000000000 : ℝ)^3135
        have hw : |(-434974101/2000000000 : ℝ)|=(434974101/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5263895581/10000000000 : ℝ)|^4159 ≤ (21342561088631/50000000000000 : ℝ)^3135
        have hw : |(5263895581/10000000000 : ℝ)|=(5263895581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079004017/2000000000 : ℝ)|^4159 ≤ (22050715562831/50000000000000 : ℝ)^3135
        have hw : |(1079004017/2000000000 : ℝ)|=(1079004017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s5_5 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5311974251/10000000000 : ℝ)*x 0 + (-263786103/1250000000 : ℝ)*x 1 + (5395019947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5311974251/10000000000 : ℝ)^4159 ≤ (2160155473819/5000000000000 : ℝ)^3135 := by
    have hnat : (5311974251 : ℕ)^4159*5000000000000^3135 ≤ 2160155473819^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5311974251 10000000000 2160155473819 5000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263786103/1250000000 : ℝ)^4159 ≤ (12695460873507/100000000000000 : ℝ)^3135 := by
    have hnat : (263786103 : ℕ)^4159*100000000000000^3135 ≤ 12695460873507^3135*1250000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263786103 1250000000 12695460873507 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5395019947/10000000000 : ℝ)^4159 ≤ (11025357407279/25000000000000 : ℝ)^3135 := by
    have hnat : (5395019947 : ℕ)^4159*25000000000000^3135 ≤ 11025357407279^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395019947 10000000000 11025357407279 25000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5311974251/10000000000 : ℝ), (-263786103/1250000000 : ℝ), (5395019947/10000000000 : ℝ)] ![(2160155473819/5000000000000 : ℝ), (12695460873507/100000000000000 : ℝ), (11025357407279/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5311974251/10000000000 : ℝ)|^4159 ≤ (2160155473819/5000000000000 : ℝ)^3135
        have hw : |(5311974251/10000000000 : ℝ)|=(5311974251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-263786103/1250000000 : ℝ)|^4159 ≤ (12695460873507/100000000000000 : ℝ)^3135
        have hw : |(-263786103/1250000000 : ℝ)|=(263786103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5395019947/10000000000 : ℝ)|^4159 ≤ (11025357407279/25000000000000 : ℝ)^3135
        have hw : |(5395019947/10000000000 : ℝ)|=(5395019947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s5_6 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655987063/5000000000 : ℝ)*x 0 + (5395020087/10000000000 : ℝ)*x 1 + (-527572201/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655987063/5000000000 : ℝ)^4159 ≤ (2700194257979/6250000000000 : ℝ)^3135 := by
    have hnat : (2655987063 : ℕ)^4159*6250000000000^3135 ≤ 2700194257979^3135*5000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655987063 5000000000 2700194257979 6250000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5395020087/10000000000 : ℝ)^4159 ≤ (5512678893419/12500000000000 : ℝ)^3135 := by
    have hnat : (5395020087 : ℕ)^4159*12500000000000^3135 ≤ 5512678893419^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5395020087 10000000000 5512678893419 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (527572201/2500000000 : ℝ)^4159 ≤ (12695460713887/100000000000000 : ℝ)^3135 := by
    have hnat : (527572201 : ℕ)^4159*100000000000000^3135 ≤ 12695460713887^3135*2500000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527572201 2500000000 12695460713887 100000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655987063/5000000000 : ℝ), (5395020087/10000000000 : ℝ), (-527572201/2500000000 : ℝ)] ![(2700194257979/6250000000000 : ℝ), (5512678893419/12500000000000 : ℝ), (12695460713887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655987063/5000000000 : ℝ)|^4159 ≤ (2700194257979/6250000000000 : ℝ)^3135
        have hw : |(2655987063/5000000000 : ℝ)|=(2655987063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5395020087/10000000000 : ℝ)|^4159 ≤ (5512678893419/12500000000000 : ℝ)^3135
        have hw : |(5395020087/10000000000 : ℝ)|=(5395020087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-527572201/2500000000 : ℝ)|^4159 ≤ (12695460713887/100000000000000 : ℝ)^3135
        have hw : |(-527572201/2500000000 : ℝ)|=(527572201/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1125_s5_7 (p : ℝ) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4366982513/10000000000 : ℝ)*x 0 + (4498926523/10000000000 : ℝ)*x 1 + (4238927031/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366982513/10000000000 : ℝ)^4159 ≤ (16657975125893/50000000000000 : ℝ)^3135 := by
    have hnat : (4366982513 : ℕ)^4159*50000000000000^3135 ≤ 16657975125893^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366982513 10000000000 16657975125893 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498926523/10000000000 : ℝ)^4159 ≤ (17328948477397/50000000000000 : ℝ)^3135 := by
    have hnat : (4498926523 : ℕ)^4159*50000000000000^3135 ≤ 17328948477397^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498926523 10000000000 17328948477397 50000000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238927031/10000000000 : ℝ)^4159 ≤ (4003269097041/12500000000000 : ℝ)^3135 := by
    have hnat : (4238927031 : ℕ)^4159*12500000000000^3135 ≤ 4003269097041^3135*10000000000^4159 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238927031 10000000000 4003269097041 12500000000000 4159 3135 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4159/1024 : ℝ)) 4159 3135 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366982513/10000000000 : ℝ), (4498926523/10000000000 : ℝ), (4238927031/10000000000 : ℝ)] ![(16657975125893/50000000000000 : ℝ), (17328948477397/50000000000000 : ℝ), (4003269097041/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366982513/10000000000 : ℝ)|^4159 ≤ (16657975125893/50000000000000 : ℝ)^3135
        have hw : |(4366982513/10000000000 : ℝ)|=(4366982513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498926523/10000000000 : ℝ)|^4159 ≤ (17328948477397/50000000000000 : ℝ)^3135
        have hw : |(4498926523/10000000000 : ℝ)|=(4498926523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238927031/10000000000 : ℝ)|^4159 ≤ (4003269097041/12500000000000 : ℝ)^3135
        have hw : |(4238927031/10000000000 : ℝ)|=(4238927031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1125_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1129/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7041/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11143/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11143/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11143/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11143/100000 : ℝ) ^ (8317/2048 : ℝ) ≤ (2696945335869821/20000000000000000000 : ℝ) := by
    have hpowers : (11143/100000 : ℝ)^8317 ≤ (2696945335869821/20000000000000000000 : ℝ)^2048 := by
      have hnat : (11143 : ℕ)^8317*20000000000000000000^2048 ≤ 2696945335869821^2048*100000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11143 100000 2696945335869821 20000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11143/100000 : ℝ)) (X := (2696945335869821/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (8317/2048 : ℝ) ≤ (36465218513298333/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^8317 ≤ (36465218513298333/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3559 : ℕ)^8317*100000000000000000000^2048 ≤ 36465218513298333^2048*25000^8317 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 36465218513298333 100000000000000000000 8317 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (36465218513298333/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002696945335869821/10000000000000000000 : ℝ) ≤ (2500166008859323/2500000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (10002696945335869821/10000000000000000000 : ℝ)^2048 ≤ (2500166008859323/2500000000000000 : ℝ)^8317 := by
      have hnat : (10002696945335869821 : ℕ)^2048*2500000000000000^8317 ≤ 2500166008859323^8317*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002696945335869821 10000000000000000000 2500166008859323 2500000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500166008859323/2500000000000000 : ℝ)) (X := (10002696945335869821/10000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50024974972596323719/50000000000000000000 : ℝ) ≤ (10001229749137943/10000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (50024974972596323719/50000000000000000000 : ℝ)^2048 ≤ (10001229749137943/10000000000000000 : ℝ)^8317 := by
      have hnat : (50024974972596323719 : ℕ)^2048*10000000000000000^8317 ≤ 10001229749137943^8317*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024974972596323719 50000000000000000000 10001229749137943 10000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001229749137943/10000000000000000 : ℝ)) (X := (50024974972596323719/50000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036465218513298333/50000000000000000000 : ℝ) ≤ (5000897731419297/5000000000000000 : ℝ) ^ (8317/2048 : ℝ) := by
    have hpowers : (50036465218513298333/50000000000000000000 : ℝ)^2048 ≤ (5000897731419297/5000000000000000 : ℝ)^8317 := by
      have hnat : (50036465218513298333 : ℕ)^2048*5000000000000000^8317 ≤ 5000897731419297^8317*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036465218513298333 50000000000000000000 5000897731419297 5000000000000000 2048 8317 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000897731419297/5000000000000000 : ℝ)) (X := (50036465218513298333/50000000000000000000 : ℝ)) (by norm_num) 8317 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2696945335869821/20000000000000000000 : ℝ) ≤ ((3091944636607483597/3093000000000000000 : ℝ)+2*(565713700651/309300000000000 : ℝ)*(11143/100000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (3091944636607483597/3093000000000000000 : ℝ)+2*(565713700651/309300000000000 : ℝ)*(11143/100000 : ℝ)=(2500166008859323/2500000000000000 : ℝ) by norm_num, show 1+2*(2696945335869821/20000000000000000000 : ℝ)=(10002696945335869821/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36465218513298333/100000000000000000000 : ℝ)+(2696945335869821/20000000000000000000 : ℝ) ≤ ((3091944636607483597/3093000000000000000 : ℝ)+(565713700651/309300000000000 : ℝ)*((3559/25000 : ℝ)+(11143/100000 : ℝ)))^(8317/2048 : ℝ) := by
    rw [show (3091944636607483597/3093000000000000000 : ℝ)+(565713700651/309300000000000 : ℝ)*((3559/25000 : ℝ)+(11143/100000 : ℝ))=(10001229749137943/10000000000000000 : ℝ) by norm_num, show 1+(36465218513298333/100000000000000000000 : ℝ)+(2696945335869821/20000000000000000000 : ℝ)=(50024974972596323719/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36465218513298333/100000000000000000000 : ℝ) ≤ ((3091944636607483597/3093000000000000000 : ℝ)+2*(565713700651/309300000000000 : ℝ)*(3559/25000 : ℝ))^(8317/2048 : ℝ) := by
    rw [show (3091944636607483597/3093000000000000000 : ℝ)+2*(565713700651/309300000000000 : ℝ)*(3559/25000 : ℝ)=(5000897731419297/5000000000000000 : ℝ) by norm_num, show 1+2*(36465218513298333/100000000000000000000 : ℝ)=(50036465218513298333/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3091944636607483597/3093000000000000000 : ℝ)*(X 1 0+X 2 0)+(565713700651/309300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3091944636607483597/3093000000000000000 : ℝ)) (alpha := (565713700651/309300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3091944636607483597/3093000000000000000 : ℝ)*(X 0 1+X 2 1)+(565713700651/309300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3091944636607483597/3093000000000000000 : ℝ)) (alpha := (565713700651/309300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3091944636607483597/3093000000000000000 : ℝ)*(X 0 2+X 1 2)+(565713700651/309300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8317/2048 : ℝ)) (lo := (11143/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3091944636607483597/3093000000000000000 : ℝ)) (alpha := (565713700651/309300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-217486571/1000000000 : ℝ)*X 0 0+(5395362227/10000000000 : ℝ)*X 0 1+(657944283/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345325803/10000000000 : ℝ)*X 1 0+(-1120877227/5000000000 : ℝ)*X 1 1+(657944263/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672662673/5000000000 : ℝ)*X 2 0+(2631777231/5000000000 : ℝ)*X 2 1+(-560438647/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436697193/1000000000 : ℝ)*X 0 0+(105956207/250000000 : ℝ)*X 0 1+(4499602651/10000000000 : ℝ)*X 0 2+(436697193/1000000000 : ℝ)*X 1 0+(105956207/250000000 : ℝ)*X 1 1+(4499602651/10000000000 : ℝ)*X 1 2+(436697193/1000000000 : ℝ)*X 2 0+(105956207/250000000 : ℝ)*X 2 1+(4499602651/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-434974101/2000000000 : ℝ)*X 0 0+(5263895581/10000000000 : ℝ)*X 0 1+(1079004017/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5311974251/10000000000 : ℝ)*X 1 0+(-263786103/1250000000 : ℝ)*X 1 1+(5395019947/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655987063/5000000000 : ℝ)*X 2 0+(5395020087/10000000000 : ℝ)*X 2 1+(-527572201/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4366982513/10000000000 : ℝ)*X 0 0+(4498926523/10000000000 : ℝ)*X 0 1+(4238927031/10000000000 : ℝ)*X 0 2+(4366982513/10000000000 : ℝ)*X 1 0+(4498926523/10000000000 : ℝ)*X 1 1+(4238927031/10000000000 : ℝ)*X 1 2+(4366982513/10000000000 : ℝ)*X 2 0+(4498926523/10000000000 : ℝ)*X 2 1+(4238927031/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1125_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (362352549399886798938147/64437500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1993359753/100000000000000 : ℝ)*(base19) + (629388969/50000000000000 : ℝ)*(base23) + (13872457/12500000000000 : ℝ)*(upper2) + (391912787/100000000000000 : ℝ)*(upper3) + (156917011/100000000000000 : ℝ)*(upper4) + (28532878513323/500000000000 : ℝ)*(major0) + (28532878513323/500000000000 : ℝ)*(major1) + (28532878513323/500000000000 : ℝ)*(major2) + (379342579306291/5000000000000 : ℝ)*(sp0) + (7586882364867579/100000000000000 : ℝ)*(sp1) + (7586883099449393/100000000000000 : ℝ)*(sp2) + (1913121130967827/50000000000000 : ℝ)*(sp3) + (32772101511/100000000000000 : ℝ)*(sp4) + (24597722273/100000000000000 : ℝ)*(sp7) + (478283357457241/12500000000000 : ℝ)*(f.failure) + (7586884358227331/100000000000000 : ℝ)*(f.sum) + (738126060103/515500000000000000000000000 : ℝ)*base65 + (8234632090149277/515500000000000000000000000000 : ℝ)*base67 + (7191580111518277/515500000000000000000000000000 : ℝ)*base69 + (1991927463371277/515500000000000000000000000000 : ℝ)*base71 + (1181599915383/1031000000000000000000000000 : ℝ)*base74 + (7374722603147223/515500000000000000000000000000 : ℝ)*base76 + (2847464645235777/515500000000000000000000000000 : ℝ)*base77 + (2082336750856777/515500000000000000000000000000 : ℝ)*base79 + (2871838341517/1031000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (155017/10000000000000000000 : ℝ)*base89 + (155017/10000000000000000000 : ℝ)*base91 + (155017/10000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (50366205644003037505206609/5155000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15039077/1562500000000 : ℝ)*(base19) + (1181632237/100000000000000 : ℝ)*(base23) + (6815541/12500000000000 : ℝ)*(upper3) + (174118297/100000000000000 : ℝ)*(lower4) + (573624606868601/10000000000000 : ℝ)*(major0) + (573624606868601/10000000000000 : ℝ)*(major1) + (573624606868601/10000000000000 : ℝ)*(major2) + (21561651033/100000000000000 : ℝ)*(sp1) + (1313586321/4000000000000 : ℝ)*(sp2) + (189562399/50000000000000 : ℝ)*(sp3) + (1906582732699503/25000000000000 : ℝ)*(sp4) + (7626308406646051/100000000000000 : ℝ)*(sp5) + (7626296909507749/100000000000000 : ℝ)*(sp6) + (384616050177053/10000000000000 : ℝ)*(sp7) + (3846160880895327/100000000000000 : ℝ)*(f.failure) + (1906582732699503/25000000000000 : ℝ)*(f.sum) + (3014799651677/773250000000000000000000000 : ℝ)*base66 + (163678812544487797/30930000000000000000000000000000 : ℝ)*base67 + (177696061332707797/30930000000000000000000000000000 : ℝ)*base69 + (618170426957447797/30930000000000000000000000000000 : ℝ)*base71 + (2092034560853/309300000000000000000000000 : ℝ)*base74 + (287228541193337797/30930000000000000000000000000000 : ℝ)*base75 + (341966556184127797/30930000000000000000000000000000 : ℝ)*base77 + (1617091057445357797/30930000000000000000000000000000 : ℝ)*base79 + (7399642202737/1546500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (229201/80000000000000000000 : ℝ)*base90 + (229201/80000000000000000000 : ℝ)*base92 + (229201/80000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1125_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11143/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1125_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1125_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8277/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1125_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1125_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1125_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8317/2048 : ℝ) ≤ p) (hpb : p ≤ (4159/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (1193137/800000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8277/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (281/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1129/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7041/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1125_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
