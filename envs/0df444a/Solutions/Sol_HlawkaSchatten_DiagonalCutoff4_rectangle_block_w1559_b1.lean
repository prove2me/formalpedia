-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1559_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:23:59.670532+00:00
-- url     : https://prove2.me/submissions/ada238d6-6bc1-4067-81e6-91d8d06d05c7

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
theorem support_rectangle_w1559_s3_0 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-450116977/2500000000 : ℝ)*x 0 + (5429089973/10000000000 : ℝ)*x 1 + (1043592171/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (450116977/2500000000 : ℝ)^4615 ≤ (5521067639529/50000000000000 : ℝ)^3591 := by
    have hnat : (450116977 : ℕ)^4615*50000000000000^3591 ≤ 5521067639529^3591*2500000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450116977 2500000000 5521067639529 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429089973/10000000000 : ℝ)^4615 ≤ (11403089062507/25000000000000 : ℝ)^3591 := by
    have hnat : (5429089973 : ℕ)^4615*25000000000000^3591 ≤ 11403089062507^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429089973 10000000000 11403089062507 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043592171/2000000000 : ℝ)^4615 ≤ (43345508451321/100000000000000 : ℝ)^3591 := by
    have hnat : (1043592171 : ℕ)^4615*100000000000000^3591 ≤ 43345508451321^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043592171 2000000000 43345508451321 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-450116977/2500000000 : ℝ), (5429089973/10000000000 : ℝ), (1043592171/2000000000 : ℝ)] ![(5521067639529/50000000000000 : ℝ), (11403089062507/25000000000000 : ℝ), (43345508451321/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-450116977/2500000000 : ℝ)|^4615 ≤ (5521067639529/50000000000000 : ℝ)^3591
        have hw : |(-450116977/2500000000 : ℝ)|=(450116977/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429089973/10000000000 : ℝ)|^4615 ≤ (11403089062507/25000000000000 : ℝ)^3591
        have hw : |(5429089973/10000000000 : ℝ)|=(5429089973/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043592171/2000000000 : ℝ)|^4615 ≤ (43345508451321/100000000000000 : ℝ)^3591
        have hw : |(1043592171/2000000000 : ℝ)|=(1043592171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s3_1 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674681897/5000000000 : ℝ)*x 0 + (-954271477/5000000000 : ℝ)*x 1 + (2608980443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674681897/5000000000 : ℝ)^4615 ≤ (2797084013801/6250000000000 : ℝ)^3591 := by
    have hnat : (2674681897 : ℕ)^4615*6250000000000^3591 ≤ 2797084013801^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674681897 5000000000 2797084013801 6250000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (954271477/5000000000 : ℝ)^4615 ≤ (2975286742751/25000000000000 : ℝ)^3591 := by
    have hnat : (954271477 : ℕ)^4615*25000000000000^3591 ≤ 2975286742751^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954271477 5000000000 2975286742751 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608980443/5000000000 : ℝ)^4615 ≤ (4334550878227/10000000000000 : ℝ)^3591 := by
    have hnat : (2608980443 : ℕ)^4615*10000000000000^3591 ≤ 4334550878227^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608980443 5000000000 4334550878227 10000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674681897/5000000000 : ℝ), (-954271477/5000000000 : ℝ), (2608980443/5000000000 : ℝ)] ![(2797084013801/6250000000000 : ℝ), (2975286742751/25000000000000 : ℝ), (4334550878227/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674681897/5000000000 : ℝ)|^4615 ≤ (2797084013801/6250000000000 : ℝ)^3591
        have hw : |(2674681897/5000000000 : ℝ)|=(2674681897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-954271477/5000000000 : ℝ)|^4615 ≤ (2975286742751/25000000000000 : ℝ)^3591
        have hw : |(-954271477/5000000000 : ℝ)|=(954271477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608980443/5000000000 : ℝ)|^4615 ≤ (4334550878227/10000000000000 : ℝ)^3591
        have hw : |(2608980443/5000000000 : ℝ)|=(2608980443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s3_2 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349363759/10000000000 : ℝ)*x 0 + (52179609/100000000 : ℝ)*x 1 + (-238567873/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349363759/10000000000 : ℝ)^4615 ≤ (8950668768901/20000000000000 : ℝ)^3591 := by
    have hnat : (5349363759 : ℕ)^4615*20000000000000^3591 ≤ 8950668768901^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349363759 10000000000 8950668768901 20000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (52179609/100000000 : ℝ)^4615 ≤ (43345508931731/100000000000000 : ℝ)^3591 := by
    have hnat : (52179609 : ℕ)^4615*100000000000000^3591 ≤ 43345508931731^3591*100000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52179609 100000000 43345508931731 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238567873/1250000000 : ℝ)^4615 ≤ (11901147211421/100000000000000 : ℝ)^3591 := by
    have hnat : (238567873 : ℕ)^4615*100000000000000^3591 ≤ 11901147211421^3591*1250000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238567873 1250000000 11901147211421 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349363759/10000000000 : ℝ), (52179609/100000000 : ℝ), (-238567873/1250000000 : ℝ)] ![(8950668768901/20000000000000 : ℝ), (43345508931731/100000000000000 : ℝ), (11901147211421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349363759/10000000000 : ℝ)|^4615 ≤ (8950668768901/20000000000000 : ℝ)^3591
        have hw : |(5349363759/10000000000 : ℝ)|=(5349363759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(52179609/100000000 : ℝ)|^4615 ≤ (43345508931731/100000000000000 : ℝ)^3591
        have hw : |(52179609/100000000 : ℝ)|=(52179609/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-238567873/1250000000 : ℝ)|^4615 ≤ (11901147211421/100000000000000 : ℝ)^3591
        have hw : |(-238567873/1250000000 : ℝ)|=(238567873/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s3_3 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4248195797/10000000000 : ℝ)*x 0 + (4006752217/10000000000 : ℝ)*x 1 + (2250701541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248195797/10000000000 : ℝ)^4615 ≤ (33280076586859/100000000000000 : ℝ)^3591 := by
    have hnat : (4248195797 : ℕ)^4615*100000000000000^3591 ≤ 33280076586859^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248195797 10000000000 33280076586859 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4006752217/10000000000 : ℝ)^4615 ≤ (30869233698083/100000000000000 : ℝ)^3591 := by
    have hnat : (4006752217 : ℕ)^4615*100000000000000^3591 ≤ 30869233698083^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4006752217 10000000000 30869233698083 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2250701541/5000000000 : ℝ)^4615 ≤ (35850689700699/100000000000000 : ℝ)^3591 := by
    have hnat : (2250701541 : ℕ)^4615*100000000000000^3591 ≤ 35850689700699^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250701541 5000000000 35850689700699 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248195797/10000000000 : ℝ), (4006752217/10000000000 : ℝ), (2250701541/5000000000 : ℝ)] ![(33280076586859/100000000000000 : ℝ), (30869233698083/100000000000000 : ℝ), (35850689700699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248195797/10000000000 : ℝ)|^4615 ≤ (33280076586859/100000000000000 : ℝ)^3591
        have hw : |(4248195797/10000000000 : ℝ)|=(4248195797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4006752217/10000000000 : ℝ)|^4615 ≤ (30869233698083/100000000000000 : ℝ)^3591
        have hw : |(4006752217/10000000000 : ℝ)|=(4006752217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2250701541/5000000000 : ℝ)|^4615 ≤ (35850689700699/100000000000000 : ℝ)^3591
        have hw : |(2250701541/5000000000 : ℝ)|=(2250701541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s3_4 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1800496151/10000000000 : ℝ)*x 0 + (1043815473/2000000000 : ℝ)*x 1 + (5427965337/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1800496151/10000000000 : ℝ)^4615 ≤ (11042357884499/100000000000000 : ℝ)^3591 := by
    have hnat : (1800496151 : ℕ)^4615*100000000000000^3591 ≤ 11042357884499^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800496151 10000000000 11042357884499 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043815473/2000000000 : ℝ)^4615 ≤ (10839357107311/25000000000000 : ℝ)^3591 := by
    have hnat : (1043815473 : ℕ)^4615*25000000000000^3591 ≤ 10839357107311^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043815473 2000000000 10839357107311 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5427965337/10000000000 : ℝ)^4615 ≤ (22800106835727/50000000000000 : ℝ)^3591 := by
    have hnat : (5427965337 : ℕ)^4615*50000000000000^3591 ≤ 22800106835727^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427965337 10000000000 22800106835727 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1800496151/10000000000 : ℝ), (1043815473/2000000000 : ℝ), (5427965337/10000000000 : ℝ)] ![(11042357884499/100000000000000 : ℝ), (10839357107311/25000000000000 : ℝ), (22800106835727/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1800496151/10000000000 : ℝ)|^4615 ≤ (11042357884499/100000000000000 : ℝ)^3591
        have hw : |(-1800496151/10000000000 : ℝ)|=(1800496151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043815473/2000000000 : ℝ)|^4615 ≤ (10839357107311/25000000000000 : ℝ)^3591
        have hw : |(1043815473/2000000000 : ℝ)|=(1043815473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5427965337/10000000000 : ℝ)|^4615 ≤ (22800106835727/50000000000000 : ℝ)^3591
        have hw : |(5427965337/10000000000 : ℝ)|=(5427965337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s3_5 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661697403/1250000000 : ℝ)*x 0 + (-1698538783/10000000000 : ℝ)*x 1 + (2713982817/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661697403/1250000000 : ℝ)^4615 ≤ (8830891157501/20000000000000 : ℝ)^3591 := by
    have hnat : (661697403 : ℕ)^4615*20000000000000^3591 ≤ 8830891157501^3591*1250000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661697403 1250000000 8830891157501 20000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1698538783/10000000000 : ℝ)^4615 ≤ (2049065463003/20000000000000 : ℝ)^3591 := by
    have hnat : (1698538783 : ℕ)^4615*20000000000000^3591 ≤ 2049065463003^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1698538783 10000000000 2049065463003 20000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713982817/5000000000 : ℝ)^4615 ≤ (22800108439019/50000000000000 : ℝ)^3591 := by
    have hnat : (2713982817 : ℕ)^4615*50000000000000^3591 ≤ 22800108439019^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713982817 5000000000 22800108439019 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661697403/1250000000 : ℝ), (-1698538783/10000000000 : ℝ), (2713982817/5000000000 : ℝ)] ![(8830891157501/20000000000000 : ℝ), (2049065463003/20000000000000 : ℝ), (22800108439019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661697403/1250000000 : ℝ)|^4615 ≤ (8830891157501/20000000000000 : ℝ)^3591
        have hw : |(661697403/1250000000 : ℝ)|=(661697403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1698538783/10000000000 : ℝ)|^4615 ≤ (2049065463003/20000000000000 : ℝ)^3591
        have hw : |(-1698538783/10000000000 : ℝ)|=(1698538783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713982817/5000000000 : ℝ)|^4615 ≤ (22800108439019/50000000000000 : ℝ)^3591
        have hw : |(2713982817/5000000000 : ℝ)|=(2713982817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s3_6 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323395001/2500000000 : ℝ)*x 0 + (5427965257/10000000000 : ℝ)*x 1 + (-169853823/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323395001/2500000000 : ℝ)^4615 ≤ (2759654009303/6250000000000 : ℝ)^3591 := by
    have hnat : (1323395001 : ℕ)^4615*6250000000000^3591 ≤ 2759654009303^3591*2500000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323395001 2500000000 2759654009303 6250000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427965257/10000000000 : ℝ)^4615 ≤ (2850013300483/6250000000000 : ℝ)^3591 := by
    have hnat : (5427965257 : ℕ)^4615*6250000000000^3591 ≤ 2850013300483^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427965257 10000000000 2850013300483 6250000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169853823/1000000000 : ℝ)^4615 ≤ (10245323028229/100000000000000 : ℝ)^3591 := by
    have hnat : (169853823 : ℕ)^4615*100000000000000^3591 ≤ 10245323028229^3591*1000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169853823 1000000000 10245323028229 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323395001/2500000000 : ℝ), (5427965257/10000000000 : ℝ), (-169853823/1000000000 : ℝ)] ![(2759654009303/6250000000000 : ℝ), (2850013300483/6250000000000 : ℝ), (10245323028229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323395001/2500000000 : ℝ)|^4615 ≤ (2759654009303/6250000000000 : ℝ)^3591
        have hw : |(1323395001/2500000000 : ℝ)|=(1323395001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427965257/10000000000 : ℝ)|^4615 ≤ (2850013300483/6250000000000 : ℝ)^3591
        have hw : |(5427965257/10000000000 : ℝ)|=(5427965257/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-169853823/1000000000 : ℝ)|^4615 ≤ (10245323028229/100000000000000 : ℝ)^3591
        have hw : |(-169853823/1000000000 : ℝ)|=(169853823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s3_7 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4248262661/10000000000 : ℝ)*x 0 + (179951527/400000000 : ℝ)*x 1 + (4009386921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248262661/10000000000 : ℝ)^4615 ≤ (16640374882047/50000000000000 : ℝ)^3591 := by
    have hnat : (4248262661 : ℕ)^4615*50000000000000^3591 ≤ 16640374882047^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248262661 10000000000 16640374882047 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179951527/400000000 : ℝ)^4615 ≤ (7164785446281/20000000000000 : ℝ)^3591 := by
    have hnat : (179951527 : ℕ)^4615*20000000000000^3591 ≤ 7164785446281^3591*400000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179951527 400000000 7164785446281 20000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4009386921/10000000000 : ℝ)^4615 ≤ (1930957686539/6250000000000 : ℝ)^3591 := by
    have hnat : (4009386921 : ℕ)^4615*6250000000000^3591 ≤ 1930957686539^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4009386921 10000000000 1930957686539 6250000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248262661/10000000000 : ℝ), (179951527/400000000 : ℝ), (4009386921/10000000000 : ℝ)] ![(16640374882047/50000000000000 : ℝ), (7164785446281/20000000000000 : ℝ), (1930957686539/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248262661/10000000000 : ℝ)|^4615 ≤ (16640374882047/50000000000000 : ℝ)^3591
        have hw : |(4248262661/10000000000 : ℝ)|=(4248262661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(179951527/400000000 : ℝ)|^4615 ≤ (7164785446281/20000000000000 : ℝ)^3591
        have hw : |(179951527/400000000 : ℝ)|=(179951527/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4009386921/10000000000 : ℝ)|^4615 ≤ (1930957686539/6250000000000 : ℝ)^3591
        have hw : |(4009386921/10000000000 : ℝ)|=(4009386921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1559_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7921/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1381/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (621/4000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7921/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2689/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7921/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2689/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7921/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2689/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7921/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2689/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7921/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2689/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7921/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2689/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2689/25000 : ℝ) ^ (4613/1024 : ℝ) ≤ (2171052410491601/50000000000000000000 : ℝ) := by
    have hpowers : (2689/25000 : ℝ)^4613 ≤ (2171052410491601/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2689 : ℕ)^4613*50000000000000000000^1024 ≤ 2171052410491601^1024*25000^4613 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2689 25000 2171052410491601 50000000000000000000 4613 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2689/25000 : ℝ)) (X := (2171052410491601/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7921/50000 : ℝ) ^ (4613/1024 : ℝ) ≤ (24844934870228377/100000000000000000000 : ℝ) := by
    have hpowers : (7921/50000 : ℝ)^4613 ≤ (24844934870228377/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7921 : ℕ)^4613*100000000000000000000^1024 ≤ 24844934870228377^1024*50000^4613 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7921 50000 24844934870228377 100000000000000000000 4613 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7921/50000 : ℝ)) (X := (24844934870228377/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002171052410491601/25000000000000000000 : ℝ) ≤ (2000038553350421/2000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (25002171052410491601/25000000000000000000 : ℝ)^1024 ≤ (2000038553350421/2000000000000000 : ℝ)^4613 := by
      have hnat : (25002171052410491601 : ℕ)^1024*2000000000000000^4613 ≤ 2000038553350421^4613*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002171052410491601 25000000000000000000 2000038553350421 2000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000038553350421/2000000000000000 : ℝ)) (X := (25002171052410491601/25000000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100029187039691211579/100000000000000000000 : ℝ) ≤ (10000647824318049/10000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (100029187039691211579/100000000000000000000 : ℝ)^1024 ≤ (10000647824318049/10000000000000000 : ℝ)^4613 := by
      have hnat : (100029187039691211579 : ℕ)^1024*10000000000000000^4613 ≤ 10000647824318049^4613*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100029187039691211579 100000000000000000000 10000647824318049 10000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000647824318049/10000000000000000 : ℝ)) (X := (100029187039691211579/100000000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024844934870228377/50000000000000000000 : ℝ) ≤ (10001102881883993/10000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (50024844934870228377/50000000000000000000 : ℝ)^1024 ≤ (10001102881883993/10000000000000000 : ℝ)^4613 := by
      have hnat : (50024844934870228377 : ℕ)^1024*10000000000000000^4613 ≤ 10001102881883993^4613*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024844934870228377 50000000000000000000 10001102881883993 10000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001102881883993/10000000000000000 : ℝ)) (X := (50024844934870228377/50000000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2171052410491601/50000000000000000000 : ℝ) ≤ ((25425595606671309351/25430000000000000000 : ℝ)+2*(56882195743/63575000000000 : ℝ)*(2689/25000 : ℝ))^(4613/1024 : ℝ) := by
    rw [show (25425595606671309351/25430000000000000000 : ℝ)+2*(56882195743/63575000000000 : ℝ)*(2689/25000 : ℝ)=(2000038553350421/2000000000000000 : ℝ) by norm_num, show 1+2*(2171052410491601/50000000000000000000 : ℝ)=(25002171052410491601/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24844934870228377/100000000000000000000 : ℝ)+(2171052410491601/50000000000000000000 : ℝ) ≤ ((25425595606671309351/25430000000000000000 : ℝ)+(56882195743/63575000000000 : ℝ)*((7921/50000 : ℝ)+(2689/25000 : ℝ)))^(4613/1024 : ℝ) := by
    rw [show (25425595606671309351/25430000000000000000 : ℝ)+(56882195743/63575000000000 : ℝ)*((7921/50000 : ℝ)+(2689/25000 : ℝ))=(10000647824318049/10000000000000000 : ℝ) by norm_num, show 1+(24844934870228377/100000000000000000000 : ℝ)+(2171052410491601/50000000000000000000 : ℝ)=(100029187039691211579/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24844934870228377/100000000000000000000 : ℝ) ≤ ((25425595606671309351/25430000000000000000 : ℝ)+2*(56882195743/63575000000000 : ℝ)*(7921/50000 : ℝ))^(4613/1024 : ℝ) := by
    rw [show (25425595606671309351/25430000000000000000 : ℝ)+2*(56882195743/63575000000000 : ℝ)*(7921/50000 : ℝ)=(10001102881883993/10000000000000000 : ℝ) by norm_num, show 1+2*(24844934870228377/100000000000000000000 : ℝ)=(50024844934870228377/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (25425595606671309351/25430000000000000000 : ℝ)*(X 1 0+X 2 0)+(56882195743/63575000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (7921/50000 : ℝ)) (c := (25425595606671309351/25430000000000000000 : ℝ)) (alpha := (56882195743/63575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (25425595606671309351/25430000000000000000 : ℝ)*(X 0 1+X 2 1)+(56882195743/63575000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (7921/50000 : ℝ)) (c := (25425595606671309351/25430000000000000000 : ℝ)) (alpha := (56882195743/63575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (25425595606671309351/25430000000000000000 : ℝ)*(X 0 2+X 1 2)+(56882195743/63575000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (2689/25000 : ℝ)) (hi := (7921/50000 : ℝ)) (c := (25425595606671309351/25430000000000000000 : ℝ)) (alpha := (56882195743/63575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-450116977/2500000000 : ℝ)*X 0 0+(5429089973/10000000000 : ℝ)*X 0 1+(1043592171/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674681897/5000000000 : ℝ)*X 1 0+(-954271477/5000000000 : ℝ)*X 1 1+(2608980443/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349363759/10000000000 : ℝ)*X 2 0+(52179609/100000000 : ℝ)*X 2 1+(-238567873/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4248195797/10000000000 : ℝ)*X 0 0+(4006752217/10000000000 : ℝ)*X 0 1+(2250701541/5000000000 : ℝ)*X 0 2+(4248195797/10000000000 : ℝ)*X 1 0+(4006752217/10000000000 : ℝ)*X 1 1+(2250701541/5000000000 : ℝ)*X 1 2+(4248195797/10000000000 : ℝ)*X 2 0+(4006752217/10000000000 : ℝ)*X 2 1+(2250701541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1800496151/10000000000 : ℝ)*X 0 0+(1043815473/2000000000 : ℝ)*X 0 1+(5427965337/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((661697403/1250000000 : ℝ)*X 1 0+(-1698538783/10000000000 : ℝ)*X 1 1+(2713982817/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323395001/2500000000 : ℝ)*X 2 0+(5427965257/10000000000 : ℝ)*X 2 1+(-169853823/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4248262661/10000000000 : ℝ)*X 0 0+(179951527/400000000 : ℝ)*X 0 1+(4009386921/10000000000 : ℝ)*X 0 2+(4248262661/10000000000 : ℝ)*X 1 0+(179951527/400000000 : ℝ)*X 1 1+(4009386921/10000000000 : ℝ)*X 1 2+(4248262661/10000000000 : ℝ)*X 2 0+(179951527/400000000 : ℝ)*X 2 1+(4009386921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28669209119893545884391/2543000000000000000000000000 : ℝ) := by norm_num
    linear_combination (390230557/20000000000000 : ℝ)*(base19) + (890289923/50000000000000 : ℝ)*(base23) + (74667919/100000000000000 : ℝ)*(lower2) + (303253111/100000000000000 : ℝ)*(upper3) + (168185331/100000000000000 : ℝ)*(upper5) + (168953942312373/5000000000000 : ℝ)*(major0) + (168953942312373/5000000000000 : ℝ)*(major1) + (168953942312373/5000000000000 : ℝ)*(major2) + (2368235659060897/50000000000000 : ℝ)*(sp0) + (4736500055787213/100000000000000 : ℝ)*(sp1) + (592062528295019/12500000000000 : ℝ)*(sp2) + (252705080643761/12500000000000 : ℝ)*(sp3) + (7672204551/25000000000000 : ℝ)*(sp4) + (2932922467/20000000000000 : ℝ)*(sp7) + (252706913720303/12500000000000 : ℝ)*(f.failure) + (2368251003469999/50000000000000 : ℝ)*(f.sum) + (14126332808679/2543000000000000000000000000 : ℝ)*base65 + (613393844708950077/127150000000000000000000000000000 : ℝ)*base68 + (373645841395149923/127150000000000000000000000000000 : ℝ)*base69 + (1406630328348549923/127150000000000000000000000000000 : ℝ)*base71 + (5279942817593/2543000000000000000000000000 : ℝ)*base74 + (1832658682619850077/127150000000000000000000000000000 : ℝ)*base76 + (618279317319649923/127150000000000000000000000000000 : ℝ)*base77 + (659108437431650077/127150000000000000000000000000000 : ℝ)*base80 + (1360455652171/508600000000000000000000000 : ℝ)*base81 + (11041389/1250000000000000000000 : ℝ)*base89 + (11041389/1250000000000000000000 : ℝ)*base91 + (11041389/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1016109606909277466997348441/79468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (827706481/100000000000000 : ℝ)*(base19) + (558661307/25000000000000 : ℝ)*(base23) + (258140401/100000000000000 : ℝ)*(upper3) + (225605609/100000000000000 : ℝ)*(lower4) + (73638619/100000000000000 : ℝ)*(upper5) + (426910420482053/12500000000000 : ℝ)*(major0) + (426910420482053/12500000000000 : ℝ)*(major1) + (426910420482053/12500000000000 : ℝ)*(major2) + (1249834511/10000000000000 : ℝ)*(sp1) + (9657143557/25000000000000 : ℝ)*(sp2) + (2393625169235413/50000000000000 : ℝ)*(sp4) + (957447402483847/20000000000000 : ℝ)*(sp5) + (4787209475251371/100000000000000 : ℝ)*(sp6) + (2043315963032717/100000000000000 : ℝ)*(sp7) + (2043315963032717/100000000000000 : ℝ)*(f.failure) + (2393625169235413/50000000000000 : ℝ)*(f.sum) + (22953705694263/12715000000000000000000000000 : ℝ)*base65 + (1155663195258802603/317875000000000000000000000000000 : ℝ)*base67 + (3963682654206052603/317875000000000000000000000000000 : ℝ)*base69 + (1513455045766802603/317875000000000000000000000000000 : ℝ)*base71 + (28006313925911/6357500000000000000000000000 : ℝ)*base74 + (3526229726608052603/317875000000000000000000000000000 : ℝ)*base75 + (1277127478596697397/317875000000000000000000000000000 : ℝ)*base78 + (872166676264927603/317875000000000000000000000000000 : ℝ)*base79 + (32551299669503/12715000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (24580871/10000000000000000000000 : ℝ)*base89 + (24580871/10000000000000000000000 : ℝ)*base91 + (24580871/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1559_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7921/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1381/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (621/4000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1559_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1559_s4_0 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-360144719/2000000000 : ℝ)*x 0 + (5427382639/10000000000 : ℝ)*x 1 + (1043899739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360144719/2000000000 : ℝ)^4615 ≤ (5522075293507/50000000000000 : ℝ)^3591 := by
    have hnat : (360144719 : ℕ)^4615*50000000000000^3591 ≤ 5522075293507^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360144719 2000000000 5522075293507 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427382639/10000000000 : ℝ)^4615 ≤ (911878452471/2000000000000 : ℝ)^3591 := by
    have hnat : (5427382639 : ℕ)^4615*2000000000000^3591 ≤ 911878452471^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427382639 10000000000 911878452471 2000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043899739/2000000000 : ℝ)^4615 ≤ (10840481695381/25000000000000 : ℝ)^3591 := by
    have hnat : (1043899739 : ℕ)^4615*25000000000000^3591 ≤ 10840481695381^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043899739 2000000000 10840481695381 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360144719/2000000000 : ℝ), (5427382639/10000000000 : ℝ), (1043899739/2000000000 : ℝ)] ![(5522075293507/50000000000000 : ℝ), (911878452471/2000000000000 : ℝ), (10840481695381/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360144719/2000000000 : ℝ)|^4615 ≤ (5522075293507/50000000000000 : ℝ)^3591
        have hw : |(-360144719/2000000000 : ℝ)|=(360144719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427382639/10000000000 : ℝ)|^4615 ≤ (911878452471/2000000000000 : ℝ)^3591
        have hw : |(5427382639/10000000000 : ℝ)|=(5427382639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043899739/2000000000 : ℝ)|^4615 ≤ (10840481695381/25000000000000 : ℝ)^3591
        have hw : |(1043899739/2000000000 : ℝ)|=(1043899739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s4_1 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (106978249/200000000 : ℝ)*x 0 + (-1907099607/10000000000 : ℝ)*x 1 + (32621867/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (106978249/200000000 : ℝ)^4615 ≤ (44748491535729/100000000000000 : ℝ)^3591 := by
    have hnat : (106978249 : ℕ)^4615*100000000000000^3591 ≤ 44748491535729^3591*200000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106978249 200000000 44748491535729 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1907099607/10000000000 : ℝ)^4615 ≤ (2972395349897/25000000000000 : ℝ)^3591 := by
    have hnat : (1907099607 : ℕ)^4615*25000000000000^3591 ≤ 2972395349897^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1907099607 10000000000 2972395349897 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32621867/62500000 : ℝ)^4615 ≤ (43361927048441/100000000000000 : ℝ)^3591 := by
    have hnat : (32621867 : ℕ)^4615*100000000000000^3591 ≤ 43361927048441^3591*62500000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32621867 62500000 43361927048441 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(106978249/200000000 : ℝ), (-1907099607/10000000000 : ℝ), (32621867/62500000 : ℝ)] ![(44748491535729/100000000000000 : ℝ), (2972395349897/25000000000000 : ℝ), (43361927048441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(106978249/200000000 : ℝ)|^4615 ≤ (44748491535729/100000000000000 : ℝ)^3591
        have hw : |(106978249/200000000 : ℝ)|=(106978249/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1907099607/10000000000 : ℝ)|^4615 ≤ (2972395349897/25000000000000 : ℝ)^3591
        have hw : |(-1907099607/10000000000 : ℝ)|=(1907099607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32621867/62500000 : ℝ)|^4615 ≤ (43361927048441/100000000000000 : ℝ)^3591
        have hw : |(32621867/62500000 : ℝ)|=(32621867/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s4_2 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334307031/625000000 : ℝ)*x 0 + (130487467/250000000 : ℝ)*x 1 + (-953549799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334307031/625000000 : ℝ)^4615 ≤ (22374246015149/50000000000000 : ℝ)^3591 := by
    have hnat : (334307031 : ℕ)^4615*50000000000000^3591 ≤ 22374246015149^3591*625000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334307031 625000000 22374246015149 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130487467/250000000 : ℝ)^4615 ≤ (21680963310687/50000000000000 : ℝ)^3591 := by
    have hnat : (130487467 : ℕ)^4615*50000000000000^3591 ≤ 21680963310687^3591*250000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130487467 250000000 21680963310687 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (953549799/5000000000 : ℝ)^4615 ≤ (5944790663739/50000000000000 : ℝ)^3591 := by
    have hnat : (953549799 : ℕ)^4615*50000000000000^3591 ≤ 5944790663739^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953549799 5000000000 5944790663739 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334307031/625000000 : ℝ), (130487467/250000000 : ℝ), (-953549799/5000000000 : ℝ)] ![(22374246015149/50000000000000 : ℝ), (21680963310687/50000000000000 : ℝ), (5944790663739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334307031/625000000 : ℝ)|^4615 ≤ (22374246015149/50000000000000 : ℝ)^3591
        have hw : |(334307031/625000000 : ℝ)|=(334307031/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130487467/250000000 : ℝ)|^4615 ≤ (21680963310687/50000000000000 : ℝ)^3591
        have hw : |(130487467/250000000 : ℝ)|=(130487467/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-953549799/5000000000 : ℝ)|^4615 ≤ (5944790663739/50000000000000 : ℝ)^3591
        have hw : |(-953549799/5000000000 : ℝ)|=(953549799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s4_3 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849671411/2000000000 : ℝ)*x 0 + (2005267859/5000000000 : ℝ)*x 1 + (2248791769/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849671411/2000000000 : ℝ)^4615 ≤ (33281700114593/100000000000000 : ℝ)^3591 := by
    have hnat : (849671411 : ℕ)^4615*100000000000000^3591 ≤ 33281700114593^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849671411 2000000000 33281700114593 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2005267859/5000000000 : ℝ)^4615 ≤ (30906700098471/100000000000000 : ℝ)^3591 := by
    have hnat : (2005267859 : ℕ)^4615*100000000000000^3591 ≤ 30906700098471^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2005267859 5000000000 30906700098471 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248791769/5000000000 : ℝ)^4615 ≤ (35811599772437/100000000000000 : ℝ)^3591 := by
    have hnat : (2248791769 : ℕ)^4615*100000000000000^3591 ≤ 35811599772437^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248791769 5000000000 35811599772437 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849671411/2000000000 : ℝ), (2005267859/5000000000 : ℝ), (2248791769/5000000000 : ℝ)] ![(33281700114593/100000000000000 : ℝ), (30906700098471/100000000000000 : ℝ), (35811599772437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849671411/2000000000 : ℝ)|^4615 ≤ (33281700114593/100000000000000 : ℝ)^3591
        have hw : |(849671411/2000000000 : ℝ)|=(849671411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2005267859/5000000000 : ℝ)|^4615 ≤ (30906700098471/100000000000000 : ℝ)^3591
        have hw : |(2005267859/5000000000 : ℝ)|=(2005267859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248791769/5000000000 : ℝ)|^4615 ≤ (35811599772437/100000000000000 : ℝ)^3591
        have hw : |(2248791769/5000000000 : ℝ)|=(2248791769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s4_4 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-360150179/2000000000 : ℝ)*x 0 + (1044116191/2000000000 : ℝ)*x 1 + (5426292371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (360150179/2000000000 : ℝ)^4615 ≤ (11044365768623/100000000000000 : ℝ)^3591 := by
    have hnat : (360150179 : ℕ)^4615*100000000000000^3591 ≤ 11044365768623^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      360150179 2000000000 11044365768623 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044116191/2000000000 : ℝ)^4615 ≤ (21686741031441/50000000000000 : ℝ)^3591 := by
    have hnat : (1044116191 : ℕ)^4615*50000000000000^3591 ≤ 21686741031441^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044116191 2000000000 21686741031441 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426292371/10000000000 : ℝ)^4615 ≤ (45582152157939/100000000000000 : ℝ)^3591 := by
    have hnat : (5426292371 : ℕ)^4615*100000000000000^3591 ≤ 45582152157939^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426292371 10000000000 45582152157939 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-360150179/2000000000 : ℝ), (1044116191/2000000000 : ℝ), (5426292371/10000000000 : ℝ)] ![(11044365768623/100000000000000 : ℝ), (21686741031441/50000000000000 : ℝ), (45582152157939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-360150179/2000000000 : ℝ)|^4615 ≤ (11044365768623/100000000000000 : ℝ)^3591
        have hw : |(-360150179/2000000000 : ℝ)|=(360150179/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1044116191/2000000000 : ℝ)|^4615 ≤ (21686741031441/50000000000000 : ℝ)^3591
        have hw : |(1044116191/2000000000 : ℝ)|=(1044116191/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426292371/10000000000 : ℝ)|^4615 ≤ (45582152157939/100000000000000 : ℝ)^3591
        have hw : |(5426292371/10000000000 : ℝ)|=(5426292371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s4_5 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10339817/19531250 : ℝ)*x 0 + (-1700305939/10000000000 : ℝ)*x 1 + (5426292381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10339817/19531250 : ℝ)^4615 ≤ (44158819598649/100000000000000 : ℝ)^3591 := by
    have hnat : (10339817 : ℕ)^4615*100000000000000^3591 ≤ 44158819598649^3591*19531250^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10339817 19531250 44158819598649 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1700305939/10000000000 : ℝ)^4615 ≤ (5129514058061/50000000000000 : ℝ)^3591 := by
    have hnat : (1700305939 : ℕ)^4615*50000000000000^3591 ≤ 5129514058061^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700305939 10000000000 5129514058061 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426292381/10000000000 : ℝ)^4615 ≤ (9116430453179/20000000000000 : ℝ)^3591 := by
    have hnat : (5426292381 : ℕ)^4615*20000000000000^3591 ≤ 9116430453179^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426292381 10000000000 9116430453179 20000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10339817/19531250 : ℝ), (-1700305939/10000000000 : ℝ), (5426292381/10000000000 : ℝ)] ![(44158819598649/100000000000000 : ℝ), (5129514058061/50000000000000 : ℝ), (9116430453179/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10339817/19531250 : ℝ)|^4615 ≤ (44158819598649/100000000000000 : ℝ)^3591
        have hw : |(10339817/19531250 : ℝ)|=(10339817/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1700305939/10000000000 : ℝ)|^4615 ≤ (5129514058061/50000000000000 : ℝ)^3591
        have hw : |(-1700305939/10000000000 : ℝ)|=(1700305939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426292381/10000000000 : ℝ)|^4615 ≤ (9116430453179/20000000000000 : ℝ)^3591
        have hw : |(5426292381/10000000000 : ℝ)|=(5426292381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s4_6 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323496577/2500000000 : ℝ)*x 0 + (1085258477/2000000000 : ℝ)*x 1 + (-212538241/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323496577/2500000000 : ℝ)^4615 ≤ (5519852455191/12500000000000 : ℝ)^3591 := by
    have hnat : (1323496577 : ℕ)^4615*12500000000000^3591 ≤ 5519852455191^3591*2500000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323496577 2500000000 5519852455191 12500000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085258477/2000000000 : ℝ)^4615 ≤ (22791076154539/50000000000000 : ℝ)^3591 := by
    have hnat : (1085258477 : ℕ)^4615*50000000000000^3591 ≤ 22791076154539^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085258477 2000000000 22791076154539 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (212538241/1250000000 : ℝ)^4615 ≤ (5129514015413/50000000000000 : ℝ)^3591 := by
    have hnat : (212538241 : ℕ)^4615*50000000000000^3591 ≤ 5129514015413^3591*1250000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212538241 1250000000 5129514015413 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323496577/2500000000 : ℝ), (1085258477/2000000000 : ℝ), (-212538241/1250000000 : ℝ)] ![(5519852455191/12500000000000 : ℝ), (22791076154539/50000000000000 : ℝ), (5129514015413/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323496577/2500000000 : ℝ)|^4615 ≤ (5519852455191/12500000000000 : ℝ)^3591
        have hw : |(1323496577/2500000000 : ℝ)|=(1323496577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085258477/2000000000 : ℝ)|^4615 ≤ (22791076154539/50000000000000 : ℝ)^3591
        have hw : |(1085258477/2000000000 : ℝ)|=(1085258477/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-212538241/1250000000 : ℝ)|^4615 ≤ (5129514015413/50000000000000 : ℝ)^3591
        have hw : |(-212538241/1250000000 : ℝ)|=(212538241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s4_7 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4248420967/10000000000 : ℝ)*x 0 + (2247523983/5000000000 : ℝ)*x 1 + (4013090117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248420967/10000000000 : ℝ)^4615 ≤ (33282343578413/100000000000000 : ℝ)^3591 := by
    have hnat : (4248420967 : ℕ)^4615*100000000000000^3591 ≤ 33282343578413^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248420967 10000000000 33282343578413 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247523983/5000000000 : ℝ)^4615 ≤ (17892827740443/50000000000000 : ℝ)^3591 := by
    have hnat : (2247523983 : ℕ)^4615*50000000000000^3591 ≤ 17892827740443^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247523983 5000000000 17892827740443 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4013090117/10000000000 : ℝ)^4615 ≤ (3866500115679/12500000000000 : ℝ)^3591 := by
    have hnat : (4013090117 : ℕ)^4615*12500000000000^3591 ≤ 3866500115679^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013090117 10000000000 3866500115679 12500000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248420967/10000000000 : ℝ), (2247523983/5000000000 : ℝ), (4013090117/10000000000 : ℝ)] ![(33282343578413/100000000000000 : ℝ), (17892827740443/50000000000000 : ℝ), (3866500115679/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248420967/10000000000 : ℝ)|^4615 ≤ (33282343578413/100000000000000 : ℝ)^3591
        have hw : |(4248420967/10000000000 : ℝ)|=(4248420967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247523983/5000000000 : ℝ)|^4615 ≤ (17892827740443/50000000000000 : ℝ)^3591
        have hw : |(2247523983/5000000000 : ℝ)|=(2247523983/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4013090117/10000000000 : ℝ)|^4615 ≤ (3866500115679/12500000000000 : ℝ)^3591
        have hw : |(4013090117/10000000000 : ℝ)|=(4013090117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1559_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (621/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1381/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11081/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15489/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (621/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1381/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (621/4000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1381/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (621/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1381/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (621/4000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1381/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (621/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1381/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (621/4000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1381/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1381/12500 : ℝ) ^ (4613/1024 : ℝ) ≤ (4898972804634761/100000000000000000000 : ℝ) := by
    have hpowers : (1381/12500 : ℝ)^4613 ≤ (4898972804634761/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1381 : ℕ)^4613*100000000000000000000^1024 ≤ 4898972804634761^1024*12500^4613 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1381 12500 4898972804634761 100000000000000000000 4613 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1381/12500 : ℝ)) (X := (4898972804634761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (621/4000 : ℝ) ^ (4613/1024 : ℝ) ≤ (22682566815718731/100000000000000000000 : ℝ) := by
    have hpowers : (621/4000 : ℝ)^4613 ≤ (22682566815718731/100000000000000000000 : ℝ)^1024 := by
      have hnat : (621 : ℕ)^4613*100000000000000000000^1024 ≤ 22682566815718731^1024*4000^4613 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        621 4000 22682566815718731 100000000000000000000 4613 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (621/4000 : ℝ)) (X := (22682566815718731/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004898972804634761/50000000000000000000 : ℝ) ≤ (2500054371959221/2500000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (50004898972804634761/50000000000000000000 : ℝ)^1024 ≤ (2500054371959221/2500000000000000 : ℝ)^4613 := by
      have hnat : (50004898972804634761 : ℕ)^1024*2500000000000000^4613 ≤ 2500054371959221^4613*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004898972804634761 50000000000000000000 2500054371959221 2500000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500054371959221/2500000000000000 : ℝ)) (X := (50004898972804634761/50000000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006895384905088373/25000000000000000000 : ℝ) ≤ (10000612193077983/10000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (25006895384905088373/25000000000000000000 : ℝ)^1024 ≤ (10000612193077983/10000000000000000 : ℝ)^4613 := by
      have hnat : (25006895384905088373 : ℕ)^1024*10000000000000000^4613 ≤ 10000612193077983^4613*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006895384905088373 25000000000000000000 10000612193077983 10000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000612193077983/10000000000000000 : ℝ)) (X := (25006895384905088373/25000000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022682566815718731/50000000000000000000 : ℝ) ≤ (5000503449159541/5000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (50022682566815718731/50000000000000000000 : ℝ)^1024 ≤ (5000503449159541/5000000000000000 : ℝ)^4613 := by
      have hnat : (50022682566815718731 : ℕ)^1024*5000000000000000^4613 ≤ 5000503449159541^4613*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022682566815718731 50000000000000000000 5000503449159541 5000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000503449159541/5000000000000000 : ℝ)) (X := (50022682566815718731/50000000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4898972804634761/100000000000000000000 : ℝ) ≤ ((11190563071509601541/11192500000000000000 : ℝ)+2*(394705241099/447700000000000 : ℝ)*(1381/12500 : ℝ))^(4613/1024 : ℝ) := by
    rw [show (11190563071509601541/11192500000000000000 : ℝ)+2*(394705241099/447700000000000 : ℝ)*(1381/12500 : ℝ)=(2500054371959221/2500000000000000 : ℝ) by norm_num, show 1+2*(4898972804634761/100000000000000000000 : ℝ)=(50004898972804634761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22682566815718731/100000000000000000000 : ℝ)+(4898972804634761/100000000000000000000 : ℝ) ≤ ((11190563071509601541/11192500000000000000 : ℝ)+(394705241099/447700000000000 : ℝ)*((621/4000 : ℝ)+(1381/12500 : ℝ)))^(4613/1024 : ℝ) := by
    rw [show (11190563071509601541/11192500000000000000 : ℝ)+(394705241099/447700000000000 : ℝ)*((621/4000 : ℝ)+(1381/12500 : ℝ))=(10000612193077983/10000000000000000 : ℝ) by norm_num, show 1+(22682566815718731/100000000000000000000 : ℝ)+(4898972804634761/100000000000000000000 : ℝ)=(25006895384905088373/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22682566815718731/100000000000000000000 : ℝ) ≤ ((11190563071509601541/11192500000000000000 : ℝ)+2*(394705241099/447700000000000 : ℝ)*(621/4000 : ℝ))^(4613/1024 : ℝ) := by
    rw [show (11190563071509601541/11192500000000000000 : ℝ)+2*(394705241099/447700000000000 : ℝ)*(621/4000 : ℝ)=(5000503449159541/5000000000000000 : ℝ) by norm_num, show 1+2*(22682566815718731/100000000000000000000 : ℝ)=(50022682566815718731/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11190563071509601541/11192500000000000000 : ℝ)*(X 1 0+X 2 0)+(394705241099/447700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (1381/12500 : ℝ)) (hi := (621/4000 : ℝ)) (c := (11190563071509601541/11192500000000000000 : ℝ)) (alpha := (394705241099/447700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11190563071509601541/11192500000000000000 : ℝ)*(X 0 1+X 2 1)+(394705241099/447700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (1381/12500 : ℝ)) (hi := (621/4000 : ℝ)) (c := (11190563071509601541/11192500000000000000 : ℝ)) (alpha := (394705241099/447700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11190563071509601541/11192500000000000000 : ℝ)*(X 0 2+X 1 2)+(394705241099/447700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (1381/12500 : ℝ)) (hi := (621/4000 : ℝ)) (c := (11190563071509601541/11192500000000000000 : ℝ)) (alpha := (394705241099/447700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-360144719/2000000000 : ℝ)*X 0 0+(5427382639/10000000000 : ℝ)*X 0 1+(1043899739/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((106978249/200000000 : ℝ)*X 1 0+(-1907099607/10000000000 : ℝ)*X 1 1+(32621867/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334307031/625000000 : ℝ)*X 2 0+(130487467/250000000 : ℝ)*X 2 1+(-953549799/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((849671411/2000000000 : ℝ)*X 0 0+(2005267859/5000000000 : ℝ)*X 0 1+(2248791769/5000000000 : ℝ)*X 0 2+(849671411/2000000000 : ℝ)*X 1 0+(2005267859/5000000000 : ℝ)*X 1 1+(2248791769/5000000000 : ℝ)*X 1 2+(849671411/2000000000 : ℝ)*X 2 0+(2005267859/5000000000 : ℝ)*X 2 1+(2248791769/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-360150179/2000000000 : ℝ)*X 0 0+(1044116191/2000000000 : ℝ)*X 0 1+(5426292371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10339817/19531250 : ℝ)*X 1 0+(-1700305939/10000000000 : ℝ)*X 1 1+(5426292381/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323496577/2500000000 : ℝ)*X 2 0+(1085258477/2000000000 : ℝ)*X 2 1+(-212538241/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4248420967/10000000000 : ℝ)*X 0 0+(2247523983/5000000000 : ℝ)*X 0 1+(4013090117/10000000000 : ℝ)*X 0 2+(4248420967/10000000000 : ℝ)*X 1 0+(2247523983/5000000000 : ℝ)*X 1 1+(4013090117/10000000000 : ℝ)*X 1 2+(4248420967/10000000000 : ℝ)*X 2 0+(2247523983/5000000000 : ℝ)*X 2 1+(4013090117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (37587773800336417399208637/3497656250000000000000000000000 : ℝ) := by norm_num
    linear_combination (919764233/50000000000000 : ℝ)*(base19) + (433856311/25000000000000 : ℝ)*(base23) + (1215811/1562500000000 : ℝ)*(lower2) + (10921821/4000000000000 : ℝ)*(upper3) + (91577057/50000000000000 : ℝ)*(upper5) + (171591241413399/5000000000000 : ℝ)*(major0) + (171591241413399/5000000000000 : ℝ)*(major1) + (171591241413399/5000000000000 : ℝ)*(major2) + (2405203453669711/50000000000000 : ℝ)*(sp0) + (4810434970436477/100000000000000 : ℝ)*(sp1) + (4810435074539699/100000000000000 : ℝ)*(sp2) + (64162457790579/3125000000000 : ℝ)*(sp3) + (373782819/1250000000000 : ℝ)*(sp4) + (2767810761/20000000000000 : ℝ)*(sp7) + (1026606244176167/50000000000000 : ℝ)*(f.failure) + (4810436809964943/100000000000000 : ℝ)*(f.sum) + (15130062675159/4477000000000000000000000000 : ℝ)*base65 + (373096430233672859/55962500000000000000000000000000 : ℝ)*base67 + (439034835311685359/55962500000000000000000000000000 : ℝ)*base69 + (34798465403160359/55962500000000000000000000000000 : ℝ)*base71 + (11372394755989/4477000000000000000000000000 : ℝ)*base73 + (33615890297189641/55962500000000000000000000000000 : ℝ)*base76 + (389055637631185359/55962500000000000000000000000000 : ℝ)*base77 + (54891916926497859/55962500000000000000000000000000 : ℝ)*base79 + (1875339132837/895400000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (57763221/5000000000000000000000 : ℝ)*base89 + (57763221/5000000000000000000000 : ℝ)*base91 + (57763221/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1148148730367489445600694149/139906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (125717217/10000000000000 : ℝ)*(base19) + (345139621/25000000000000 : ℝ)*(base23) + (169830503/100000000000000 : ℝ)*(upper3) + (52592669/100000000000000 : ℝ)*(lower4) + (41776033/25000000000000 : ℝ)*(upper5) + (867006025782637/25000000000000 : ℝ)*(major0) + (867006025782637/25000000000000 : ℝ)*(major1) + (867006025782637/25000000000000 : ℝ)*(major2) + (9913854883/50000000000000 : ℝ)*(sp1) + (10895474271/50000000000000 : ℝ)*(sp2) + (486117792774791/10000000000000 : ℝ)*(sp4) + (2430578421432987/50000000000000 : ℝ)*(sp5) + (1215288689060221/25000000000000 : ℝ)*(sp6) + (414974000992251/20000000000000 : ℝ)*(sp7) + (414974000992251/20000000000000 : ℝ)*(f.failure) + (486117792774791/10000000000000 : ℝ)*(f.sum) + (100121785680277/22385000000000000000000000000 : ℝ)*base65 + (901165253981568617/279812500000000000000000000000000 : ℝ)*base67 + (262211195456243883/279812500000000000000000000000000 : ℝ)*base70 + (818304657889256117/279812500000000000000000000000000 : ℝ)*base71 + (15716552693909/11192500000000000000000000000 : ℝ)*base74 + (2579382955112006117/279812500000000000000000000000000 : ℝ)*base75 + (2319501432332006117/279812500000000000000000000000000 : ℝ)*base77 + (779035735484056383/279812500000000000000000000000000 : ℝ)*base80 + (24849621326957/22385000000000000000000000000 : ℝ)*base81 + (2880913/2000000000000000000000 : ℝ)*base89 + (2880913/2000000000000000000000 : ℝ)*base91 + (2880913/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1559_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (621/4000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1381/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11081/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1559_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1559_s5_0 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-900375523/5000000000 : ℝ)*x 0 + (678400237/1250000000 : ℝ)*x 1 + (2609830597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (900375523/5000000000 : ℝ)^4615 ≤ (441774678353/4000000000000 : ℝ)^3591 := by
    have hnat : (900375523 : ℕ)^4615*4000000000000^3591 ≤ 441774678353^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900375523 5000000000 441774678353 4000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678400237/1250000000 : ℝ)^4615 ≤ (45591971286721/100000000000000 : ℝ)^3591 := by
    have hnat : (678400237 : ℕ)^4615*100000000000000^3591 ≤ 45591971286721^3591*1250000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678400237 1250000000 45591971286721 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609830597/5000000000 : ℝ)^4615 ≤ (43363661738459/100000000000000 : ℝ)^3591 := by
    have hnat : (2609830597 : ℕ)^4615*100000000000000^3591 ≤ 43363661738459^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609830597 5000000000 43363661738459 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-900375523/5000000000 : ℝ), (678400237/1250000000 : ℝ), (2609830597/5000000000 : ℝ)] ![(441774678353/4000000000000 : ℝ), (45591971286721/100000000000000 : ℝ), (43363661738459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-900375523/5000000000 : ℝ)|^4615 ≤ (441774678353/4000000000000 : ℝ)^3591
        have hw : |(-900375523/5000000000 : ℝ)|=(900375523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678400237/1250000000 : ℝ)|^4615 ≤ (45591971286721/100000000000000 : ℝ)^3591
        have hw : |(678400237/1250000000 : ℝ)|=(678400237/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609830597/5000000000 : ℝ)|^4615 ≤ (43363661738459/100000000000000 : ℝ)^3591
        have hw : |(2609830597/5000000000 : ℝ)|=(2609830597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s5_1 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674432261/5000000000 : ℝ)*x 0 + (-1906947413/10000000000 : ℝ)*x 1 + (2609830597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674432261/5000000000 : ℝ)^4615 ≤ (8949595247663/20000000000000 : ℝ)^3591 := by
    have hnat : (2674432261 : ℕ)^4615*20000000000000^3591 ≤ 8949595247663^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674432261 5000000000 8949595247663 20000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1906947413/10000000000 : ℝ)^4615 ≤ (23219457053/195312500000 : ℝ)^3591 := by
    have hnat : (1906947413 : ℕ)^4615*195312500000^3591 ≤ 23219457053^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906947413 10000000000 23219457053 195312500000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609830597/5000000000 : ℝ)^4615 ≤ (43363661738459/100000000000000 : ℝ)^3591 := by
    have hnat : (2609830597 : ℕ)^4615*100000000000000^3591 ≤ 43363661738459^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609830597 5000000000 43363661738459 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674432261/5000000000 : ℝ), (-1906947413/10000000000 : ℝ), (2609830597/5000000000 : ℝ)] ![(8949595247663/20000000000000 : ℝ), (23219457053/195312500000 : ℝ), (43363661738459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674432261/5000000000 : ℝ)|^4615 ≤ (8949595247663/20000000000000 : ℝ)^3591
        have hw : |(2674432261/5000000000 : ℝ)|=(2674432261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1906947413/10000000000 : ℝ)|^4615 ≤ (23219457053/195312500000 : ℝ)^3591
        have hw : |(-1906947413/10000000000 : ℝ)|=(1906947413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609830597/5000000000 : ℝ)|^4615 ≤ (43363661738459/100000000000000 : ℝ)^3591
        have hw : |(2609830597/5000000000 : ℝ)|=(2609830597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s5_2 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2674432261/5000000000 : ℝ)*x 0 + (2609830597/5000000000 : ℝ)*x 1 + (-1906947413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674432261/5000000000 : ℝ)^4615 ≤ (8949595247663/20000000000000 : ℝ)^3591 := by
    have hnat : (2674432261 : ℕ)^4615*20000000000000^3591 ≤ 8949595247663^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674432261 5000000000 8949595247663 20000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2609830597/5000000000 : ℝ)^4615 ≤ (43363661738459/100000000000000 : ℝ)^3591 := by
    have hnat : (2609830597 : ℕ)^4615*100000000000000^3591 ≤ 43363661738459^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609830597 5000000000 43363661738459 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1906947413/10000000000 : ℝ)^4615 ≤ (23219457053/195312500000 : ℝ)^3591 := by
    have hnat : (1906947413 : ℕ)^4615*195312500000^3591 ≤ 23219457053^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906947413 10000000000 23219457053 195312500000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674432261/5000000000 : ℝ), (2609830597/5000000000 : ℝ), (-1906947413/10000000000 : ℝ)] ![(8949595247663/20000000000000 : ℝ), (43363661738459/100000000000000 : ℝ), (23219457053/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674432261/5000000000 : ℝ)|^4615 ≤ (8949595247663/20000000000000 : ℝ)^3591
        have hw : |(2674432261/5000000000 : ℝ)|=(2674432261/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2609830597/5000000000 : ℝ)|^4615 ≤ (43363661738459/100000000000000 : ℝ)^3591
        have hw : |(2609830597/5000000000 : ℝ)|=(2609830597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1906947413/10000000000 : ℝ)|^4615 ≤ (23219457053/195312500000 : ℝ)^3591
        have hw : |(-1906947413/10000000000 : ℝ)|=(1906947413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s5_3 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4248373899/10000000000 : ℝ)*x 0 + (4010935953/10000000000 : ℝ)*x 1 + (449717959/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4248373899/10000000000 : ℝ)^4615 ≤ (33281869699139/100000000000000 : ℝ)^3591 := by
    have hnat : (4248373899 : ℕ)^4615*100000000000000^3591 ≤ 33281869699139^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248373899 10000000000 33281869699139 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4010935953/10000000000 : ℝ)^4615 ≤ (30910664045053/100000000000000 : ℝ)^3591 := by
    have hnat : (4010935953 : ℕ)^4615*100000000000000^3591 ≤ 30910664045053^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4010935953 10000000000 30910664045053 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449717959/1000000000 : ℝ)^4615 ≤ (17903733123167/50000000000000 : ℝ)^3591 := by
    have hnat : (449717959 : ℕ)^4615*50000000000000^3591 ≤ 17903733123167^3591*1000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449717959 1000000000 17903733123167 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4248373899/10000000000 : ℝ), (4010935953/10000000000 : ℝ), (449717959/1000000000 : ℝ)] ![(33281869699139/100000000000000 : ℝ), (30910664045053/100000000000000 : ℝ), (17903733123167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4248373899/10000000000 : ℝ)|^4615 ≤ (33281869699139/100000000000000 : ℝ)^3591
        have hw : |(4248373899/10000000000 : ℝ)|=(4248373899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4010935953/10000000000 : ℝ)|^4615 ≤ (30910664045053/100000000000000 : ℝ)^3591
        have hw : |(4010935953/10000000000 : ℝ)|=(4010935953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449717959/1000000000 : ℝ)|^4615 ≤ (17903733123167/50000000000000 : ℝ)^3591
        have hw : |(449717959/1000000000 : ℝ)|=(449717959/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s5_4 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-900389177/5000000000 : ℝ)*x 0 + (5220739881/10000000000 : ℝ)*x 1 + (5426115137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (900389177/5000000000 : ℝ)^4615 ≤ (5522291102213/50000000000000 : ℝ)^3591 := by
    have hnat : (900389177 : ℕ)^4615*50000000000000^3591 ≤ 5522291102213^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      900389177 5000000000 5522291102213 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220739881/10000000000 : ℝ)^4615 ≤ (10843794743009/25000000000000 : ℝ)^3591 := by
    have hnat : (5220739881 : ℕ)^4615*25000000000000^3591 ≤ 10843794743009^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220739881 10000000000 10843794743009 25000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5426115137/10000000000 : ℝ)^4615 ≤ (45580238814403/100000000000000 : ℝ)^3591 := by
    have hnat : (5426115137 : ℕ)^4615*100000000000000^3591 ≤ 45580238814403^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426115137 10000000000 45580238814403 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-900389177/5000000000 : ℝ), (5220739881/10000000000 : ℝ), (5426115137/10000000000 : ℝ)] ![(5522291102213/50000000000000 : ℝ), (10843794743009/25000000000000 : ℝ), (45580238814403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-900389177/5000000000 : ℝ)|^4615 ≤ (5522291102213/50000000000000 : ℝ)^3591
        have hw : |(-900389177/5000000000 : ℝ)|=(900389177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220739881/10000000000 : ℝ)|^4615 ≤ (10843794743009/25000000000000 : ℝ)^3591
        have hw : |(5220739881/10000000000 : ℝ)|=(5220739881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5426115137/10000000000 : ℝ)|^4615 ≤ (45580238814403/100000000000000 : ℝ)^3591
        have hw : |(5426115137/10000000000 : ℝ)|=(5426115137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s5_5 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294029059/10000000000 : ℝ)*x 0 + (-1700493589/10000000000 : ℝ)*x 1 + (271305757/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294029059/10000000000 : ℝ)^4615 ≤ (44159277928721/100000000000000 : ℝ)^3591 := by
    have hnat : (5294029059 : ℕ)^4615*100000000000000^3591 ≤ 44159277928721^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294029059 10000000000 44159277928721 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1700493589/10000000000 : ℝ)^4615 ≤ (2052096641891/20000000000000 : ℝ)^3591 := by
    have hnat : (1700493589 : ℕ)^4615*20000000000000^3591 ≤ 2052096641891^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1700493589 10000000000 2052096641891 20000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (271305757/500000000 : ℝ)^4615 ≤ (4558023884679/10000000000000 : ℝ)^3591 := by
    have hnat : (271305757 : ℕ)^4615*10000000000000^3591 ≤ 4558023884679^3591*500000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271305757 500000000 4558023884679 10000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294029059/10000000000 : ℝ), (-1700493589/10000000000 : ℝ), (271305757/500000000 : ℝ)] ![(44159277928721/100000000000000 : ℝ), (2052096641891/20000000000000 : ℝ), (4558023884679/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294029059/10000000000 : ℝ)|^4615 ≤ (44159277928721/100000000000000 : ℝ)^3591
        have hw : |(5294029059/10000000000 : ℝ)|=(5294029059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1700493589/10000000000 : ℝ)|^4615 ≤ (2052096641891/20000000000000 : ℝ)^3591
        have hw : |(-1700493589/10000000000 : ℝ)|=(1700493589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(271305757/500000000 : ℝ)|^4615 ≤ (4558023884679/10000000000000 : ℝ)^3591
        have hw : |(271305757/500000000 : ℝ)|=(271305757/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s5_6 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058805809/2000000000 : ℝ)*x 0 + (5426115243/10000000000 : ℝ)*x 1 + (-340098693/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058805809/2000000000 : ℝ)^4615 ≤ (22079638889321/50000000000000 : ℝ)^3591 := by
    have hnat : (1058805809 : ℕ)^4615*50000000000000^3591 ≤ 22079638889321^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058805809 2000000000 22079638889321 50000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5426115243/10000000000 : ℝ)^4615 ≤ (45580239958729/100000000000000 : ℝ)^3591 := by
    have hnat : (5426115243 : ℕ)^4615*100000000000000^3591 ≤ 45580239958729^3591*10000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5426115243 10000000000 45580239958729 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (340098693/2000000000 : ℝ)^4615 ≤ (10260482247907/100000000000000 : ℝ)^3591 := by
    have hnat : (340098693 : ℕ)^4615*100000000000000^3591 ≤ 10260482247907^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      340098693 2000000000 10260482247907 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058805809/2000000000 : ℝ), (5426115243/10000000000 : ℝ), (-340098693/2000000000 : ℝ)] ![(22079638889321/50000000000000 : ℝ), (45580239958729/100000000000000 : ℝ), (10260482247907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058805809/2000000000 : ℝ)|^4615 ≤ (22079638889321/50000000000000 : ℝ)^3591
        have hw : |(1058805809/2000000000 : ℝ)|=(1058805809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5426115243/10000000000 : ℝ)|^4615 ≤ (45580239958729/100000000000000 : ℝ)^3591
        have hw : |(5426115243/10000000000 : ℝ)|=(5426115243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-340098693/2000000000 : ℝ)|^4615 ≤ (10260482247907/100000000000000 : ℝ)^3591
        have hw : |(-340098693/2000000000 : ℝ)|=(340098693/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1559_s5_7 (p : ℝ) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (849687503/2000000000 : ℝ)*x 0 + (2247326293/5000000000 : ℝ)*x 1 + (62710651/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (849687503/2000000000 : ℝ)^4615 ≤ (33282510183559/100000000000000 : ℝ)^3591 := by
    have hnat : (849687503 : ℕ)^4615*100000000000000^3591 ≤ 33282510183559^3591*2000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849687503 2000000000 33282510183559 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247326293/5000000000 : ℝ)^4615 ≤ (55908766061/156250000000 : ℝ)^3591 := by
    have hnat : (2247326293 : ℕ)^4615*156250000000^3591 ≤ 55908766061^3591*5000000000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247326293 5000000000 55908766061 156250000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (62710651/156250000 : ℝ)^4615 ≤ (30935879528571/100000000000000 : ℝ)^3591 := by
    have hnat : (62710651 : ℕ)^4615*100000000000000^3591 ≤ 30935879528571^3591*156250000^4615 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      62710651 156250000 30935879528571 100000000000000 4615 3591 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4615/1024 : ℝ)) 4615 3591 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(849687503/2000000000 : ℝ), (2247326293/5000000000 : ℝ), (62710651/156250000 : ℝ)] ![(33282510183559/100000000000000 : ℝ), (55908766061/156250000000 : ℝ), (30935879528571/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(849687503/2000000000 : ℝ)|^4615 ≤ (33282510183559/100000000000000 : ℝ)^3591
        have hw : |(849687503/2000000000 : ℝ)|=(849687503/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247326293/5000000000 : ℝ)|^4615 ≤ (55908766061/156250000000 : ℝ)^3591
        have hw : |(2247326293/5000000000 : ℝ)|=(2247326293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(62710651/156250000 : ℝ)|^4615 ≤ (30935879528571/100000000000000 : ℝ)^3591
        have hw : |(62710651/156250000 : ℝ)|=(62710651/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1559_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2217/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11081/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15489/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11081/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15489/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11081/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11081/100000 : ℝ) ^ (4613/1024 : ℝ) ≤ (4965238967748657/100000000000000000000 : ℝ) := by
    have hpowers : (11081/100000 : ℝ)^4613 ≤ (4965238967748657/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11081 : ℕ)^4613*100000000000000000000^1024 ≤ 4965238967748657^1024*100000^4613 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11081 100000 4965238967748657 100000000000000000000 4613 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11081/100000 : ℝ)) (X := (4965238967748657/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15489/100000 : ℝ) ^ (4613/1024 : ℝ) ≤ (4489316666413027/20000000000000000000 : ℝ) := by
    have hpowers : (15489/100000 : ℝ)^4613 ≤ (4489316666413027/20000000000000000000 : ℝ)^1024 := by
      have hnat : (15489 : ℕ)^4613*20000000000000000000^1024 ≤ 4489316666413027^1024*100000^4613 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15489 100000 4489316666413027 20000000000000000000 4613 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15489/100000 : ℝ)) (X := (4489316666413027/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004965238967748657/50000000000000000000 : ℝ) ≤ (10000220429581683/10000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (50004965238967748657/50000000000000000000 : ℝ)^1024 ≤ (10000220429581683/10000000000000000 : ℝ)^4613 := by
      have hnat : (50004965238967748657 : ℕ)^1024*10000000000000000^4613 ≤ 10000220429581683^4613*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004965238967748657 50000000000000000000 10000220429581683 10000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000220429581683/10000000000000000 : ℝ)) (X := (50004965238967748657/50000000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (3125856619446869181/3125000000000000000 : ℝ) ≤ (625038026654727/625000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (3125856619446869181/3125000000000000000 : ℝ)^1024 ≤ (625038026654727/625000000000000 : ℝ)^4613 := by
      have hnat : (3125856619446869181 : ℕ)^1024*625000000000000^4613 ≤ 625038026654727^4613*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125856619446869181 3125000000000000000 625038026654727 625000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625038026654727/625000000000000 : ℝ)) (X := (3125856619446869181/3125000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004489316666413027/10000000000000000000 : ℝ) ≤ (10000996423369581/10000000000000000 : ℝ) ^ (4613/1024 : ℝ) := by
    have hpowers : (10004489316666413027/10000000000000000000 : ℝ)^1024 ≤ (10000996423369581/10000000000000000 : ℝ)^4613 := by
      have hnat : (10004489316666413027 : ℕ)^1024*10000000000000000^4613 ≤ 10000996423369581^4613*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004489316666413027 10000000000000000000 10000996423369581 10000000000000000 1024 4613 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000996423369581/10000000000000000 : ℝ)) (X := (10004489316666413027/10000000000000000000 : ℝ)) (by norm_num) 4613 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4965238967748657/100000000000000000000 : ℝ) ≤ ((22036186433216180463/22040000000000000000 : ℝ)+2*(387996893949/440800000000000 : ℝ)*(11081/100000 : ℝ))^(4613/1024 : ℝ) := by
    rw [show (22036186433216180463/22040000000000000000 : ℝ)+2*(387996893949/440800000000000 : ℝ)*(11081/100000 : ℝ)=(10000220429581683/10000000000000000 : ℝ) by norm_num, show 1+2*(4965238967748657/100000000000000000000 : ℝ)=(50004965238967748657/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4489316666413027/20000000000000000000 : ℝ)+(4965238967748657/100000000000000000000 : ℝ) ≤ ((22036186433216180463/22040000000000000000 : ℝ)+(387996893949/440800000000000 : ℝ)*((15489/100000 : ℝ)+(11081/100000 : ℝ)))^(4613/1024 : ℝ) := by
    rw [show (22036186433216180463/22040000000000000000 : ℝ)+(387996893949/440800000000000 : ℝ)*((15489/100000 : ℝ)+(11081/100000 : ℝ))=(625038026654727/625000000000000 : ℝ) by norm_num, show 1+(4489316666413027/20000000000000000000 : ℝ)+(4965238967748657/100000000000000000000 : ℝ)=(3125856619446869181/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4489316666413027/20000000000000000000 : ℝ) ≤ ((22036186433216180463/22040000000000000000 : ℝ)+2*(387996893949/440800000000000 : ℝ)*(15489/100000 : ℝ))^(4613/1024 : ℝ) := by
    rw [show (22036186433216180463/22040000000000000000 : ℝ)+2*(387996893949/440800000000000 : ℝ)*(15489/100000 : ℝ)=(10000996423369581/10000000000000000 : ℝ) by norm_num, show 1+2*(4489316666413027/20000000000000000000 : ℝ)=(10004489316666413027/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22036186433216180463/22040000000000000000 : ℝ)*(X 1 0+X 2 0)+(387996893949/440800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (11081/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (22036186433216180463/22040000000000000000 : ℝ)) (alpha := (387996893949/440800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22036186433216180463/22040000000000000000 : ℝ)*(X 0 1+X 2 1)+(387996893949/440800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (11081/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (22036186433216180463/22040000000000000000 : ℝ)) (alpha := (387996893949/440800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22036186433216180463/22040000000000000000 : ℝ)*(X 0 2+X 1 2)+(387996893949/440800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4613/1024 : ℝ)) (lo := (11081/100000 : ℝ)) (hi := (15489/100000 : ℝ)) (c := (22036186433216180463/22040000000000000000 : ℝ)) (alpha := (387996893949/440800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-900375523/5000000000 : ℝ)*X 0 0+(678400237/1250000000 : ℝ)*X 0 1+(2609830597/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674432261/5000000000 : ℝ)*X 1 0+(-1906947413/10000000000 : ℝ)*X 1 1+(2609830597/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674432261/5000000000 : ℝ)*X 2 0+(2609830597/5000000000 : ℝ)*X 2 1+(-1906947413/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4248373899/10000000000 : ℝ)*X 0 0+(4010935953/10000000000 : ℝ)*X 0 1+(449717959/1000000000 : ℝ)*X 0 2+(4248373899/10000000000 : ℝ)*X 1 0+(4010935953/10000000000 : ℝ)*X 1 1+(449717959/1000000000 : ℝ)*X 1 2+(4248373899/10000000000 : ℝ)*X 2 0+(4010935953/10000000000 : ℝ)*X 2 1+(449717959/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-900389177/5000000000 : ℝ)*X 0 0+(5220739881/10000000000 : ℝ)*X 0 1+(5426115137/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294029059/10000000000 : ℝ)*X 1 0+(-1700493589/10000000000 : ℝ)*X 1 1+(271305757/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058805809/2000000000 : ℝ)*X 2 0+(5426115243/10000000000 : ℝ)*X 2 1+(-340098693/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((849687503/2000000000 : ℝ)*X 0 0+(2247326293/5000000000 : ℝ)*X 0 1+(62710651/156250000 : ℝ)*X 0 2+(849687503/2000000000 : ℝ)*X 1 0+(2247326293/5000000000 : ℝ)*X 1 1+(62710651/156250000 : ℝ)*X 1 2+(849687503/2000000000 : ℝ)*X 2 0+(2247326293/5000000000 : ℝ)*X 2 1+(62710651/156250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1559_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3131046379131352091841/580000000000000000000000000 : ℝ) := by norm_num
    linear_combination (459098943/50000000000000 : ℝ)*(base19) + (428721739/50000000000000 : ℝ)*(base23) + (3249671/10000000000000 : ℝ)*(lower2) + (133167593/100000000000000 : ℝ)*(upper3) + (89354063/100000000000000 : ℝ)*(upper5) + (1718739367843077/50000000000000 : ℝ)*(major0) + (1718739367843077/50000000000000 : ℝ)*(major1) + (1718739367843077/50000000000000 : ℝ)*(major2) + (4818347339666103/100000000000000 : ℝ)*(sp0) + (2409180615826527/50000000000000 : ℝ)*(sp1) + (2409180646203731/50000000000000 : ℝ)*(sp2) + (1028294147355857/50000000000000 : ℝ)*(sp3) + (14810184837/100000000000000 : ℝ)*(sp4) + (855858057/12500000000000 : ℝ)*(sp7) + (205659514157617/10000000000000 : ℝ)*(f.failure) + (240918107492547/5000000000000 : ℝ)*(f.sum) + (1813866415933/580000000000000000000000000 : ℝ)*base66 + (607051454987623929/58000000000000000000000000000000 : ℝ)*base67 + (161072962571623929/58000000000000000000000000000000 : ℝ)*base69 + (237267164130376071/58000000000000000000000000000000 : ℝ)*base72 + (178503377787/580000000000000000000000000 : ℝ)*base73 + (168293856721623929/58000000000000000000000000000000 : ℝ)*base75 + (92633316738376071/58000000000000000000000000000000 : ℝ)*base78 + (119196353706376071/58000000000000000000000000000000 : ℝ)*base80 + (4122410573773/580000000000000000000000000 : ℝ)*base82 + (3539571/1000000000000000000000 : ℝ)*base89 + (3539571/1000000000000000000000 : ℝ)*base91 + (3539571/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1609330490795306148426188019/275500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (846568953/100000000000000 : ℝ)*(base19) + (122852647/12500000000000 : ℝ)*(base23) + (88773887/50000000000000 : ℝ)*(lower1) + (40380669/100000000000000 : ℝ)*(upper2) + (211123853/100000000000000 : ℝ)*(upper3) + (92022533/100000000000000 : ℝ)*(upper5) + (868423020818443/25000000000000 : ℝ)*(major0) + (868423020818443/25000000000000 : ℝ)*(major1) + (868423020818443/25000000000000 : ℝ)*(major2) + (7033480237/100000000000000 : ℝ)*(sp2) + (1217280723533201/25000000000000 : ℝ)*(sp4) + (1217280511890963/25000000000000 : ℝ)*(sp5) + (4869114877831391/100000000000000 : ℝ)*(sp6) + (2078261077698401/100000000000000 : ℝ)*(sp7) + (2078261077698401/100000000000000 : ℝ)*(f.failure) + (1217280723533201/25000000000000 : ℝ)*(f.sum) + (41454978532083/5510000000000000000000000000 : ℝ)*base66 + (3568747631907029109/551000000000000000000000000000000 : ℝ)*base67 + (11814736973705029109/551000000000000000000000000000000 : ℝ)*base69 + (224608804284029109/551000000000000000000000000000000 : ℝ)*base71 + (2794832730827/5510000000000000000000000000 : ℝ)*base73 + (143859885973029109/551000000000000000000000000000000 : ℝ)*base75 + (3641785153693029109/551000000000000000000000000000000 : ℝ)*base77 + (1050314155390029109/551000000000000000000000000000000 : ℝ)*base79 + (35601855351727/5510000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1583363/10000000000000000000000 : ℝ)*base89 + (1583363/10000000000000000000000 : ℝ)*base91 + (1583363/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1559_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15489/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11081/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1559_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1559_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7921/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1559_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1559_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1559_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4613/1024 : ℝ) ≤ p) (hpb : p ≤ (4615/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (167144163/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7921/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2689/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2217/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1559_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
