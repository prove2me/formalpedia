-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1217_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:09:37.916962+00:00
-- url     : https://prove2.me/submissions/e9f29f00-79d0-4d37-8edf-0af8a45e3aa1

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
theorem support_rectangle_w1217_s0_0 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1868298561/10000000000 : ℝ)*x 0 + (603715767/1000000000 : ℝ)*x 1 + (2394941919/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1868298561/10000000000 : ℝ)^4205 ≤ (10887209211491/100000000000000 : ℝ)^3181 := by
    have hnat : (1868298561 : ℕ)^4205*100000000000000^3181 ≤ 10887209211491^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868298561 10000000000 10887209211491 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (603715767/1000000000 : ℝ)^4205 ≤ (51319216663459/100000000000000 : ℝ)^3181 := by
    have hnat : (603715767 : ℕ)^4205*100000000000000^3181 ≤ 51319216663459^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      603715767 1000000000 51319216663459 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2394941919/5000000000 : ℝ)^4205 ≤ (18896787057641/50000000000000 : ℝ)^3181 := by
    have hnat : (2394941919 : ℕ)^4205*50000000000000^3181 ≤ 18896787057641^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2394941919 5000000000 18896787057641 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1868298561/10000000000 : ℝ), (603715767/1000000000 : ℝ), (2394941919/5000000000 : ℝ)] ![(10887209211491/100000000000000 : ℝ), (51319216663459/100000000000000 : ℝ), (18896787057641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1868298561/10000000000 : ℝ)|^4205 ≤ (10887209211491/100000000000000 : ℝ)^3181
        have hw : |(-1868298561/10000000000 : ℝ)|=(1868298561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(603715767/1000000000 : ℝ)|^4205 ≤ (51319216663459/100000000000000 : ℝ)^3181
        have hw : |(603715767/1000000000 : ℝ)|=(603715767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2394941919/5000000000 : ℝ)|^4205 ≤ (18896787057641/50000000000000 : ℝ)^3181
        have hw : |(2394941919/5000000000 : ℝ)|=(2394941919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s0_1 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2756283987/5000000000 : ℝ)*x 0 + (-645503747/2500000000 : ℝ)*x 1 + (957976761/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2756283987/5000000000 : ℝ)^4205 ≤ (22754267832669/50000000000000 : ℝ)^3181 := by
    have hnat : (2756283987 : ℕ)^4205*50000000000000^3181 ≤ 22754267832669^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2756283987 5000000000 22754267832669 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (645503747/2500000000 : ℝ)^4205 ≤ (16697890546153/100000000000000 : ℝ)^3181 := by
    have hnat : (645503747 : ℕ)^4205*100000000000000^3181 ≤ 16697890546153^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      645503747 2500000000 16697890546153 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (957976761/2000000000 : ℝ)^4205 ≤ (9448393442771/25000000000000 : ℝ)^3181 := by
    have hnat : (957976761 : ℕ)^4205*25000000000000^3181 ≤ 9448393442771^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      957976761 2000000000 9448393442771 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2756283987/5000000000 : ℝ), (-645503747/2500000000 : ℝ), (957976761/2000000000 : ℝ)] ![(22754267832669/50000000000000 : ℝ), (16697890546153/100000000000000 : ℝ), (9448393442771/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2756283987/5000000000 : ℝ)|^4205 ≤ (22754267832669/50000000000000 : ℝ)^3181
        have hw : |(2756283987/5000000000 : ℝ)|=(2756283987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-645503747/2500000000 : ℝ)|^4205 ≤ (16697890546153/100000000000000 : ℝ)^3181
        have hw : |(-645503747/2500000000 : ℝ)|=(645503747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(957976761/2000000000 : ℝ)|^4205 ≤ (9448393442771/25000000000000 : ℝ)^3181
        have hw : |(957976761/2000000000 : ℝ)|=(957976761/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s0_2 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (344535497/625000000 : ℝ)*x 0 + (598735479/1250000000 : ℝ)*x 1 + (-2582014983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (344535497/625000000 : ℝ)^4205 ≤ (22754267712627/50000000000000 : ℝ)^3181 := by
    have hnat : (344535497 : ℕ)^4205*50000000000000^3181 ≤ 22754267712627^3181*625000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344535497 625000000 22754267712627 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598735479/1250000000 : ℝ)^4205 ≤ (37793574052701/100000000000000 : ℝ)^3181 := by
    have hnat : (598735479 : ℕ)^4205*100000000000000^3181 ≤ 37793574052701^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598735479 1250000000 37793574052701 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2582014983/10000000000 : ℝ)^4205 ≤ (16697890503409/100000000000000 : ℝ)^3181 := by
    have hnat : (2582014983 : ℕ)^4205*100000000000000^3181 ≤ 16697890503409^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2582014983 10000000000 16697890503409 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(344535497/625000000 : ℝ), (598735479/1250000000 : ℝ), (-2582014983/10000000000 : ℝ)] ![(22754267712627/50000000000000 : ℝ), (37793574052701/100000000000000 : ℝ), (16697890503409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(344535497/625000000 : ℝ)|^4205 ≤ (22754267712627/50000000000000 : ℝ)^3181
        have hw : |(344535497/625000000 : ℝ)|=(344535497/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598735479/1250000000 : ℝ)|^4205 ≤ (37793574052701/100000000000000 : ℝ)^3181
        have hw : |(598735479/1250000000 : ℝ)|=(598735479/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2582014983/10000000000 : ℝ)|^4205 ≤ (16697890503409/100000000000000 : ℝ)^3181
        have hw : |(-2582014983/10000000000 : ℝ)|=(2582014983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s0_3 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1048748027/2500000000 : ℝ)*x 0 + (311785567/1000000000 : ℝ)*x 1 + (2817915227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048748027/2500000000 : ℝ)^4205 ≤ (31716409989911/100000000000000 : ℝ)^3181 := by
    have hnat : (1048748027 : ℕ)^4205*100000000000000^3181 ≤ 31716409989911^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048748027 2500000000 31716409989911 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (311785567/1000000000 : ℝ)^4205 ≤ (10712541471453/50000000000000 : ℝ)^3181 := by
    have hnat : (311785567 : ℕ)^4205*50000000000000^3181 ≤ 10712541471453^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311785567 1000000000 10712541471453 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2817915227/5000000000 : ℝ)^4205 ≤ (23429253524441/50000000000000 : ℝ)^3181 := by
    have hnat : (2817915227 : ℕ)^4205*50000000000000^3181 ≤ 23429253524441^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2817915227 5000000000 23429253524441 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048748027/2500000000 : ℝ), (311785567/1000000000 : ℝ), (2817915227/5000000000 : ℝ)] ![(31716409989911/100000000000000 : ℝ), (10712541471453/50000000000000 : ℝ), (23429253524441/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048748027/2500000000 : ℝ)|^4205 ≤ (31716409989911/100000000000000 : ℝ)^3181
        have hw : |(1048748027/2500000000 : ℝ)|=(1048748027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(311785567/1000000000 : ℝ)|^4205 ≤ (10712541471453/50000000000000 : ℝ)^3181
        have hw : |(311785567/1000000000 : ℝ)|=(311785567/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2817915227/5000000000 : ℝ)|^4205 ≤ (23429253524441/50000000000000 : ℝ)^3181
        have hw : |(2817915227/5000000000 : ℝ)|=(2817915227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s0_4 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1873227529/10000000000 : ℝ)*x 0 + (4822019591/10000000000 : ℝ)*x 1 + (6003886923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1873227529/10000000000 : ℝ)^4205 ≤ (5462597138803/50000000000000 : ℝ)^3181 := by
    have hnat : (1873227529 : ℕ)^4205*50000000000000^3181 ≤ 5462597138803^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873227529 10000000000 5462597138803 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4822019591/10000000000 : ℝ)^4205 ≤ (38129119920261/100000000000000 : ℝ)^3181 := by
    have hnat : (4822019591 : ℕ)^4205*100000000000000^3181 ≤ 38129119920261^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4822019591 10000000000 38129119920261 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6003886923/10000000000 : ℝ)^4205 ≤ (25472842896283/50000000000000 : ℝ)^3181 := by
    have hnat : (6003886923 : ℕ)^4205*50000000000000^3181 ≤ 25472842896283^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6003886923 10000000000 25472842896283 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1873227529/10000000000 : ℝ), (4822019591/10000000000 : ℝ), (6003886923/10000000000 : ℝ)] ![(5462597138803/50000000000000 : ℝ), (38129119920261/100000000000000 : ℝ), (25472842896283/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1873227529/10000000000 : ℝ)|^4205 ≤ (5462597138803/50000000000000 : ℝ)^3181
        have hw : |(-1873227529/10000000000 : ℝ)|=(1873227529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4822019591/10000000000 : ℝ)|^4205 ≤ (38129119920261/100000000000000 : ℝ)^3181
        have hw : |(4822019591/10000000000 : ℝ)|=(4822019591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6003886923/10000000000 : ℝ)|^4205 ≤ (25472842896283/50000000000000 : ℝ)^3181
        have hw : |(6003886923/10000000000 : ℝ)|=(6003886923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s0_5 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5173310453/10000000000 : ℝ)*x 0 + (-171001269/1250000000 : ℝ)*x 1 + (6003888727/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173310453/10000000000 : ℝ)^4205 ≤ (4184344051739/10000000000000 : ℝ)^3181 := by
    have hnat : (5173310453 : ℕ)^4205*10000000000000^3181 ≤ 4184344051739^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173310453 10000000000 4184344051739 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (171001269/1250000000 : ℝ)^4205 ≤ (7210853434041/100000000000000 : ℝ)^3181 := by
    have hnat : (171001269 : ℕ)^4205*100000000000000^3181 ≤ 7210853434041^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      171001269 1250000000 7210853434041 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6003888727/10000000000 : ℝ)^4205 ≤ (50945706028059/100000000000000 : ℝ)^3181 := by
    have hnat : (6003888727 : ℕ)^4205*100000000000000^3181 ≤ 50945706028059^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6003888727 10000000000 50945706028059 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173310453/10000000000 : ℝ), (-171001269/1250000000 : ℝ), (6003888727/10000000000 : ℝ)] ![(4184344051739/10000000000000 : ℝ), (7210853434041/100000000000000 : ℝ), (50945706028059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173310453/10000000000 : ℝ)|^4205 ≤ (4184344051739/10000000000000 : ℝ)^3181
        have hw : |(5173310453/10000000000 : ℝ)|=(5173310453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-171001269/1250000000 : ℝ)|^4205 ≤ (7210853434041/100000000000000 : ℝ)^3181
        have hw : |(-171001269/1250000000 : ℝ)|=(171001269/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6003888727/10000000000 : ℝ)|^4205 ≤ (50945706028059/100000000000000 : ℝ)^3181
        have hw : |(6003888727/10000000000 : ℝ)|=(6003888727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s0_6 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5173311363/10000000000 : ℝ)*x 0 + (3001943693/5000000000 : ℝ)*x 1 + (-342002729/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173311363/10000000000 : ℝ)^4205 ≤ (1046086256179/2500000000000 : ℝ)^3181 := by
    have hnat : (5173311363 : ℕ)^4205*2500000000000^3181 ≤ 1046086256179^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173311363 10000000000 1046086256179 2500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3001943693/5000000000 : ℝ)^4205 ≤ (50945690986043/100000000000000 : ℝ)^3181 := by
    have hnat : (3001943693 : ℕ)^4205*100000000000000^3181 ≤ 50945690986043^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3001943693 5000000000 50945690986043 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (342002729/2500000000 : ℝ)^4205 ≤ (721085875749/10000000000000 : ℝ)^3181 := by
    have hnat : (342002729 : ℕ)^4205*10000000000000^3181 ≤ 721085875749^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342002729 2500000000 721085875749 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173311363/10000000000 : ℝ), (3001943693/5000000000 : ℝ), (-342002729/2500000000 : ℝ)] ![(1046086256179/2500000000000 : ℝ), (50945690986043/100000000000000 : ℝ), (721085875749/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173311363/10000000000 : ℝ)|^4205 ≤ (1046086256179/2500000000000 : ℝ)^3181
        have hw : |(5173311363/10000000000 : ℝ)|=(5173311363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3001943693/5000000000 : ℝ)|^4205 ≤ (50945690986043/100000000000000 : ℝ)^3181
        have hw : |(3001943693/5000000000 : ℝ)|=(3001943693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-342002729/2500000000 : ℝ)|^4205 ≤ (721085875749/10000000000000 : ℝ)^3181
        have hw : |(-342002729/2500000000 : ℝ)|=(342002729/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s0_7 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4204941743/10000000000 : ℝ)*x 0 + (1114191899/2000000000 : ℝ)*x 1 + (3185017007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4204941743/10000000000 : ℝ)^4205 ≤ (31815888215009/100000000000000 : ℝ)^3181 := by
    have hnat : (4204941743 : ℕ)^4205*100000000000000^3181 ≤ 31815888215009^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4204941743 10000000000 31815888215009 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1114191899/2000000000 : ℝ)^4205 ≤ (9229368373557/20000000000000 : ℝ)^3181 := by
    have hnat : (1114191899 : ℕ)^4205*20000000000000^3181 ≤ 9229368373557^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1114191899 2000000000 9229368373557 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3185017007/10000000000 : ℝ)^4205 ≤ (11018634953477/50000000000000 : ℝ)^3181 := by
    have hnat : (3185017007 : ℕ)^4205*50000000000000^3181 ≤ 11018634953477^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3185017007 10000000000 11018634953477 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4204941743/10000000000 : ℝ), (1114191899/2000000000 : ℝ), (3185017007/10000000000 : ℝ)] ![(31815888215009/100000000000000 : ℝ), (9229368373557/20000000000000 : ℝ), (11018634953477/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4204941743/10000000000 : ℝ)|^4205 ≤ (31815888215009/100000000000000 : ℝ)^3181
        have hw : |(4204941743/10000000000 : ℝ)|=(4204941743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1114191899/2000000000 : ℝ)|^4205 ≤ (9229368373557/20000000000000 : ℝ)^3181
        have hw : |(1114191899/2000000000 : ℝ)|=(1114191899/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3185017007/10000000000 : ℝ)|^4205 ≤ (11018634953477/50000000000000 : ℝ)^3181
        have hw : |(3185017007/10000000000 : ℝ)|=(3185017007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1217_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (359/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2753/10000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8409/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8409 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8409*1^2048 ≤ 0^2048*1^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8409/2048 : ℝ) ≤ (1161570109084955053/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8409 ≤ (1161570109084955053/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8409*50000000000000000000^2048 ≤ 1161570109084955053^2048*5^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1161570109084955053 50000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1161570109084955053/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8409 := by
      have hnat : (1 : ℕ)^2048*1^8409 ≤ 1^8409*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51161570109084955053/50000000000000000000 : ℝ) ≤ (2011217851091563/2000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (51161570109084955053/50000000000000000000 : ℝ)^2048 ≤ (2011217851091563/2000000000000000 : ℝ)^8409 := by
      have hnat : (51161570109084955053 : ℕ)^2048*2000000000000000^8409 ≤ 2011217851091563^8409*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51161570109084955053 50000000000000000000 2011217851091563 2000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2011217851091563/2000000000000000 : ℝ)) (X := (51161570109084955053/50000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26161570109084955053/25000000000000000000 : ℝ) ≤ (1011217851091563/1000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (26161570109084955053/25000000000000000000 : ℝ)^2048 ≤ (1011217851091563/1000000000000000 : ℝ)^8409 := by
      have hnat : (26161570109084955053 : ℕ)^2048*1000000000000000^8409 ≤ 1011217851091563^8409*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26161570109084955053 25000000000000000000 1011217851091563 1000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1011217851091563/1000000000000000 : ℝ)) (X := (26161570109084955053/25000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11217851091563/800000000000000 : ℝ)*(0 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11217851091563/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1161570109084955053/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11217851091563/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8409/2048 : ℝ) := by
    rw [show (1 : ℝ)+(11217851091563/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2011217851091563/2000000000000000 : ℝ) by norm_num, show 1+(1161570109084955053/50000000000000000000 : ℝ)+(0 : ℝ)=(51161570109084955053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1161570109084955053/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11217851091563/800000000000000 : ℝ)*(2/5 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(11217851091563/800000000000000 : ℝ)*(2/5 : ℝ)=(1011217851091563/1000000000000000 : ℝ) by norm_num, show 1+2*(1161570109084955053/50000000000000000000 : ℝ)=(26161570109084955053/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11217851091563/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11217851091563/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11217851091563/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11217851091563/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11217851091563/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11217851091563/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1868298561/10000000000 : ℝ)*X 0 0+(603715767/1000000000 : ℝ)*X 0 1+(2394941919/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2756283987/5000000000 : ℝ)*X 1 0+(-645503747/2500000000 : ℝ)*X 1 1+(957976761/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((344535497/625000000 : ℝ)*X 2 0+(598735479/1250000000 : ℝ)*X 2 1+(-2582014983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1048748027/2500000000 : ℝ)*X 0 0+(311785567/1000000000 : ℝ)*X 0 1+(2817915227/5000000000 : ℝ)*X 0 2+(1048748027/2500000000 : ℝ)*X 1 0+(311785567/1000000000 : ℝ)*X 1 1+(2817915227/5000000000 : ℝ)*X 1 2+(1048748027/2500000000 : ℝ)*X 2 0+(311785567/1000000000 : ℝ)*X 2 1+(2817915227/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1873227529/10000000000 : ℝ)*X 0 0+(4822019591/10000000000 : ℝ)*X 0 1+(6003886923/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5173310453/10000000000 : ℝ)*X 1 0+(-171001269/1250000000 : ℝ)*X 1 1+(6003888727/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173311363/10000000000 : ℝ)*X 2 0+(3001943693/5000000000 : ℝ)*X 2 1+(-342002729/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4204941743/10000000000 : ℝ)*X 0 0+(1114191899/2000000000 : ℝ)*X 0 1+(3185017007/10000000000 : ℝ)*X 0 2+(4204941743/10000000000 : ℝ)*X 1 0+(1114191899/2000000000 : ℝ)*X 1 1+(3185017007/10000000000 : ℝ)*X 1 2+(4204941743/10000000000 : ℝ)*X 2 0+(1114191899/2000000000 : ℝ)*X 2 1+(3185017007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12627655175721097989087/2000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (71031269/100000000000000 : ℝ)*(base1) + (96436399/6250000000000 : ℝ)*(base19) + (1434108823/100000000000000 : ℝ)*(base23) + (2113477/2000000000000 : ℝ)*(base24) + (88031391/25000000000000 : ℝ)*(upper3) + (29972656037183/5000000000000 : ℝ)*(major0) + (29972656037183/5000000000000 : ℝ)*(major1) + (29972656037183/5000000000000 : ℝ)*(major2) + (801753781025983/100000000000000 : ℝ)*(sp0) + (400877793210369/50000000000000 : ℝ)*(sp1) + (801755589620449/100000000000000 : ℝ)*(sp2) + (198573069311839/50000000000000 : ℝ)*(sp3) + (3419408407/100000000000000 : ℝ)*(sp4) + (2691968327/100000000000000 : ℝ)*(sp7) + (198574450811637/50000000000000 : ℝ)*(f.failure) + (801757129403121/100000000000000 : ℝ)*(f.sum) + (739855250971/2000000000000000000000000000 : ℝ)*base66 + (4017224499029/4000000000000000000000000000 : ℝ)*base67 + (4867740476971/4000000000000000000000000000 : ℝ)*base70 + (11606942400971/4000000000000000000000000000 : ℝ)*base72 + (1261569625029/2000000000000000000000000000 : ℝ)*base73 + (23463835176971/4000000000000000000000000000 : ℝ)*base76 + (17258964944971/4000000000000000000000000000 : ℝ)*base78 + (11022133184971/4000000000000000000000000000 : ℝ)*base80 + (5024386119029/2000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (6091/2441406250000000000 : ℝ)*base90 + (6091/2441406250000000000 : ℝ)*base92 + (6091/2441406250000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34338967445334491532543/8000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1229485879/100000000000000 : ℝ)*(base19) + (715829989/50000000000000 : ℝ)*(base23) + (8929059/25000000000000 : ℝ)*(base39) + (293899789/100000000000000 : ℝ)*(upper3) + (15154081/50000000000000 : ℝ)*(upper5) + (632619682638801/100000000000000 : ℝ)*(major0) + (632619682638801/100000000000000 : ℝ)*(major1) + (126523929384513/20000000000000 : ℝ)*(major2) + (1441740129/50000000000000 : ℝ)*(sp1) + (3166994569/100000000000000 : ℝ)*(sp2) + (846116817424383/100000000000000 : ℝ)*(sp4) + (423056352229123/50000000000000 : ℝ)*(sp5) + (105764031810759/12500000000000 : ℝ)*(sp6) + (8382447381159/2000000000000 : ℝ)*(sp7) + (8382447381159/2000000000000 : ℝ)*(f.failure) + (846116853140619/100000000000000 : ℝ)*(f.sum) + (26755856957529/40000000000000000000000000000 : ℝ)*base65 + (23170635515819/16000000000000000000000000000 : ℝ)*base67 + (83849825184037/80000000000000000000000000000 : ℝ)*base70 + (31902756116181/16000000000000000000000000000 : ℝ)*base72 + (171477948517529/40000000000000000000000000000 : ℝ)*base73 + (403687507024037/80000000000000000000000000000 : ℝ)*base76 + (69265546384037/80000000000000000000000000000 : ℝ)*base78 + (202452408464037/80000000000000000000000000000 : ℝ)*base80 + (47839452695963/40000000000000000000000000000 : ℝ)*base81 + (1083/1562500000000000000 : ℝ)*base89 + (1083/1562500000000000000 : ℝ)*base91 + (1083/1562500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1217_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (359/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2753/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1217_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1217_s1_0 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1033763981/5000000000 : ℝ)*x 0 + (284096407/500000000 : ℝ)*x 1 + (5017583371/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033763981/5000000000 : ℝ)^4205 ≤ (6223825827277/50000000000000 : ℝ)^3181 := by
    have hnat : (1033763981 : ℕ)^4205*50000000000000^3181 ≤ 6223825827277^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033763981 5000000000 6223825827277 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (284096407/500000000 : ℝ)^4205 ≤ (23682913717127/50000000000000 : ℝ)^3181 := by
    have hnat : (284096407 : ℕ)^4205*50000000000000^3181 ≤ 23682913717127^3181*500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      284096407 500000000 23682913717127 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5017583371/10000000000 : ℝ)^4205 ≤ (40186520897581/100000000000000 : ℝ)^3181 := by
    have hnat : (5017583371 : ℕ)^4205*100000000000000^3181 ≤ 40186520897581^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5017583371 10000000000 40186520897581 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1033763981/5000000000 : ℝ), (284096407/500000000 : ℝ), (5017583371/10000000000 : ℝ)] ![(6223825827277/50000000000000 : ℝ), (23682913717127/50000000000000 : ℝ), (40186520897581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1033763981/5000000000 : ℝ)|^4205 ≤ (6223825827277/50000000000000 : ℝ)^3181
        have hw : |(-1033763981/5000000000 : ℝ)|=(1033763981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(284096407/500000000 : ℝ)|^4205 ≤ (23682913717127/50000000000000 : ℝ)^3181
        have hw : |(284096407/500000000 : ℝ)|=(284096407/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5017583371/10000000000 : ℝ)|^4205 ≤ (40186520897581/100000000000000 : ℝ)^3181
        have hw : |(5017583371/10000000000 : ℝ)|=(5017583371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s1_1 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2707509007/5000000000 : ℝ)*x 0 + (-606176327/2500000000 : ℝ)*x 1 + (5017583297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2707509007/5000000000 : ℝ)^4205 ≤ (44447024459061/100000000000000 : ℝ)^3181 := by
    have hnat : (2707509007 : ℕ)^4205*100000000000000^3181 ≤ 44447024459061^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707509007 5000000000 44447024459061 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (606176327/2500000000 : ℝ)^4205 ≤ (1920806926667/12500000000000 : ℝ)^3181 := by
    have hnat : (606176327 : ℕ)^4205*12500000000000^3181 ≤ 1920806926667^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      606176327 2500000000 1920806926667 12500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5017583297/10000000000 : ℝ)^4205 ≤ (8037304022823/20000000000000 : ℝ)^3181 := by
    have hnat : (5017583297 : ℕ)^4205*20000000000000^3181 ≤ 8037304022823^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5017583297 10000000000 8037304022823 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2707509007/5000000000 : ℝ), (-606176327/2500000000 : ℝ), (5017583297/10000000000 : ℝ)] ![(44447024459061/100000000000000 : ℝ), (1920806926667/12500000000000 : ℝ), (8037304022823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2707509007/5000000000 : ℝ)|^4205 ≤ (44447024459061/100000000000000 : ℝ)^3181
        have hw : |(2707509007/5000000000 : ℝ)|=(2707509007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-606176327/2500000000 : ℝ)|^4205 ≤ (1920806926667/12500000000000 : ℝ)^3181
        have hw : |(-606176327/2500000000 : ℝ)|=(606176327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5017583297/10000000000 : ℝ)|^4205 ≤ (8037304022823/20000000000000 : ℝ)^3181
        have hw : |(5017583297/10000000000 : ℝ)|=(5017583297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s1_2 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1353754497/2500000000 : ℝ)*x 0 + (1003516671/2000000000 : ℝ)*x 1 + (-2424705269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353754497/2500000000 : ℝ)^4205 ≤ (44447024176951/100000000000000 : ℝ)^3181 := by
    have hnat : (1353754497 : ℕ)^4205*100000000000000^3181 ≤ 44447024176951^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353754497 2500000000 44447024176951 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003516671/2000000000 : ℝ)^4205 ≤ (40186520728183/100000000000000 : ℝ)^3181 := by
    have hnat : (1003516671 : ℕ)^4205*100000000000000^3181 ≤ 40186520728183^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003516671 2000000000 40186520728183 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2424705269/10000000000 : ℝ)^4205 ≤ (15366455086611/100000000000000 : ℝ)^3181 := by
    have hnat : (2424705269 : ℕ)^4205*100000000000000^3181 ≤ 15366455086611^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2424705269 10000000000 15366455086611 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353754497/2500000000 : ℝ), (1003516671/2000000000 : ℝ), (-2424705269/10000000000 : ℝ)] ![(44447024176951/100000000000000 : ℝ), (40186520728183/100000000000000 : ℝ), (15366455086611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353754497/2500000000 : ℝ)|^4205 ≤ (44447024176951/100000000000000 : ℝ)^3181
        have hw : |(1353754497/2500000000 : ℝ)|=(1353754497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003516671/2000000000 : ℝ)|^4205 ≤ (40186520728183/100000000000000 : ℝ)^3181
        have hw : |(1003516671/2000000000 : ℝ)|=(1003516671/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2424705269/10000000000 : ℝ)|^4205 ≤ (15366455086611/100000000000000 : ℝ)^3181
        have hw : |(-2424705269/10000000000 : ℝ)|=(2424705269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s1_3 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (862204137/2000000000 : ℝ)*x 0 + (3690915521/10000000000 : ℝ)*x 1 + (5032084103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (862204137/2000000000 : ℝ)^4205 ≤ (3288117253613/10000000000000 : ℝ)^3181 := by
    have hnat : (862204137 : ℕ)^4205*10000000000000^3181 ≤ 3288117253613^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      862204137 2000000000 3288117253613 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3690915521/10000000000 : ℝ)^4205 ≤ (1071148421963/4000000000000 : ℝ)^3181 := by
    have hnat : (3690915521 : ℕ)^4205*4000000000000^3181 ≤ 1071148421963^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3690915521 10000000000 1071148421963 4000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5032084103/10000000000 : ℝ)^4205 ≤ (40340116897783/100000000000000 : ℝ)^3181 := by
    have hnat : (5032084103 : ℕ)^4205*100000000000000^3181 ≤ 40340116897783^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5032084103 10000000000 40340116897783 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(862204137/2000000000 : ℝ), (3690915521/10000000000 : ℝ), (5032084103/10000000000 : ℝ)] ![(3288117253613/10000000000000 : ℝ), (1071148421963/4000000000000 : ℝ), (40340116897783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(862204137/2000000000 : ℝ)|^4205 ≤ (3288117253613/10000000000000 : ℝ)^3181
        have hw : |(862204137/2000000000 : ℝ)|=(862204137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3690915521/10000000000 : ℝ)|^4205 ≤ (1071148421963/4000000000000 : ℝ)^3181
        have hw : |(3690915521/10000000000 : ℝ)|=(3690915521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5032084103/10000000000 : ℝ)|^4205 ≤ (40340116897783/100000000000000 : ℝ)^3181
        have hw : |(5032084103/10000000000 : ℝ)|=(5032084103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s1_4 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-82729261/400000000 : ℝ)*x 0 + (2513196851/5000000000 : ℝ)*x 1 + (567295067/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82729261/400000000 : ℝ)^4205 ≤ (12453251359473/100000000000000 : ℝ)^3181 := by
    have hnat : (82729261 : ℕ)^4205*100000000000000^3181 ≤ 12453251359473^3181*400000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82729261 400000000 12453251359473 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2513196851/5000000000 : ℝ)^4205 ≤ (40279825494811/100000000000000 : ℝ)^3181 := by
    have hnat : (2513196851 : ℕ)^4205*100000000000000^3181 ≤ 40279825494811^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513196851 5000000000 40279825494811 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567295067/1000000000 : ℝ)^4205 ≤ (945338462629/2000000000000 : ℝ)^3181 := by
    have hnat : (567295067 : ℕ)^4205*2000000000000^3181 ≤ 945338462629^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567295067 1000000000 945338462629 2000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82729261/400000000 : ℝ), (2513196851/5000000000 : ℝ), (567295067/1000000000 : ℝ)] ![(12453251359473/100000000000000 : ℝ), (40279825494811/100000000000000 : ℝ), (945338462629/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82729261/400000000 : ℝ)|^4205 ≤ (12453251359473/100000000000000 : ℝ)^3181
        have hw : |(-82729261/400000000 : ℝ)|=(82729261/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2513196851/5000000000 : ℝ)|^4205 ≤ (40279825494811/100000000000000 : ℝ)^3181
        have hw : |(2513196851/5000000000 : ℝ)|=(2513196851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(567295067/1000000000 : ℝ)|^4205 ≤ (945338462629/2000000000000 : ℝ)^3181
        have hw : |(567295067/1000000000 : ℝ)|=(567295067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s1_5 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5244066447/10000000000 : ℝ)*x 0 + (-1769342279/10000000000 : ℝ)*x 1 + (709118201/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244066447/10000000000 : ℝ)^4205 ≤ (21300813895003/50000000000000 : ℝ)^3181 := by
    have hnat : (5244066447 : ℕ)^4205*50000000000000^3181 ≤ 21300813895003^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244066447 10000000000 21300813895003 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1769342279/10000000000 : ℝ)^4205 ≤ (1013150481431/10000000000000 : ℝ)^3181 := by
    have hnat : (1769342279 : ℕ)^4205*10000000000000^3181 ≤ 1013150481431^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769342279 10000000000 1013150481431 10000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (709118201/1250000000 : ℝ)^4205 ≤ (47266867377873/100000000000000 : ℝ)^3181 := by
    have hnat : (709118201 : ℕ)^4205*100000000000000^3181 ≤ 47266867377873^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      709118201 1250000000 47266867377873 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244066447/10000000000 : ℝ), (-1769342279/10000000000 : ℝ), (709118201/1250000000 : ℝ)] ![(21300813895003/50000000000000 : ℝ), (1013150481431/10000000000000 : ℝ), (47266867377873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244066447/10000000000 : ℝ)|^4205 ≤ (21300813895003/50000000000000 : ℝ)^3181
        have hw : |(5244066447/10000000000 : ℝ)|=(5244066447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1769342279/10000000000 : ℝ)|^4205 ≤ (1013150481431/10000000000000 : ℝ)^3181
        have hw : |(-1769342279/10000000000 : ℝ)|=(1769342279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(709118201/1250000000 : ℝ)|^4205 ≤ (47266867377873/100000000000000 : ℝ)^3181
        have hw : |(709118201/1250000000 : ℝ)|=(709118201/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s1_6 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2622033297/5000000000 : ℝ)*x 0 + (1134589211/2000000000 : ℝ)*x 1 + (-1769341421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622033297/5000000000 : ℝ)^4205 ≤ (21300814684313/50000000000000 : ℝ)^3181 := by
    have hnat : (2622033297 : ℕ)^4205*50000000000000^3181 ≤ 21300814684313^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622033297 5000000000 21300814684313 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1134589211/2000000000 : ℝ)^4205 ≤ (47266872301193/100000000000000 : ℝ)^3181 := by
    have hnat : (1134589211 : ℕ)^4205*100000000000000^3181 ≤ 47266872301193^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134589211 2000000000 47266872301193 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1769341421/10000000000 : ℝ)^4205 ≤ (10131498319721/100000000000000 : ℝ)^3181 := by
    have hnat : (1769341421 : ℕ)^4205*100000000000000^3181 ≤ 10131498319721^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769341421 10000000000 10131498319721 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622033297/5000000000 : ℝ), (1134589211/2000000000 : ℝ), (-1769341421/10000000000 : ℝ)] ![(21300814684313/50000000000000 : ℝ), (47266872301193/100000000000000 : ℝ), (10131498319721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622033297/5000000000 : ℝ)|^4205 ≤ (21300814684313/50000000000000 : ℝ)^3181
        have hw : |(2622033297/5000000000 : ℝ)|=(2622033297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1134589211/2000000000 : ℝ)|^4205 ≤ (47266872301193/100000000000000 : ℝ)^3181
        have hw : |(1134589211/2000000000 : ℝ)|=(1134589211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1769341421/10000000000 : ℝ)|^4205 ≤ (10131498319721/100000000000000 : ℝ)^3181
        have hw : |(-1769341421/10000000000 : ℝ)|=(1769341421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s1_7 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4312445953/10000000000 : ℝ)*x 0 + (5014293317/10000000000 : ℝ)*x 1 + (927262279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312445953/10000000000 : ℝ)^4205 ≤ (32895543608053/100000000000000 : ℝ)^3181 := by
    have hnat : (4312445953 : ℕ)^4205*100000000000000^3181 ≤ 32895543608053^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312445953 10000000000 32895543608053 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5014293317/10000000000 : ℝ)^4205 ≤ (2007584577559/5000000000000 : ℝ)^3181 := by
    have hnat : (5014293317 : ℕ)^4205*5000000000000^3181 ≤ 2007584577559^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5014293317 10000000000 2007584577559 5000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (927262279/2500000000 : ℝ)^4205 ≤ (5390552966417/20000000000000 : ℝ)^3181 := by
    have hnat : (927262279 : ℕ)^4205*20000000000000^3181 ≤ 5390552966417^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      927262279 2500000000 5390552966417 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312445953/10000000000 : ℝ), (5014293317/10000000000 : ℝ), (927262279/2500000000 : ℝ)] ![(32895543608053/100000000000000 : ℝ), (2007584577559/5000000000000 : ℝ), (5390552966417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312445953/10000000000 : ℝ)|^4205 ≤ (32895543608053/100000000000000 : ℝ)^3181
        have hw : |(4312445953/10000000000 : ℝ)|=(4312445953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5014293317/10000000000 : ℝ)|^4205 ≤ (2007584577559/5000000000000 : ℝ)^3181
        have hw : |(5014293317/10000000000 : ℝ)|=(5014293317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(927262279/2500000000 : ℝ)|^4205 ≤ (5390552966417/20000000000000 : ℝ)^3181
        have hw : |(927262279/2500000000 : ℝ)|=(927262279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1217_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2753/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (359/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (6059/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10053/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2753/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (359/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2753/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (359/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2753/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (359/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2753/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (359/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2753/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (359/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2753/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (359/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (359/50000 : ℝ) ^ (8409/2048 : ℝ) ≤ (39380306901/25000000000000000000 : ℝ) := by
    have hpowers : (359/50000 : ℝ)^8409 ≤ (39380306901/25000000000000000000 : ℝ)^2048 := by
      have hnat : (359 : ℕ)^8409*25000000000000000000^2048 ≤ 39380306901^2048*50000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        359 50000 39380306901 25000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (359/50000 : ℝ)) (X := (39380306901/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2753/10000 : ℝ) ^ (8409/2048 : ℝ) ≤ (501035357716304573/100000000000000000000 : ℝ) := by
    have hpowers : (2753/10000 : ℝ)^8409 ≤ (501035357716304573/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2753 : ℕ)^8409*100000000000000000000^2048 ≤ 501035357716304573^2048*10000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2753 10000 501035357716304573 100000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2753/10000 : ℝ)) (X := (501035357716304573/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000039380306901/12500000000000000000 : ℝ) ≤ (2000000001534563/2000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (12500000039380306901/12500000000000000000 : ℝ)^2048 ≤ (2000000001534563/2000000000000000 : ℝ)^8409 := by
      have hnat : (12500000039380306901 : ℕ)^2048*2000000000000000^8409 ≤ 2000000001534563^8409*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000039380306901 12500000000000000000 2000000001534563 2000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000001534563/2000000000000000 : ℝ)) (X := (12500000039380306901/12500000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100501035515237532177/100000000000000000000 : ℝ) ≤ (500608979590179/500000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (100501035515237532177/100000000000000000000 : ℝ)^2048 ≤ (500608979590179/500000000000000 : ℝ)^8409 := by
      have hnat : (100501035515237532177 : ℕ)^2048*500000000000000^8409 ≤ 500608979590179^8409*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100501035515237532177 100000000000000000000 500608979590179 500000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500608979590179/500000000000000 : ℝ)) (X := (100501035515237532177/100000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50501035357716304573/50000000000000000000 : ℝ) ≤ (2004871835186869/2000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (50501035357716304573/50000000000000000000 : ℝ)^2048 ≤ (2004871835186869/2000000000000000 : ℝ)^8409 := by
      have hnat : (50501035357716304573 : ℕ)^2048*2000000000000000^8409 ≤ 2004871835186869^8409*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50501035357716304573 50000000000000000000 2004871835186869 2000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2004871835186869/2000000000000000 : ℝ)) (X := (50501035357716304573/50000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(39380306901/25000000000000000000 : ℝ) ≤ ((6702562758072793431/6703000000000000000 : ℝ)+2*(2435916826153/536240000000000 : ℝ)*(359/50000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (6702562758072793431/6703000000000000000 : ℝ)+2*(2435916826153/536240000000000 : ℝ)*(359/50000 : ℝ)=(2000000001534563/2000000000000000 : ℝ) by norm_num, show 1+2*(39380306901/25000000000000000000 : ℝ)=(12500000039380306901/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(501035357716304573/100000000000000000000 : ℝ)+(39380306901/25000000000000000000 : ℝ) ≤ ((6702562758072793431/6703000000000000000 : ℝ)+(2435916826153/536240000000000 : ℝ)*((2753/10000 : ℝ)+(359/50000 : ℝ)))^(8409/2048 : ℝ) := by
    rw [show (6702562758072793431/6703000000000000000 : ℝ)+(2435916826153/536240000000000 : ℝ)*((2753/10000 : ℝ)+(359/50000 : ℝ))=(500608979590179/500000000000000 : ℝ) by norm_num, show 1+(501035357716304573/100000000000000000000 : ℝ)+(39380306901/25000000000000000000 : ℝ)=(100501035515237532177/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(501035357716304573/100000000000000000000 : ℝ) ≤ ((6702562758072793431/6703000000000000000 : ℝ)+2*(2435916826153/536240000000000 : ℝ)*(2753/10000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (6702562758072793431/6703000000000000000 : ℝ)+2*(2435916826153/536240000000000 : ℝ)*(2753/10000 : ℝ)=(2004871835186869/2000000000000000 : ℝ) by norm_num, show 1+2*(501035357716304573/100000000000000000000 : ℝ)=(50501035357716304573/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6702562758072793431/6703000000000000000 : ℝ)*(X 1 0+X 2 0)+(2435916826153/536240000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (359/50000 : ℝ)) (hi := (2753/10000 : ℝ)) (c := (6702562758072793431/6703000000000000000 : ℝ)) (alpha := (2435916826153/536240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6702562758072793431/6703000000000000000 : ℝ)*(X 0 1+X 2 1)+(2435916826153/536240000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (359/50000 : ℝ)) (hi := (2753/10000 : ℝ)) (c := (6702562758072793431/6703000000000000000 : ℝ)) (alpha := (2435916826153/536240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6702562758072793431/6703000000000000000 : ℝ)*(X 0 2+X 1 2)+(2435916826153/536240000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (359/50000 : ℝ)) (hi := (2753/10000 : ℝ)) (c := (6702562758072793431/6703000000000000000 : ℝ)) (alpha := (2435916826153/536240000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1033763981/5000000000 : ℝ)*X 0 0+(284096407/500000000 : ℝ)*X 0 1+(5017583371/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2707509007/5000000000 : ℝ)*X 1 0+(-606176327/2500000000 : ℝ)*X 1 1+(5017583297/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1353754497/2500000000 : ℝ)*X 2 0+(1003516671/2000000000 : ℝ)*X 2 1+(-2424705269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((862204137/2000000000 : ℝ)*X 0 0+(3690915521/10000000000 : ℝ)*X 0 1+(5032084103/10000000000 : ℝ)*X 0 2+(862204137/2000000000 : ℝ)*X 1 0+(3690915521/10000000000 : ℝ)*X 1 1+(5032084103/10000000000 : ℝ)*X 1 2+(862204137/2000000000 : ℝ)*X 2 0+(3690915521/10000000000 : ℝ)*X 2 1+(5032084103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-82729261/400000000 : ℝ)*X 0 0+(2513196851/5000000000 : ℝ)*X 0 1+(567295067/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5244066447/10000000000 : ℝ)*X 1 0+(-1769342279/10000000000 : ℝ)*X 1 1+(709118201/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2622033297/5000000000 : ℝ)*X 2 0+(1134589211/2000000000 : ℝ)*X 2 1+(-1769341421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4312445953/10000000000 : ℝ)*X 0 0+(5014293317/10000000000 : ℝ)*X 0 1+(927262279/2500000000 : ℝ)*X 0 2+(4312445953/10000000000 : ℝ)*X 1 0+(5014293317/10000000000 : ℝ)*X 1 1+(927262279/2500000000 : ℝ)*X 1 2+(4312445953/10000000000 : ℝ)*X 2 0+(5014293317/10000000000 : ℝ)*X 2 1+(927262279/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36068912710275872997147/6703000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2945793/4000000000000 : ℝ)*(base1) + (119130917/10000000000000 : ℝ)*(base19) + (148010219/12500000000000 : ℝ)*(base23) + (65179573/50000000000000 : ℝ)*(upper3) + (8944977/6250000000000 : ℝ)*(upper5) + (56272002335243/5000000000000 : ℝ)*(major0) + (56272002335243/5000000000000 : ℝ)*(major1) + (56272002335243/5000000000000 : ℝ)*(major2) + (752624289109523/50000000000000 : ℝ)*(sp0) + (1505253647269433/100000000000000 : ℝ)*(sp1) + (30105073089937/2000000000000 : ℝ)*(sp2) + (372810849623521/50000000000000 : ℝ)*(sp3) + (6334004381/100000000000000 : ℝ)*(sp4) + (3302572233/100000000000000 : ℝ)*(sp7) + (7456250754641/1000000000000 : ℝ)*(f.failure) + (752627419289301/50000000000000 : ℝ)*(f.sum) + (40623284869/6703000000000000000000000000 : ℝ)*base65 + (31510392340251233/33515000000000000000000000000000 : ℝ)*base67 + (292035710717923767/33515000000000000000000000000000 : ℝ)*base70 + (48915024829288767/33515000000000000000000000000000 : ℝ)*base72 + (4606022172729/3351500000000000000000000000 : ℝ)*base73 + (348927130464398767/33515000000000000000000000000000 : ℝ)*base76 + (10313630371641233/33515000000000000000000000000000 : ℝ)*base77 + (104915989399531233/33515000000000000000000000000000 : ℝ)*base79 + (33970768466017/6703000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2071/390625000000000000 : ℝ)*base89 + (2071/390625000000000000 : ℝ)*base91 + (2071/390625000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (184059533404028762378646693/16757500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (256073321/25000000000000 : ℝ)*(base19) + (435065403/20000000000000 : ℝ)*(base23) + (427969/12500000000000 : ℝ)*(lower3) + (463905417/100000000000000 : ℝ)*(lower4) + (115640400153551/10000000000000 : ℝ)*(major0) + (115640400153551/10000000000000 : ℝ)*(major1) + (115640400153551/10000000000000 : ℝ)*(major2) + (7903329433/100000000000000 : ℝ)*(sp0) + (2772143989/100000000000000 : ℝ)*(sp1) + (9614344703/100000000000000 : ℝ)*(sp2) + (1546660459085731/100000000000000 : ℝ)*(sp4) + (1546664565977891/100000000000000 : ℝ)*(sp5) + (773328286371723/50000000000000 : ℝ)*(sp6) + (2394185232913/312500000000 : ℝ)*(sp7) + (2394185232913/312500000000 : ℝ)*(f.failure) + (386667090603791/25000000000000 : ℝ)*(f.sum) + (48370442526961/13406000000000000000000000000 : ℝ)*base65 + (145396400553649019/67030000000000000000000000000000 : ℝ)*base68 + (581703617114779019/67030000000000000000000000000000 : ℝ)*base70 + (20737179556320981/67030000000000000000000000000000 : ℝ)*base71 + (2465838223199/13406000000000000000000000000 : ℝ)*base74 + (262597653012219019/67030000000000000000000000000000 : ℝ)*base76 + (106942862479629019/67030000000000000000000000000000 : ℝ)*base78 + (245178150924039019/67030000000000000000000000000000 : ℝ)*base80 + (74935003231407/13406000000000000000000000000 : ℝ)*base82 + (13521/3906250000000000000 : ℝ)*base89 + (13521/3906250000000000000 : ℝ)*base91 + (13521/3906250000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1217_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2753/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (359/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6059/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10053/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1217_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1217_s2_0 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-529207497/2500000000 : ℝ)*x 0 + (5497116219/10000000000 : ℝ)*x 1 + (323186021/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529207497/2500000000 : ℝ)^4205 ≤ (6420763119549/50000000000000 : ℝ)^3181 := by
    have hnat : (529207497 : ℕ)^4205*50000000000000^3181 ≤ 6420763119549^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529207497 2500000000 6420763119549 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497116219/10000000000 : ℝ)^4205 ≤ (45339987921487/100000000000000 : ℝ)^3181 := by
    have hnat : (5497116219 : ℕ)^4205*100000000000000^3181 ≤ 45339987921487^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497116219 10000000000 45339987921487 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323186021/625000000 : ℝ)^4205 ≤ (41818485823049/100000000000000 : ℝ)^3181 := by
    have hnat : (323186021 : ℕ)^4205*100000000000000^3181 ≤ 41818485823049^3181*625000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323186021 625000000 41818485823049 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529207497/2500000000 : ℝ), (5497116219/10000000000 : ℝ), (323186021/625000000 : ℝ)] ![(6420763119549/50000000000000 : ℝ), (45339987921487/100000000000000 : ℝ), (41818485823049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529207497/2500000000 : ℝ)|^4205 ≤ (6420763119549/50000000000000 : ℝ)^3181
        have hw : |(-529207497/2500000000 : ℝ)|=(529207497/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497116219/10000000000 : ℝ)|^4205 ≤ (45339987921487/100000000000000 : ℝ)^3181
        have hw : |(5497116219/10000000000 : ℝ)|=(5497116219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323186021/625000000 : ℝ)|^4205 ≤ (41818485823049/100000000000000 : ℝ)^3181
        have hw : |(323186021/625000000 : ℝ)|=(323186021/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s2_1 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167834711/312500000 : ℝ)*x 0 + (-2285917437/10000000000 : ℝ)*x 1 + (5170976269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167834711/312500000 : ℝ)^4205 ≤ (43966907959633/100000000000000 : ℝ)^3181 := by
    have hnat : (167834711 : ℕ)^4205*100000000000000^3181 ≤ 43966907959633^3181*312500000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167834711 312500000 43966907959633 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2285917437/10000000000 : ℝ)^4205 ≤ (14214606923057/100000000000000 : ℝ)^3181 := by
    have hnat : (2285917437 : ℕ)^4205*100000000000000^3181 ≤ 14214606923057^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285917437 10000000000 14214606923057 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170976269/10000000000 : ℝ)^4205 ≤ (8363697021357/20000000000000 : ℝ)^3181 := by
    have hnat : (5170976269 : ℕ)^4205*20000000000000^3181 ≤ 8363697021357^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170976269 10000000000 8363697021357 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167834711/312500000 : ℝ), (-2285917437/10000000000 : ℝ), (5170976269/10000000000 : ℝ)] ![(43966907959633/100000000000000 : ℝ), (14214606923057/100000000000000 : ℝ), (8363697021357/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167834711/312500000 : ℝ)|^4205 ≤ (43966907959633/100000000000000 : ℝ)^3181
        have hw : |(167834711/312500000 : ℝ)|=(167834711/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2285917437/10000000000 : ℝ)|^4205 ≤ (14214606923057/100000000000000 : ℝ)^3181
        have hw : |(-2285917437/10000000000 : ℝ)|=(2285917437/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170976269/10000000000 : ℝ)|^4205 ≤ (8363697021357/20000000000000 : ℝ)^3181
        have hw : |(5170976269/10000000000 : ℝ)|=(5170976269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s2_2 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671338819/1250000000 : ℝ)*x 0 + (2585488223/5000000000 : ℝ)*x 1 + (-2285917469/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671338819/1250000000 : ℝ)^4205 ≤ (5495863224411/12500000000000 : ℝ)^3181 := by
    have hnat : (671338819 : ℕ)^4205*12500000000000^3181 ≤ 5495863224411^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671338819 1250000000 5495863224411 12500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2585488223/5000000000 : ℝ)^4205 ≤ (10454621749751/25000000000000 : ℝ)^3181 := by
    have hnat : (2585488223 : ℕ)^4205*25000000000000^3181 ≤ 10454621749751^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2585488223 5000000000 10454621749751 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2285917469/10000000000 : ℝ)^4205 ≤ (142146071861/1000000000000 : ℝ)^3181 := by
    have hnat : (2285917469 : ℕ)^4205*1000000000000^3181 ≤ 142146071861^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2285917469 10000000000 142146071861 1000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671338819/1250000000 : ℝ), (2585488223/5000000000 : ℝ), (-2285917469/10000000000 : ℝ)] ![(5495863224411/12500000000000 : ℝ), (10454621749751/25000000000000 : ℝ), (142146071861/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671338819/1250000000 : ℝ)|^4205 ≤ (5495863224411/12500000000000 : ℝ)^3181
        have hw : |(671338819/1250000000 : ℝ)|=(671338819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2585488223/5000000000 : ℝ)|^4205 ≤ (10454621749751/25000000000000 : ℝ)^3181
        have hw : |(2585488223/5000000000 : ℝ)|=(2585488223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2285917469/10000000000 : ℝ)|^4205 ≤ (142146071861/1000000000000 : ℝ)^3181
        have hw : |(-2285917469/10000000000 : ℝ)|=(2285917469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s2_3 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4345021317/10000000000 : ℝ)*x 0 + (1006991551/2500000000 : ℝ)*x 1 + (4686372049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345021317/10000000000 : ℝ)^4205 ≤ (6644883866761/20000000000000 : ℝ)^3181 := by
    have hnat : (4345021317 : ℕ)^4205*20000000000000^3181 ≤ 6644883866761^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345021317 10000000000 6644883866761 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006991551/2500000000 : ℝ)^4205 ≤ (751447198667/2500000000000 : ℝ)^3181 := by
    have hnat : (1006991551 : ℕ)^4205*2500000000000^3181 ≤ 751447198667^3181*2500000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006991551 2500000000 751447198667 2500000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4686372049/10000000000 : ℝ)^4205 ≤ (36717692707383/100000000000000 : ℝ)^3181 := by
    have hnat : (4686372049 : ℕ)^4205*100000000000000^3181 ≤ 36717692707383^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4686372049 10000000000 36717692707383 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345021317/10000000000 : ℝ), (1006991551/2500000000 : ℝ), (4686372049/10000000000 : ℝ)] ![(6644883866761/20000000000000 : ℝ), (751447198667/2500000000000 : ℝ), (36717692707383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345021317/10000000000 : ℝ)|^4205 ≤ (6644883866761/20000000000000 : ℝ)^3181
        have hw : |(4345021317/10000000000 : ℝ)|=(4345021317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1006991551/2500000000 : ℝ)|^4205 ≤ (751447198667/2500000000000 : ℝ)^3181
        have hw : |(1006991551/2500000000 : ℝ)|=(1006991551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4686372049/10000000000 : ℝ)|^4205 ≤ (36717692707383/100000000000000 : ℝ)^3181
        have hw : |(4686372049/10000000000 : ℝ)|=(4686372049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s2_4 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2116913793/10000000000 : ℝ)*x 0 + (2586554867/5000000000 : ℝ)*x 1 + (5494962501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116913793/10000000000 : ℝ)^4205 ≤ (6421099147727/50000000000000 : ℝ)^3181 := by
    have hnat : (2116913793 : ℕ)^4205*50000000000000^3181 ≤ 6421099147727^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116913793 10000000000 6421099147727 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2586554867/5000000000 : ℝ)^4205 ≤ (10460323608061/25000000000000 : ℝ)^3181 := by
    have hnat : (2586554867 : ℕ)^4205*25000000000000^3181 ≤ 10460323608061^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586554867 5000000000 10460323608061 25000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5494962501/10000000000 : ℝ)^4205 ≤ (2832281703979/6250000000000 : ℝ)^3181 := by
    have hnat : (5494962501 : ℕ)^4205*6250000000000^3181 ≤ 2832281703979^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494962501 10000000000 2832281703979 6250000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2116913793/10000000000 : ℝ), (2586554867/5000000000 : ℝ), (5494962501/10000000000 : ℝ)] ![(6421099147727/50000000000000 : ℝ), (10460323608061/25000000000000 : ℝ), (2832281703979/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2116913793/10000000000 : ℝ)|^4205 ≤ (6421099147727/50000000000000 : ℝ)^3181
        have hw : |(-2116913793/10000000000 : ℝ)|=(2116913793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2586554867/5000000000 : ℝ)|^4205 ≤ (10460323608061/25000000000000 : ℝ)^3181
        have hw : |(2586554867/5000000000 : ℝ)|=(2586554867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5494962501/10000000000 : ℝ)|^4205 ≤ (2832281703979/6250000000000 : ℝ)^3181
        have hw : |(5494962501/10000000000 : ℝ)|=(5494962501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s2_5 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2643776921/5000000000 : ℝ)*x 0 + (-980965527/5000000000 : ℝ)*x 1 + (5494962533/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2643776921/5000000000 : ℝ)^4205 ≤ (21534628666653/50000000000000 : ℝ)^3181 := by
    have hnat : (2643776921 : ℕ)^4205*50000000000000^3181 ≤ 21534628666653^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643776921 5000000000 21534628666653 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (980965527/5000000000 : ℝ)^4205 ≤ (11614235038567/100000000000000 : ℝ)^3181 := by
    have hnat : (980965527 : ℕ)^4205*100000000000000^3181 ≤ 11614235038567^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980965527 5000000000 11614235038567 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5494962533/10000000000 : ℝ)^4205 ≤ (22658253806259/50000000000000 : ℝ)^3181 := by
    have hnat : (5494962533 : ℕ)^4205*50000000000000^3181 ≤ 22658253806259^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5494962533 10000000000 22658253806259 50000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2643776921/5000000000 : ℝ), (-980965527/5000000000 : ℝ), (5494962533/10000000000 : ℝ)] ![(21534628666653/50000000000000 : ℝ), (11614235038567/100000000000000 : ℝ), (22658253806259/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2643776921/5000000000 : ℝ)|^4205 ≤ (21534628666653/50000000000000 : ℝ)^3181
        have hw : |(2643776921/5000000000 : ℝ)|=(2643776921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-980965527/5000000000 : ℝ)|^4205 ≤ (11614235038567/100000000000000 : ℝ)^3181
        have hw : |(-980965527/5000000000 : ℝ)|=(980965527/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5494962533/10000000000 : ℝ)|^4205 ≤ (22658253806259/50000000000000 : ℝ)^3181
        have hw : |(5494962533/10000000000 : ℝ)|=(5494962533/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s2_6 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660944253/1250000000 : ℝ)*x 0 + (2747481287/5000000000 : ℝ)*x 1 + (-1961930747/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660944253/1250000000 : ℝ)^4205 ≤ (43069259292991/100000000000000 : ℝ)^3181 := by
    have hnat : (660944253 : ℕ)^4205*100000000000000^3181 ≤ 43069259292991^3181*1250000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660944253 1250000000 43069259292991 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2747481287/5000000000 : ℝ)^4205 ≤ (1416140876859/3125000000000 : ℝ)^3181 := by
    have hnat : (2747481287 : ℕ)^4205*3125000000000^3181 ≤ 1416140876859^3181*5000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747481287 5000000000 1416140876859 3125000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1961930747/10000000000 : ℝ)^4205 ≤ (2322846527231/20000000000000 : ℝ)^3181 := by
    have hnat : (1961930747 : ℕ)^4205*20000000000000^3181 ≤ 2322846527231^3181*10000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961930747 10000000000 2322846527231 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660944253/1250000000 : ℝ), (2747481287/5000000000 : ℝ), (-1961930747/10000000000 : ℝ)] ![(43069259292991/100000000000000 : ℝ), (1416140876859/3125000000000 : ℝ), (2322846527231/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660944253/1250000000 : ℝ)|^4205 ≤ (43069259292991/100000000000000 : ℝ)^3181
        have hw : |(660944253/1250000000 : ℝ)|=(660944253/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2747481287/5000000000 : ℝ)|^4205 ≤ (1416140876859/3125000000000 : ℝ)^3181
        have hw : |(2747481287/5000000000 : ℝ)|=(2747481287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1961930747/10000000000 : ℝ)|^4205 ≤ (2322846527231/20000000000000 : ℝ)^3181
        have hw : |(-1961930747/10000000000 : ℝ)|=(1961930747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1217_s2_7 (p : ℝ) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (434518999/1000000000 : ℝ)*x 0 + (936413059/2000000000 : ℝ)*x 1 + (403231379/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (434518999/1000000000 : ℝ)^4205 ≤ (33226124301293/100000000000000 : ℝ)^3181 := by
    have hnat : (434518999 : ℕ)^4205*100000000000000^3181 ≤ 33226124301293^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      434518999 1000000000 33226124301293 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (936413059/2000000000 : ℝ)^4205 ≤ (36673093539309/100000000000000 : ℝ)^3181 := by
    have hnat : (936413059 : ℕ)^4205*100000000000000^3181 ≤ 36673093539309^3181*2000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      936413059 2000000000 36673093539309 100000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (403231379/1000000000 : ℝ)^4205 ≤ (6020156429479/20000000000000 : ℝ)^3181 := by
    have hnat : (403231379 : ℕ)^4205*20000000000000^3181 ≤ 6020156429479^3181*1000000000^4205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403231379 1000000000 6020156429479 20000000000000 4205 3181 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4205/1024 : ℝ)) 4205 3181 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(434518999/1000000000 : ℝ), (936413059/2000000000 : ℝ), (403231379/1000000000 : ℝ)] ![(33226124301293/100000000000000 : ℝ), (36673093539309/100000000000000 : ℝ), (6020156429479/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(434518999/1000000000 : ℝ)|^4205 ≤ (33226124301293/100000000000000 : ℝ)^3181
        have hw : |(434518999/1000000000 : ℝ)|=(434518999/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(936413059/2000000000 : ℝ)|^4205 ≤ (36673093539309/100000000000000 : ℝ)^3181
        have hw : |(936413059/2000000000 : ℝ)|=(936413059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(403231379/1000000000 : ℝ)|^4205 ≤ (6020156429479/20000000000000 : ℝ)^3181
        have hw : |(403231379/1000000000 : ℝ)|=(403231379/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1217_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6059/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2349/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1629/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10053/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6059/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10053/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6059/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10053/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6059/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10053/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6059/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10053/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6059/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10053/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6059/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6059/100000 : ℝ) ^ (8409/2048 : ℝ) ≤ (500680450117811/50000000000000000000 : ℝ) := by
    have hpowers : (6059/100000 : ℝ)^8409 ≤ (500680450117811/50000000000000000000 : ℝ)^2048 := by
      have hnat : (6059 : ℕ)^8409*50000000000000000000^2048 ≤ 500680450117811^2048*100000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6059 100000 500680450117811 50000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6059/100000 : ℝ)) (X := (500680450117811/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (10053/50000 : ℝ) ^ (8409/2048 : ℝ) ≤ (68937443576808917/50000000000000000000 : ℝ) := by
    have hpowers : (10053/50000 : ℝ)^8409 ≤ (68937443576808917/50000000000000000000 : ℝ)^2048 := by
      have hnat : (10053 : ℕ)^8409*50000000000000000000^2048 ≤ 68937443576808917^2048*50000^8409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10053 50000 68937443576808917 50000000000000000000 8409 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10053/50000 : ℝ)) (X := (68937443576808917/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000500680450117811/25000000000000000000 : ℝ) ≤ (500002438781769/500000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (25000500680450117811/25000000000000000000 : ℝ)^2048 ≤ (500002438781769/500000000000000 : ℝ)^8409 := by
      have hnat : (25000500680450117811 : ℕ)^2048*500000000000000^8409 ≤ 500002438781769^8409*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000500680450117811 25000000000000000000 500002438781769 500000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500002438781769/500000000000000 : ℝ)) (X := (25000500680450117811/25000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6258679765503365841/6250000000000000000 : ℝ) ≤ (10003380536116853/10000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (6258679765503365841/6250000000000000000 : ℝ)^2048 ≤ (10003380536116853/10000000000000000 : ℝ)^8409 := by
      have hnat : (6258679765503365841 : ℕ)^2048*10000000000000000^8409 ≤ 10003380536116853^8409*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6258679765503365841 6250000000000000000 10003380536116853 10000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003380536116853/10000000000000000 : ℝ)) (X := (6258679765503365841/6250000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25068937443576808917/25000000000000000000 : ℝ) ≤ (5003356148299163/5000000000000000 : ℝ) ^ (8409/2048 : ℝ) := by
    have hpowers : (25068937443576808917/25000000000000000000 : ℝ)^2048 ≤ (5003356148299163/5000000000000000 : ℝ)^8409 := by
      have hnat : (25068937443576808917 : ℕ)^2048*5000000000000000^8409 ≤ 5003356148299163^8409*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25068937443576808917 25000000000000000000 5003356148299163 5000000000000000 2048 8409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003356148299163/5000000000000000 : ℝ)) (X := (25068937443576808917/25000000000000000000 : ℝ)) (by norm_num) 8409 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(500680450117811/50000000000000000000 : ℝ) ≤ ((70215155438917846523/70235000000000000000 : ℝ)+2*(3331760481473/1404700000000000 : ℝ)*(6059/100000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (70215155438917846523/70235000000000000000 : ℝ)+2*(3331760481473/1404700000000000 : ℝ)*(6059/100000 : ℝ)=(500002438781769/500000000000000 : ℝ) by norm_num, show 1+2*(500680450117811/50000000000000000000 : ℝ)=(25000500680450117811/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(68937443576808917/50000000000000000000 : ℝ)+(500680450117811/50000000000000000000 : ℝ) ≤ ((70215155438917846523/70235000000000000000 : ℝ)+(3331760481473/1404700000000000 : ℝ)*((10053/50000 : ℝ)+(6059/100000 : ℝ)))^(8409/2048 : ℝ) := by
    rw [show (70215155438917846523/70235000000000000000 : ℝ)+(3331760481473/1404700000000000 : ℝ)*((10053/50000 : ℝ)+(6059/100000 : ℝ))=(10003380536116853/10000000000000000 : ℝ) by norm_num, show 1+(68937443576808917/50000000000000000000 : ℝ)+(500680450117811/50000000000000000000 : ℝ)=(6258679765503365841/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(68937443576808917/50000000000000000000 : ℝ) ≤ ((70215155438917846523/70235000000000000000 : ℝ)+2*(3331760481473/1404700000000000 : ℝ)*(10053/50000 : ℝ))^(8409/2048 : ℝ) := by
    rw [show (70215155438917846523/70235000000000000000 : ℝ)+2*(3331760481473/1404700000000000 : ℝ)*(10053/50000 : ℝ)=(5003356148299163/5000000000000000 : ℝ) by norm_num, show 1+2*(68937443576808917/50000000000000000000 : ℝ)=(25068937443576808917/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (70215155438917846523/70235000000000000000 : ℝ)*(X 1 0+X 2 0)+(3331760481473/1404700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (6059/100000 : ℝ)) (hi := (10053/50000 : ℝ)) (c := (70215155438917846523/70235000000000000000 : ℝ)) (alpha := (3331760481473/1404700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (70215155438917846523/70235000000000000000 : ℝ)*(X 0 1+X 2 1)+(3331760481473/1404700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (6059/100000 : ℝ)) (hi := (10053/50000 : ℝ)) (c := (70215155438917846523/70235000000000000000 : ℝ)) (alpha := (3331760481473/1404700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (70215155438917846523/70235000000000000000 : ℝ)*(X 0 2+X 1 2)+(3331760481473/1404700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8409/2048 : ℝ)) (lo := (6059/100000 : ℝ)) (hi := (10053/50000 : ℝ)) (c := (70215155438917846523/70235000000000000000 : ℝ)) (alpha := (3331760481473/1404700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-529207497/2500000000 : ℝ)*X 0 0+(5497116219/10000000000 : ℝ)*X 0 1+(323186021/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167834711/312500000 : ℝ)*X 1 0+(-2285917437/10000000000 : ℝ)*X 1 1+(5170976269/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((671338819/1250000000 : ℝ)*X 2 0+(2585488223/5000000000 : ℝ)*X 2 1+(-2285917469/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4345021317/10000000000 : ℝ)*X 0 0+(1006991551/2500000000 : ℝ)*X 0 1+(4686372049/10000000000 : ℝ)*X 0 2+(4345021317/10000000000 : ℝ)*X 1 0+(1006991551/2500000000 : ℝ)*X 1 1+(4686372049/10000000000 : ℝ)*X 1 2+(4345021317/10000000000 : ℝ)*X 2 0+(1006991551/2500000000 : ℝ)*X 2 1+(4686372049/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2116913793/10000000000 : ℝ)*X 0 0+(2586554867/5000000000 : ℝ)*X 0 1+(5494962501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2643776921/5000000000 : ℝ)*X 1 0+(-980965527/5000000000 : ℝ)*X 1 1+(5494962533/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((660944253/1250000000 : ℝ)*X 2 0+(2747481287/5000000000 : ℝ)*X 2 1+(-1961930747/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((434518999/1000000000 : ℝ)*X 0 0+(936413059/2000000000 : ℝ)*X 0 1+(403231379/1000000000 : ℝ)*X 0 2+(434518999/1000000000 : ℝ)*X 1 0+(936413059/2000000000 : ℝ)*X 1 1+(403231379/1000000000 : ℝ)*X 1 2+(434518999/1000000000 : ℝ)*X 2 0+(936413059/2000000000 : ℝ)*X 2 1+(403231379/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1217_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6958192631223778166503715517/877937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1614625703/100000000000000 : ℝ)*(base19) + (17352877/1250000000000 : ℝ)*(base23) + (30133237/50000000000000 : ℝ)*(lower2) + (254678219/100000000000000 : ℝ)*(upper3) + (4531253/4000000000000 : ℝ)*(upper5) + (1146260082332493/50000000000000 : ℝ)*(major0) + (1146260082332493/50000000000000 : ℝ)*(major1) + (1146260082332493/50000000000000 : ℝ)*(major2) + (1533093508599869/50000000000000 : ℝ)*(sp0) + (3066200973757677/100000000000000 : ℝ)*(sp1) + (153310060007661/5000000000000 : ℝ)*(sp2) + (379707024167603/25000000000000 : ℝ)*(sp3) + (7785591821/50000000000000 : ℝ)*(sp4) + (4690044543/50000000000000 : ℝ)*(sp7) + (759418738379749/50000000000000 : ℝ)*(f.failure) + (153310129419169/5000000000000 : ℝ)*(f.sum) + (283097223971/548710937500000000000000000 : ℝ)*base65 + (4039337046390421839/3511750000000000000000000000000000 : ℝ)*base67 + (246650126632078161/3511750000000000000000000000000000 : ℝ)*base70 + (19855019353424578161/3511750000000000000000000000000000 : ℝ)*base72 + (150297517520663/70235000000000000000000000000 : ℝ)*base73 + (1530400199542328161/3511750000000000000000000000000000 : ℝ)*base76 + (9194520457872578161/3511750000000000000000000000000000 : ℝ)*base78 + (3535276876282078161/3511750000000000000000000000000000 : ℝ)*base80 + (129554568446701/35117500000000000000000000000 : ℝ)*base82 + (210769/19531250000000000000 : ℝ)*base89 + (210769/19531250000000000000 : ℝ)*base91 + (210769/19531250000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7692908999668497923434541061/877937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2118559159/100000000000000 : ℝ)*(base19) + (2325731541/100000000000000 : ℝ)*(base23) + (2491017/20000000000000 : ℝ)*(upper2) + (272618601/100000000000000 : ℝ)*(upper3) + (44275353/25000000000000 : ℝ)*(upper5) + (1161515178636731/50000000000000 : ℝ)*(major0) + (1161515178636731/50000000000000 : ℝ)*(major1) + (1161515178636731/50000000000000 : ℝ)*(major2) + (5337746881/25000000000000 : ℝ)*(sp1) + (13113168599/50000000000000 : ℝ)*(sp2) + (155350468629689/5000000000000 : ℝ)*(sp4) + (1553492951523549/50000000000000 : ℝ)*(sp5) + (1553490410262521/50000000000000 : ℝ)*(sp6) + (3078102099741/200000000000 : ℝ)*(sp7) + (3078102099741/200000000000 : ℝ)*(f.failure) + (155350468629689/5000000000000 : ℝ)*(f.sum) + (141888312091787/35117500000000000000000000000 : ℝ)*base66 + (28585320208431586313/3511750000000000000000000000000000 : ℝ)*base67 + (33030188679001586313/3511750000000000000000000000000000 : ℝ)*base69 + (9167971098789586313/3511750000000000000000000000000000 : ℝ)*base71 + (173289423991087/35117500000000000000000000000 : ℝ)*base74 + (25453224903934086313/3511750000000000000000000000000000 : ℝ)*base75 + (3920580107655413687/3511750000000000000000000000000000 : ℝ)*base78 + (6160823220153586313/3511750000000000000000000000000000 : ℝ)*base79 + (112387129425007/35117500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (283/156250000000000000 : ℝ)*base90 + (283/156250000000000000 : ℝ)*base92 + (283/156250000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1217_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6059/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2349/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1217_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1217_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2349/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1217_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1217_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1217_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8409/2048 : ℝ) ≤ p) (hpb : p ≤ (4205/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (589606/390625 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2349/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1629/10000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1217_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
