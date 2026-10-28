-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1044_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:49:55.971983+00:00
-- url     : https://prove2.me/submissions/fde4145c-598c-4401-8d73-10e5fbc565b7

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
theorem support_rectangle_w1044_s0_0 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-240402483/1250000000 : ℝ)*x 0 + (379828587/625000000 : ℝ)*x 1 + (953591081/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (240402483/1250000000 : ℝ)^8237 ≤ (11145695689919/100000000000000 : ℝ)^6189 := by
    have hnat : (240402483 : ℕ)^8237*100000000000000^6189 ≤ 11145695689919^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240402483 1250000000 11145695689919 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (379828587/625000000 : ℝ)^8237 ≤ (51538810639133/100000000000000 : ℝ)^6189 := by
    have hnat : (379828587 : ℕ)^8237*100000000000000^6189 ≤ 51538810639133^6189*625000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379828587 625000000 51538810639133 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (953591081/2000000000 : ℝ)^8237 ≤ (37315493662113/100000000000000 : ℝ)^6189 := by
    have hnat : (953591081 : ℕ)^8237*100000000000000^6189 ≤ 37315493662113^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953591081 2000000000 37315493662113 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-240402483/1250000000 : ℝ), (379828587/625000000 : ℝ), (953591081/2000000000 : ℝ)] ![(11145695689919/100000000000000 : ℝ), (51538810639133/100000000000000 : ℝ), (37315493662113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-240402483/1250000000 : ℝ)|^8237 ≤ (11145695689919/100000000000000 : ℝ)^6189
        have hw : |(-240402483/1250000000 : ℝ)|=(240402483/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(379828587/625000000 : ℝ)|^8237 ≤ (51538810639133/100000000000000 : ℝ)^6189
        have hw : |(379828587/625000000 : ℝ)|=(379828587/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(953591081/2000000000 : ℝ)|^8237 ≤ (37315493662113/100000000000000 : ℝ)^6189
        have hw : |(953591081/2000000000 : ℝ)|=(953591081/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s0_1 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5522309101/10000000000 : ℝ)*x 0 + (-2677524427/10000000000 : ℝ)*x 1 + (953591229/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5522309101/10000000000 : ℝ)^8237 ≤ (2835737176401/6250000000000 : ℝ)^6189 := by
    have hnat : (5522309101 : ℕ)^8237*6250000000000^6189 ≤ 2835737176401^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5522309101 10000000000 2835737176401 6250000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2677524427/10000000000 : ℝ)^8237 ≤ (17312703796683/100000000000000 : ℝ)^6189 := by
    have hnat : (2677524427 : ℕ)^8237*100000000000000^6189 ≤ 17312703796683^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2677524427 10000000000 17312703796683 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (953591229/2000000000 : ℝ)^8237 ≤ (7463100274007/20000000000000 : ℝ)^6189 := by
    have hnat : (953591229 : ℕ)^8237*20000000000000^6189 ≤ 7463100274007^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      953591229 2000000000 7463100274007 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5522309101/10000000000 : ℝ), (-2677524427/10000000000 : ℝ), (953591229/2000000000 : ℝ)] ![(2835737176401/6250000000000 : ℝ), (17312703796683/100000000000000 : ℝ), (7463100274007/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5522309101/10000000000 : ℝ)|^8237 ≤ (2835737176401/6250000000000 : ℝ)^6189
        have hw : |(5522309101/10000000000 : ℝ)|=(5522309101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2677524427/10000000000 : ℝ)|^8237 ≤ (17312703796683/100000000000000 : ℝ)^6189
        have hw : |(-2677524427/10000000000 : ℝ)|=(2677524427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(953591229/2000000000 : ℝ)|^8237 ≤ (7463100274007/20000000000000 : ℝ)^6189
        have hw : |(953591229/2000000000 : ℝ)|=(953591229/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s0_2 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1380577607/2500000000 : ℝ)*x 0 + (4767953801/10000000000 : ℝ)*x 1 + (-1338762789/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1380577607/2500000000 : ℝ)^8237 ≤ (11342952333249/25000000000000 : ℝ)^6189 := by
    have hnat : (1380577607 : ℕ)^8237*25000000000000^6189 ≤ 11342952333249^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1380577607 2500000000 11342952333249 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4767953801/10000000000 : ℝ)^8237 ≤ (37315476954673/100000000000000 : ℝ)^6189 := by
    have hnat : (4767953801 : ℕ)^8237*100000000000000^6189 ≤ 37315476954673^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4767953801 10000000000 37315476954673 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1338762789/5000000000 : ℝ)^8237 ≤ (2164089212713/12500000000000 : ℝ)^6189 := by
    have hnat : (1338762789 : ℕ)^8237*12500000000000^6189 ≤ 2164089212713^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338762789 5000000000 2164089212713 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1380577607/2500000000 : ℝ), (4767953801/10000000000 : ℝ), (-1338762789/5000000000 : ℝ)] ![(11342952333249/25000000000000 : ℝ), (37315476954673/100000000000000 : ℝ), (2164089212713/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1380577607/2500000000 : ℝ)|^8237 ≤ (11342952333249/25000000000000 : ℝ)^6189
        have hw : |(1380577607/2500000000 : ℝ)|=(1380577607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4767953801/10000000000 : ℝ)|^8237 ≤ (37315476954673/100000000000000 : ℝ)^6189
        have hw : |(4767953801/10000000000 : ℝ)|=(4767953801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1338762789/5000000000 : ℝ)|^8237 ≤ (2164089212713/12500000000000 : ℝ)^6189
        have hw : |(-1338762789/5000000000 : ℝ)|=(1338762789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s0_3 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4209040251/10000000000 : ℝ)*x 0 + (781515647/2500000000 : ℝ)*x 1 + (568091593/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4209040251/10000000000 : ℝ)^8237 ≤ (31609790858633/100000000000000 : ℝ)^6189 := by
    have hnat : (4209040251 : ℕ)^8237*100000000000000^6189 ≤ 31609790858633^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4209040251 10000000000 31609790858633 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (781515647/2500000000 : ℝ)^8237 ≤ (21275878911697/100000000000000 : ℝ)^6189 := by
    have hnat : (781515647 : ℕ)^8237*100000000000000^6189 ≤ 21275878911697^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      781515647 2500000000 21275878911697 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (568091593/1000000000 : ℝ)^8237 ≤ (23557165112619/50000000000000 : ℝ)^6189 := by
    have hnat : (568091593 : ℕ)^8237*50000000000000^6189 ≤ 23557165112619^6189*1000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      568091593 1000000000 23557165112619 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4209040251/10000000000 : ℝ), (781515647/2500000000 : ℝ), (568091593/1000000000 : ℝ)] ![(31609790858633/100000000000000 : ℝ), (21275878911697/100000000000000 : ℝ), (23557165112619/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4209040251/10000000000 : ℝ)|^8237 ≤ (31609790858633/100000000000000 : ℝ)^6189
        have hw : |(4209040251/10000000000 : ℝ)|=(4209040251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(781515647/2500000000 : ℝ)|^8237 ≤ (21275878911697/100000000000000 : ℝ)^6189
        have hw : |(781515647/2500000000 : ℝ)|=(781515647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(568091593/1000000000 : ℝ)|^8237 ≤ (23557165112619/50000000000000 : ℝ)^6189
        have hw : |(568091593/1000000000 : ℝ)|=(568091593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s0_4 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-385732059/2000000000 : ℝ)*x 0 + (2400885373/5000000000 : ℝ)*x 1 + (6042261491/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (385732059/2000000000 : ℝ)^8237 ≤ (11187677699877/100000000000000 : ℝ)^6189 := by
    have hnat : (385732059 : ℕ)^8237*100000000000000^6189 ≤ 11187677699877^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      385732059 2000000000 11187677699877 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2400885373/5000000000 : ℝ)^8237 ≤ (37668130662331/100000000000000 : ℝ)^6189 := by
    have hnat : (2400885373 : ℕ)^8237*100000000000000^6189 ≤ 37668130662331^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2400885373 5000000000 37668130662331 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6042261491/10000000000 : ℝ)^8237 ≤ (6393023952811/12500000000000 : ℝ)^6189 := by
    have hnat : (6042261491 : ℕ)^8237*12500000000000^6189 ≤ 6393023952811^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6042261491 10000000000 6393023952811 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-385732059/2000000000 : ℝ), (2400885373/5000000000 : ℝ), (6042261491/10000000000 : ℝ)] ![(11187677699877/100000000000000 : ℝ), (37668130662331/100000000000000 : ℝ), (6393023952811/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-385732059/2000000000 : ℝ)|^8237 ≤ (11187677699877/100000000000000 : ℝ)^6189
        have hw : |(-385732059/2000000000 : ℝ)|=(385732059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2400885373/5000000000 : ℝ)|^8237 ≤ (37668130662331/100000000000000 : ℝ)^6189
        have hw : |(2400885373/5000000000 : ℝ)|=(2400885373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6042261491/10000000000 : ℝ)|^8237 ≤ (6393023952811/12500000000000 : ℝ)^6189
        have hw : |(6042261491/10000000000 : ℝ)|=(6042261491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s0_5 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1291767501/2500000000 : ℝ)*x 0 + (-1403215663/10000000000 : ℝ)*x 1 + (6042261743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1291767501/2500000000 : ℝ)^8237 ≤ (41529253442047/100000000000000 : ℝ)^6189 := by
    have hnat : (1291767501 : ℕ)^8237*100000000000000^6189 ≤ 41529253442047^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291767501 2500000000 41529253442047 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1403215663/10000000000 : ℝ)^8237 ≤ (57238688117/781250000000 : ℝ)^6189 := by
    have hnat : (1403215663 : ℕ)^8237*781250000000^6189 ≤ 57238688117^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403215663 10000000000 57238688117 781250000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6042261743/10000000000 : ℝ)^8237 ≤ (639302430767/1250000000000 : ℝ)^6189 := by
    have hnat : (6042261743 : ℕ)^8237*1250000000000^6189 ≤ 639302430767^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6042261743 10000000000 639302430767 1250000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1291767501/2500000000 : ℝ), (-1403215663/10000000000 : ℝ), (6042261743/10000000000 : ℝ)] ![(41529253442047/100000000000000 : ℝ), (57238688117/781250000000 : ℝ), (639302430767/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1291767501/2500000000 : ℝ)|^8237 ≤ (41529253442047/100000000000000 : ℝ)^6189
        have hw : |(1291767501/2500000000 : ℝ)|=(1291767501/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1403215663/10000000000 : ℝ)|^8237 ≤ (57238688117/781250000000 : ℝ)^6189
        have hw : |(-1403215663/10000000000 : ℝ)|=(1403215663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6042261743/10000000000 : ℝ)|^8237 ≤ (639302430767/1250000000000 : ℝ)^6189
        have hw : |(6042261743/10000000000 : ℝ)|=(6042261743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s0_6 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1033413429/2000000000 : ℝ)*x 0 + (6042264433/10000000000 : ℝ)*x 1 + (-175401963/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033413429/2000000000 : ℝ)^8237 ≤ (41529222859583/100000000000000 : ℝ)^6189 := by
    have hnat : (1033413429 : ℕ)^8237*100000000000000^6189 ≤ 41529222859583^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033413429 2000000000 41529222859583 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6042264433/10000000000 : ℝ)^8237 ≤ (51144224765203/100000000000000 : ℝ)^6189 := by
    have hnat : (6042264433 : ℕ)^8237*100000000000000^6189 ≤ 51144224765203^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6042264433 10000000000 51144224765203 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175401963/1250000000 : ℝ)^8237 ≤ (3663276181943/50000000000000 : ℝ)^6189 := by
    have hnat : (175401963 : ℕ)^8237*50000000000000^6189 ≤ 3663276181943^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175401963 1250000000 3663276181943 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033413429/2000000000 : ℝ), (6042264433/10000000000 : ℝ), (-175401963/1250000000 : ℝ)] ![(41529222859583/100000000000000 : ℝ), (51144224765203/100000000000000 : ℝ), (3663276181943/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033413429/2000000000 : ℝ)|^8237 ≤ (41529222859583/100000000000000 : ℝ)^6189
        have hw : |(1033413429/2000000000 : ℝ)|=(1033413429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6042264433/10000000000 : ℝ)|^8237 ≤ (51144224765203/100000000000000 : ℝ)^6189
        have hw : |(6042264433/10000000000 : ℝ)|=(6042264433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-175401963/1250000000 : ℝ)|^8237 ≤ (3663276181943/50000000000000 : ℝ)^6189
        have hw : |(-175401963/1250000000 : ℝ)|=(175401963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s0_7 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2109824927/5000000000 : ℝ)*x 0 + (5614933293/10000000000 : ℝ)*x 1 + (3194353501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109824927/5000000000 : ℝ)^8237 ≤ (15857939549533/50000000000000 : ℝ)^6189 := by
    have hnat : (2109824927 : ℕ)^8237*50000000000000^6189 ≤ 15857939549533^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109824927 5000000000 15857939549533 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5614933293/10000000000 : ℝ)^8237 ≤ (11596857276583/25000000000000 : ℝ)^6189 := by
    have hnat : (5614933293 : ℕ)^8237*25000000000000^6189 ≤ 11596857276583^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5614933293 10000000000 11596857276583 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3194353501/10000000000 : ℝ)^8237 ≤ (21896691773447/100000000000000 : ℝ)^6189 := by
    have hnat : (3194353501 : ℕ)^8237*100000000000000^6189 ≤ 21896691773447^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194353501 10000000000 21896691773447 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2109824927/5000000000 : ℝ), (5614933293/10000000000 : ℝ), (3194353501/10000000000 : ℝ)] ![(15857939549533/50000000000000 : ℝ), (11596857276583/25000000000000 : ℝ), (21896691773447/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2109824927/5000000000 : ℝ)|^8237 ≤ (15857939549533/50000000000000 : ℝ)^6189
        have hw : |(2109824927/5000000000 : ℝ)|=(2109824927/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5614933293/10000000000 : ℝ)|^8237 ≤ (11596857276583/25000000000000 : ℝ)^6189
        have hw : |(5614933293/10000000000 : ℝ)|=(5614933293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3194353501/10000000000 : ℝ)|^8237 ≤ (21896691773447/100000000000000 : ℝ)^6189
        have hw : |(3194353501/10000000000 : ℝ)|=(3194353501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1044_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5639/20000 : ℝ)*pair X 0 0 := by
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
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (2059/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2059 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2059*1^512 ≤ 0^512*1^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2059/512 : ℝ) ≤ (156881051045103423/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2059 ≤ (156881051045103423/6250000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2059*6250000000000000000^512 ≤ 156881051045103423^512*5^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 156881051045103423 6250000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (156881051045103423/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2059 := by
      have hnat : (1 : ℕ)^512*1^2059 ≤ 1^2059*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6406881051045103423/6250000000000000000 : ℝ) ≤ (10061837079788183/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (6406881051045103423/6250000000000000000 : ℝ)^512 ≤ (10061837079788183/10000000000000000 : ℝ)^2059 := by
      have hnat : (6406881051045103423 : ℕ)^512*10000000000000000^2059 ≤ 10061837079788183^2059*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6406881051045103423 6250000000000000000 10061837079788183 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10061837079788183/10000000000000000 : ℝ)) (X := (6406881051045103423/6250000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (3281881051045103423/3125000000000000000 : ℝ) ≤ (5061837079788183/5000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (3281881051045103423/3125000000000000000 : ℝ)^512 ≤ (5061837079788183/5000000000000000 : ℝ)^2059 := by
      have hnat : (3281881051045103423 : ℕ)^512*5000000000000000^2059 ≤ 5061837079788183^2059*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3281881051045103423 3125000000000000000 5061837079788183 5000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5061837079788183/5000000000000000 : ℝ)) (X := (3281881051045103423/3125000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(61837079788183/4000000000000000 : ℝ)*(0 : ℝ))^(2059/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(61837079788183/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(156881051045103423/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(61837079788183/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2059/512 : ℝ) := by
    rw [show (1 : ℝ)+(61837079788183/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10061837079788183/10000000000000000 : ℝ) by norm_num, show 1+(156881051045103423/6250000000000000000 : ℝ)+(0 : ℝ)=(6406881051045103423/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(156881051045103423/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(61837079788183/4000000000000000 : ℝ)*(2/5 : ℝ))^(2059/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(61837079788183/4000000000000000 : ℝ)*(2/5 : ℝ)=(5061837079788183/5000000000000000 : ℝ) by norm_num, show 1+2*(156881051045103423/6250000000000000000 : ℝ)=(3281881051045103423/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(61837079788183/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61837079788183/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(61837079788183/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61837079788183/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(61837079788183/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61837079788183/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-240402483/1250000000 : ℝ)*X 0 0+(379828587/625000000 : ℝ)*X 0 1+(953591081/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5522309101/10000000000 : ℝ)*X 1 0+(-2677524427/10000000000 : ℝ)*X 1 1+(953591229/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1380577607/2500000000 : ℝ)*X 2 0+(4767953801/10000000000 : ℝ)*X 2 1+(-1338762789/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4209040251/10000000000 : ℝ)*X 0 0+(781515647/2500000000 : ℝ)*X 0 1+(568091593/1000000000 : ℝ)*X 0 2+(4209040251/10000000000 : ℝ)*X 1 0+(781515647/2500000000 : ℝ)*X 1 1+(568091593/1000000000 : ℝ)*X 1 2+(4209040251/10000000000 : ℝ)*X 2 0+(781515647/2500000000 : ℝ)*X 2 1+(568091593/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-385732059/2000000000 : ℝ)*X 0 0+(2400885373/5000000000 : ℝ)*X 0 1+(6042261491/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1291767501/2500000000 : ℝ)*X 1 0+(-1403215663/10000000000 : ℝ)*X 1 1+(6042261743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1033413429/2000000000 : ℝ)*X 2 0+(6042264433/10000000000 : ℝ)*X 2 1+(-175401963/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2109824927/5000000000 : ℝ)*X 0 0+(5614933293/10000000000 : ℝ)*X 0 1+(3194353501/10000000000 : ℝ)*X 0 2+(2109824927/5000000000 : ℝ)*X 1 0+(5614933293/10000000000 : ℝ)*X 1 1+(3194353501/10000000000 : ℝ)*X 1 2+(2109824927/5000000000 : ℝ)*X 2 0+(5614933293/10000000000 : ℝ)*X 2 1+(3194353501/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (242842559617411444821711/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (152663243/100000000000000 : ℝ)*(base1) + (673277401/50000000000000 : ℝ)*(base19) + (1445633903/100000000000000 : ℝ)*(base23) + (21113307/25000000000000 : ℝ)*(base24) + (96892593/20000000000000 : ℝ)*(upper3) + (288796730569261/50000000000000 : ℝ)*(major0) + (288796730569261/50000000000000 : ℝ)*(major1) + (288796730569261/50000000000000 : ℝ)*(major2) + (763769675616859/100000000000000 : ℝ)*(sp0) + (47735610976541/6250000000000 : ℝ)*(sp1) + (763769592092327/100000000000000 : ℝ)*(sp2) + (391412918174579/100000000000000 : ℝ)*(sp3) + (799612921/50000000000000 : ℝ)*(sp4) + (2567364721/100000000000000 : ℝ)*(sp7) + (391415638202543/100000000000000 : ℝ)*(f.failure) + (381885561089729/50000000000000 : ℝ)*(f.sum) + (89376058857237/100000000000000000000000000000 : ℝ)*base66 + (428619577842763/200000000000000000000000000000 : ℝ)*base67 + (313077889242763/200000000000000000000000000000 : ℝ)*base69 + (105484027042763/200000000000000000000000000000 : ℝ)*base71 + (44844568457237/100000000000000000000000000000 : ℝ)*base74 + (376700328642763/200000000000000000000000000000 : ℝ)*base75 + (517065687042763/200000000000000000000000000000 : ℝ)*base77 + (992180564442763/200000000000000000000000000000 : ℝ)*base79 + (265684722342763/100000000000000000000000000000 : ℝ)*base81 + (29771793/10000000000000000000000 : ℝ)*base90 + (29771793/10000000000000000000000 : ℝ)*base92 + (29771793/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (69978941725854612690717/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (588889383/100000000000000 : ℝ)*(base19) + (747328429/100000000000000 : ℝ)*(base23) + (261044369/50000000000000 : ℝ)*(base39) + (45043327/25000000000000 : ℝ)*(base45) + (71050843/100000000000000 : ℝ)*(upper2) + (107097627/50000000000000 : ℝ)*(upper5) + (121925072232647/20000000000000 : ℝ)*(major0) + (121925072232647/20000000000000 : ℝ)*(major1) + (609624839074497/100000000000000 : ℝ)*(major2) + (287247071/50000000000000 : ℝ)*(sp1) + (80612752875471/10000000000000 : ℝ)*(sp4) + (161225273074237/20000000000000 : ℝ)*(sp5) + (806127303515019/100000000000000 : ℝ)*(sp6) + (413122578177763/100000000000000 : ℝ)*(sp7) + (413122578177763/100000000000000 : ℝ)*(f.failure) + (100766006355431/12500000000000 : ℝ)*(f.sum) + (442516014119761/100000000000000000000000000000 : ℝ)*base66 + (2119060370331049/400000000000000000000000000000 : ℝ)*base68 + (19543987570401/80000000000000000000000000000 : ℝ)*base69 + (1870076556331049/400000000000000000000000000000 : ℝ)*base72 + (393408925919761/100000000000000000000000000000 : ℝ)*base74 + (314135552770401/80000000000000000000000000000 : ℝ)*base75 + (145310131149599/80000000000000000000000000000 : ℝ)*base78 + (225952965469599/80000000000000000000000000000 : ℝ)*base80 + (7023938069599/40000000000000000000000000000 : ℝ)*base82 + (63357987/10000000000000000000000 : ℝ)*base89 + (63357987/10000000000000000000000 : ℝ)*base91 + (63357987/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1044_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5639/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1044_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1044_s1_0 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-85397033/400000000 : ℝ)*x 0 + (2864263861/5000000000 : ℝ)*x 1 + (4981088807/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85397033/400000000 : ℝ)^8237 ≤ (12807638635307/100000000000000 : ℝ)^6189 := by
    have hnat : (85397033 : ℕ)^8237*100000000000000^6189 ≤ 12807638635307^6189*400000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85397033 400000000 12807638635307 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2864263861/5000000000 : ℝ)^8237 ≤ (47640587920513/100000000000000 : ℝ)^6189 := by
    have hnat : (2864263861 : ℕ)^8237*100000000000000^6189 ≤ 47640587920513^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2864263861 5000000000 47640587920513 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4981088807/10000000000 : ℝ)^8237 ≤ (39551773421721/100000000000000 : ℝ)^6189 := by
    have hnat : (4981088807 : ℕ)^8237*100000000000000^6189 ≤ 39551773421721^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4981088807 10000000000 39551773421721 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85397033/400000000 : ℝ), (2864263861/5000000000 : ℝ), (4981088807/10000000000 : ℝ)] ![(12807638635307/100000000000000 : ℝ), (47640587920513/100000000000000 : ℝ), (39551773421721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85397033/400000000 : ℝ)|^8237 ≤ (12807638635307/100000000000000 : ℝ)^6189
        have hw : |(-85397033/400000000 : ℝ)|=(85397033/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2864263861/5000000000 : ℝ)|^8237 ≤ (47640587920513/100000000000000 : ℝ)^6189
        have hw : |(2864263861/5000000000 : ℝ)|=(2864263861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4981088807/10000000000 : ℝ)|^8237 ≤ (39551773421721/100000000000000 : ℝ)^6189
        have hw : |(4981088807/10000000000 : ℝ)|=(4981088807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s1_1 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271226363/500000000 : ℝ)*x 0 + (-2540368199/10000000000 : ℝ)*x 1 + (498108913/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271226363/500000000 : ℝ)^8237 ≤ (11076426885447/25000000000000 : ℝ)^6189 := by
    have hnat : (271226363 : ℕ)^8237*25000000000000^6189 ≤ 11076426885447^6189*500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271226363 500000000 11076426885447 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2540368199/10000000000 : ℝ)^8237 ≤ (8071257805541/50000000000000 : ℝ)^6189 := by
    have hnat : (2540368199 : ℕ)^8237*50000000000000^6189 ≤ 8071257805541^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2540368199 10000000000 8071257805541 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (498108913/1000000000 : ℝ)^8237 ≤ (7910355367033/20000000000000 : ℝ)^6189 := by
    have hnat : (498108913 : ℕ)^8237*20000000000000^6189 ≤ 7910355367033^6189*1000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      498108913 1000000000 7910355367033 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271226363/500000000 : ℝ), (-2540368199/10000000000 : ℝ), (498108913/1000000000 : ℝ)] ![(11076426885447/25000000000000 : ℝ), (8071257805541/50000000000000 : ℝ), (7910355367033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271226363/500000000 : ℝ)|^8237 ≤ (11076426885447/25000000000000 : ℝ)^6189
        have hw : |(271226363/500000000 : ℝ)|=(271226363/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2540368199/10000000000 : ℝ)|^8237 ≤ (8071257805541/50000000000000 : ℝ)^6189
        have hw : |(-2540368199/10000000000 : ℝ)|=(2540368199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(498108913/1000000000 : ℝ)|^8237 ≤ (7910355367033/20000000000000 : ℝ)^6189
        have hw : |(498108913/1000000000 : ℝ)|=(498108913/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s1_2 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (271226383/500000000 : ℝ)*x 0 + (2490544317/5000000000 : ℝ)*x 1 + (-508073661/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (271226383/500000000 : ℝ)^8237 ≤ (44305711889957/100000000000000 : ℝ)^6189 := by
    have hnat : (271226383 : ℕ)^8237*100000000000000^6189 ≤ 44305711889957^6189*500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      271226383 500000000 44305711889957 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2490544317/5000000000 : ℝ)^8237 ≤ (39551771593467/100000000000000 : ℝ)^6189 := by
    have hnat : (2490544317 : ℕ)^8237*100000000000000^6189 ≤ 39551771593467^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2490544317 5000000000 39551771593467 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (508073661/2000000000 : ℝ)^8237 ≤ (8071258253769/50000000000000 : ℝ)^6189 := by
    have hnat : (508073661 : ℕ)^8237*50000000000000^6189 ≤ 8071258253769^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508073661 2000000000 8071258253769 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(271226383/500000000 : ℝ), (2490544317/5000000000 : ℝ), (-508073661/2000000000 : ℝ)] ![(44305711889957/100000000000000 : ℝ), (39551771593467/100000000000000 : ℝ), (8071258253769/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(271226383/500000000 : ℝ)|^8237 ≤ (44305711889957/100000000000000 : ℝ)^6189
        have hw : |(271226383/500000000 : ℝ)|=(271226383/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2490544317/5000000000 : ℝ)|^8237 ≤ (39551771593467/100000000000000 : ℝ)^6189
        have hw : |(2490544317/5000000000 : ℝ)|=(2490544317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-508073661/2000000000 : ℝ)|^8237 ≤ (8071258253769/50000000000000 : ℝ)^6189
        have hw : |(-508073661/2000000000 : ℝ)|=(508073661/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s1_3 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1081404521/2500000000 : ℝ)*x 0 + (3658279179/10000000000 : ℝ)*x 1 + (1023351829/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081404521/2500000000 : ℝ)^8237 ≤ (512192265411/1562500000000 : ℝ)^6189 := by
    have hnat : (1081404521 : ℕ)^8237*1562500000000^6189 ≤ 512192265411^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081404521 2500000000 512192265411 1562500000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3658279179/10000000000 : ℝ)^8237 ≤ (5245548686011/20000000000000 : ℝ)^6189 := by
    have hnat : (3658279179 : ℕ)^8237*20000000000000^6189 ≤ 5245548686011^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3658279179 10000000000 5245548686011 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1023351829/2000000000 : ℝ)^8237 ≤ (4099195157267/10000000000000 : ℝ)^6189 := by
    have hnat : (1023351829 : ℕ)^8237*10000000000000^6189 ≤ 4099195157267^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1023351829 2000000000 4099195157267 10000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081404521/2500000000 : ℝ), (3658279179/10000000000 : ℝ), (1023351829/2000000000 : ℝ)] ![(512192265411/1562500000000 : ℝ), (5245548686011/20000000000000 : ℝ), (4099195157267/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081404521/2500000000 : ℝ)|^8237 ≤ (512192265411/1562500000000 : ℝ)^6189
        have hw : |(1081404521/2500000000 : ℝ)|=(1081404521/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3658279179/10000000000 : ℝ)|^8237 ≤ (5245548686011/20000000000000 : ℝ)^6189
        have hw : |(3658279179/10000000000 : ℝ)|=(3658279179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1023351829/2000000000 : ℝ)|^8237 ≤ (4099195157267/10000000000000 : ℝ)^6189
        have hw : |(1023351829/2000000000 : ℝ)|=(1023351829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s1_4 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-533970743/2500000000 : ℝ)*x 0 + (2495839909/5000000000 : ℝ)*x 1 + (2858859053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533970743/2500000000 : ℝ)^8237 ≤ (12815281315929/100000000000000 : ℝ)^6189 := by
    have hnat : (533970743 : ℕ)^8237*100000000000000^6189 ≤ 12815281315929^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533970743 2500000000 12815281315929 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2495839909/5000000000 : ℝ)^8237 ≤ (7932747585283/20000000000000 : ℝ)^6189 := by
    have hnat : (2495839909 : ℕ)^8237*20000000000000^6189 ≤ 7932747585283^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2495839909 5000000000 7932747585283 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2858859053/5000000000 : ℝ)^8237 ≤ (47520980734313/100000000000000 : ℝ)^6189 := by
    have hnat : (2858859053 : ℕ)^8237*100000000000000^6189 ≤ 47520980734313^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858859053 5000000000 47520980734313 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533970743/2500000000 : ℝ), (2495839909/5000000000 : ℝ), (2858859053/5000000000 : ℝ)] ![(12815281315929/100000000000000 : ℝ), (7932747585283/20000000000000 : ℝ), (47520980734313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533970743/2500000000 : ℝ)|^8237 ≤ (12815281315929/100000000000000 : ℝ)^6189
        have hw : |(-533970743/2500000000 : ℝ)|=(533970743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2495839909/5000000000 : ℝ)|^8237 ≤ (7932747585283/20000000000000 : ℝ)^6189
        have hw : |(2495839909/5000000000 : ℝ)|=(2495839909/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2858859053/5000000000 : ℝ)|^8237 ≤ (47520980734313/100000000000000 : ℝ)^6189
        have hw : |(2858859053/5000000000 : ℝ)|=(2858859053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s1_5 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2616932467/5000000000 : ℝ)*x 0 + (-1803737611/10000000000 : ℝ)*x 1 + (714714913/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2616932467/5000000000 : ℝ)^8237 ≤ (42245276648311/100000000000000 : ℝ)^6189 := by
    have hnat : (2616932467 : ℕ)^8237*100000000000000^6189 ≤ 42245276648311^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616932467 5000000000 42245276648311 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1803737611/10000000000 : ℝ)^8237 ≤ (409349174187/4000000000000 : ℝ)^6189 := by
    have hnat : (1803737611 : ℕ)^8237*4000000000000^6189 ≤ 409349174187^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803737611 10000000000 409349174187 4000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (714714913/1250000000 : ℝ)^8237 ≤ (23760496992953/50000000000000 : ℝ)^6189 := by
    have hnat : (714714913 : ℕ)^8237*50000000000000^6189 ≤ 23760496992953^6189*1250000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      714714913 1250000000 23760496992953 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2616932467/5000000000 : ℝ), (-1803737611/10000000000 : ℝ), (714714913/1250000000 : ℝ)] ![(42245276648311/100000000000000 : ℝ), (409349174187/4000000000000 : ℝ), (23760496992953/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2616932467/5000000000 : ℝ)|^8237 ≤ (42245276648311/100000000000000 : ℝ)^6189
        have hw : |(2616932467/5000000000 : ℝ)|=(2616932467/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1803737611/10000000000 : ℝ)|^8237 ≤ (409349174187/4000000000000 : ℝ)^6189
        have hw : |(-1803737611/10000000000 : ℝ)|=(1803737611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(714714913/1250000000 : ℝ)|^8237 ≤ (23760496992953/50000000000000 : ℝ)^6189
        have hw : |(714714913/1250000000 : ℝ)|=(714714913/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s1_6 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5233863043/10000000000 : ℝ)*x 0 + (5717721379/10000000000 : ℝ)*x 1 + (-901868631/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5233863043/10000000000 : ℝ)^8237 ≤ (21122628167149/50000000000000 : ℝ)^6189 := by
    have hnat : (5233863043 : ℕ)^8237*50000000000000^6189 ≤ 21122628167149^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233863043 10000000000 21122628167149 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5717721379/10000000000 : ℝ)^8237 ≤ (23760508469187/50000000000000 : ℝ)^6189 := by
    have hnat : (5717721379 : ℕ)^8237*50000000000000^6189 ≤ 23760508469187^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5717721379 10000000000 23760508469187 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (901868631/5000000000 : ℝ)^8237 ≤ (2558431679837/25000000000000 : ℝ)^6189 := by
    have hnat : (901868631 : ℕ)^8237*25000000000000^6189 ≤ 2558431679837^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      901868631 5000000000 2558431679837 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5233863043/10000000000 : ℝ), (5717721379/10000000000 : ℝ), (-901868631/5000000000 : ℝ)] ![(21122628167149/50000000000000 : ℝ), (23760508469187/50000000000000 : ℝ), (2558431679837/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5233863043/10000000000 : ℝ)|^8237 ≤ (21122628167149/50000000000000 : ℝ)^6189
        have hw : |(5233863043/10000000000 : ℝ)|=(5233863043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5717721379/10000000000 : ℝ)|^8237 ≤ (23760508469187/50000000000000 : ℝ)^6189
        have hw : |(5717721379/10000000000 : ℝ)|=(5717721379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-901868631/5000000000 : ℝ)|^8237 ≤ (2558431679837/25000000000000 : ℝ)^6189
        have hw : |(-901868631/5000000000 : ℝ)|=(901868631/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s1_7 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4327482653/10000000000 : ℝ)*x 0 + (2548044757/5000000000 : ℝ)*x 1 + (919842361/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327482653/10000000000 : ℝ)^8237 ≤ (32799112129451/100000000000000 : ℝ)^6189 := by
    have hnat : (4327482653 : ℕ)^8237*100000000000000^6189 ≤ 32799112129451^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327482653 10000000000 32799112129451 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2548044757/5000000000 : ℝ)^8237 ≤ (40771712536073/100000000000000 : ℝ)^6189 := by
    have hnat : (2548044757 : ℕ)^8237*100000000000000^6189 ≤ 40771712536073^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2548044757 5000000000 40771712536073 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (919842361/2500000000 : ℝ)^8237 ≤ (13214587660371/50000000000000 : ℝ)^6189 := by
    have hnat : (919842361 : ℕ)^8237*50000000000000^6189 ≤ 13214587660371^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      919842361 2500000000 13214587660371 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327482653/10000000000 : ℝ), (2548044757/5000000000 : ℝ), (919842361/2500000000 : ℝ)] ![(32799112129451/100000000000000 : ℝ), (40771712536073/100000000000000 : ℝ), (13214587660371/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327482653/10000000000 : ℝ)|^8237 ≤ (32799112129451/100000000000000 : ℝ)^6189
        have hw : |(4327482653/10000000000 : ℝ)|=(4327482653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2548044757/5000000000 : ℝ)|^8237 ≤ (40771712536073/100000000000000 : ℝ)^6189
        have hw : |(2548044757/5000000000 : ℝ)|=(2548044757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(919842361/2500000000 : ℝ)|^8237 ≤ (13214587660371/50000000000000 : ℝ)^6189
        have hw : |(919842361/2500000000 : ℝ)|=(919842361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1044_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5639/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5083/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20897/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5639/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5639/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5639/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5639/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5639/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5639/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3/100000 : ℝ) ^ (2059/512 : ℝ) ≤ (13/20000000000000000000 : ℝ) := by
    have hpowers : (3/100000 : ℝ)^2059 ≤ (13/20000000000000000000 : ℝ)^512 := by
      have hnat : (3 : ℕ)^2059*20000000000000000000^512 ≤ 13^512*100000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3 100000 13 20000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3/100000 : ℝ)) (X := (13/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hpowhi : (5639/20000 : ℝ) ^ (2059/512 : ℝ) ≤ (123000161748690683/20000000000000000000 : ℝ) := by
    have hpowers : (5639/20000 : ℝ)^2059 ≤ (123000161748690683/20000000000000000000 : ℝ)^512 := by
      have hnat : (5639 : ℕ)^2059*20000000000000000000^512 ≤ 123000161748690683^512*20000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5639 20000 123000161748690683 20000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5639/20000 : ℝ)) (X := (123000161748690683/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000000000000013/10000000000000000000 : ℝ) ≤ (10000000000000001/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (10000000000000000013/10000000000000000000 : ℝ)^512 ≤ (10000000000000001/10000000000000000 : ℝ)^2059 := by
      have hnat : (10000000000000000013 : ℕ)^512*10000000000000000^2059 ≤ 10000000000000001^2059*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000000000000013 10000000000000000000 10000000000000001 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000000001/10000000000000000 : ℝ)) (X := (10000000000000000013/10000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (2515375020218586337/2500000000000000000 : ℝ) ≤ (10015257674979029/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (2515375020218586337/2500000000000000000 : ℝ)^512 ≤ (10015257674979029/10000000000000000 : ℝ)^2059 := by
      have hnat : (2515375020218586337 : ℕ)^512*10000000000000000^2059 ≤ 10015257674979029^2059*2500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2515375020218586337 2500000000000000000 10015257674979029 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015257674979029/10000000000000000 : ℝ)) (X := (2515375020218586337/2500000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (10123000161748690683/10000000000000000000 : ℝ) ≤ (10030515349958057/10000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (10123000161748690683/10000000000000000000 : ℝ)^512 ≤ (10030515349958057/10000000000000000 : ℝ)^2059 := by
      have hnat : (10123000161748690683 : ℕ)^512*10000000000000000^2059 ≤ 10030515349958057^2059*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10123000161748690683 10000000000000000000 10030515349958057 10000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10030515349958057/10000000000000000 : ℝ)) (X := (10123000161748690683/10000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13/20000000000000000000 : ℝ) ≤ ((35239988556743769253/35240000000000000000 : ℝ)+2*(3814418744757/704800000000000 : ℝ)*(3/100000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (35239988556743769253/35240000000000000000 : ℝ)+2*(3814418744757/704800000000000 : ℝ)*(3/100000 : ℝ)=(10000000000000001/10000000000000000 : ℝ) by norm_num, show 1+2*(13/20000000000000000000 : ℝ)=(10000000000000000013/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(123000161748690683/20000000000000000000 : ℝ)+(13/20000000000000000000 : ℝ) ≤ ((35239988556743769253/35240000000000000000 : ℝ)+(3814418744757/704800000000000 : ℝ)*((5639/20000 : ℝ)+(3/100000 : ℝ)))^(2059/512 : ℝ) := by
    rw [show (35239988556743769253/35240000000000000000 : ℝ)+(3814418744757/704800000000000 : ℝ)*((5639/20000 : ℝ)+(3/100000 : ℝ))=(10015257674979029/10000000000000000 : ℝ) by norm_num, show 1+(123000161748690683/20000000000000000000 : ℝ)+(13/20000000000000000000 : ℝ)=(2515375020218586337/2500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(123000161748690683/20000000000000000000 : ℝ) ≤ ((35239988556743769253/35240000000000000000 : ℝ)+2*(3814418744757/704800000000000 : ℝ)*(5639/20000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (35239988556743769253/35240000000000000000 : ℝ)+2*(3814418744757/704800000000000 : ℝ)*(5639/20000 : ℝ)=(10030515349958057/10000000000000000 : ℝ) by norm_num, show 1+2*(123000161748690683/20000000000000000000 : ℝ)=(10123000161748690683/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35239988556743769253/35240000000000000000 : ℝ)*(X 1 0+X 2 0)+(3814418744757/704800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (3/100000 : ℝ)) (hi := (5639/20000 : ℝ)) (c := (35239988556743769253/35240000000000000000 : ℝ)) (alpha := (3814418744757/704800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35239988556743769253/35240000000000000000 : ℝ)*(X 0 1+X 2 1)+(3814418744757/704800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (3/100000 : ℝ)) (hi := (5639/20000 : ℝ)) (c := (35239988556743769253/35240000000000000000 : ℝ)) (alpha := (3814418744757/704800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35239988556743769253/35240000000000000000 : ℝ)*(X 0 2+X 1 2)+(3814418744757/704800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (3/100000 : ℝ)) (hi := (5639/20000 : ℝ)) (c := (35239988556743769253/35240000000000000000 : ℝ)) (alpha := (3814418744757/704800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-85397033/400000000 : ℝ)*X 0 0+(2864263861/5000000000 : ℝ)*X 0 1+(4981088807/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((271226363/500000000 : ℝ)*X 1 0+(-2540368199/10000000000 : ℝ)*X 1 1+(498108913/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((271226383/500000000 : ℝ)*X 2 0+(2490544317/5000000000 : ℝ)*X 2 1+(-508073661/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081404521/2500000000 : ℝ)*X 0 0+(3658279179/10000000000 : ℝ)*X 0 1+(1023351829/2000000000 : ℝ)*X 0 2+(1081404521/2500000000 : ℝ)*X 1 0+(3658279179/10000000000 : ℝ)*X 1 1+(1023351829/2000000000 : ℝ)*X 1 2+(1081404521/2500000000 : ℝ)*X 2 0+(3658279179/10000000000 : ℝ)*X 2 1+(1023351829/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-533970743/2500000000 : ℝ)*X 0 0+(2495839909/5000000000 : ℝ)*X 0 1+(2858859053/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2616932467/5000000000 : ℝ)*X 1 0+(-1803737611/10000000000 : ℝ)*X 1 1+(714714913/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5233863043/10000000000 : ℝ)*X 2 0+(5717721379/10000000000 : ℝ)*X 2 1+(-901868631/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4327482653/10000000000 : ℝ)*X 0 0+(2548044757/5000000000 : ℝ)*X 0 1+(919842361/2500000000 : ℝ)*X 0 2+(4327482653/10000000000 : ℝ)*X 1 0+(2548044757/5000000000 : ℝ)*X 1 1+(919842361/2500000000 : ℝ)*X 1 2+(4327482653/10000000000 : ℝ)*X 2 0+(2548044757/5000000000 : ℝ)*X 2 1+(919842361/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (776875364911651042811105841/220250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37494317/50000000000000 : ℝ)*(base1) + (799179091/100000000000000 : ℝ)*(base19) + (897835383/100000000000000 : ℝ)*(base23) + (45022921/50000000000000 : ℝ)*(upper3) + (81738483/100000000000000 : ℝ)*(upper5) + (126472463919867/12500000000000 : ℝ)*(major0) + (126472463919867/12500000000000 : ℝ)*(major1) + (126472463919867/12500000000000 : ℝ)*(major2) + (668953019540457/50000000000000 : ℝ)*(sp0) + (334477366793097/25000000000000 : ℝ)*(sp1) + (2613104235383/195312500000 : ℝ)*(sp2) + (342823530786131/50000000000000 : ℝ)*(sp3) + (2151129599/50000000000000 : ℝ)*(sp4) + (1902230707/100000000000000 : ℝ)*(sp7) + (685649038791603/100000000000000 : ℝ)*(f.failure) + (1337910266351479/100000000000000 : ℝ)*(f.sum) + (7013237035127/2202500000000000000000000000 : ℝ)*base65 + (3529598824792399351/440500000000000000000000000000000 : ℝ)*base67 + (4585733556594399351/440500000000000000000000000000000 : ℝ)*base69 + (2679827900056899351/440500000000000000000000000000000 : ℝ)*base71 + (25130074267299/4405000000000000000000000000 : ℝ)*base73 + (2250830773907399351/440500000000000000000000000000000 : ℝ)*base75 + (1762742809616899351/440500000000000000000000000000000 : ℝ)*base77 + (2859999623816399351/440500000000000000000000000000000 : ℝ)*base79 + (42853743590029/4405000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (44195853/10000000000000000000000 : ℝ)*base90 + (44195853/10000000000000000000000 : ℝ)*base92 + (44195853/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2348582722845081779143931499/440500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (175348109/6250000000000 : ℝ)*(base19) + (2630405903/100000000000000 : ℝ)*(base23) + (39485743/25000000000000 : ℝ)*(upper2) + (98658917/25000000000000 : ℝ)*(upper3) + (266285527/50000000000000 : ℝ)*(upper5) + (260399021563287/25000000000000 : ℝ)*(major0) + (260399021563287/25000000000000 : ℝ)*(major1) + (260399021563287/25000000000000 : ℝ)*(major2) + (13192414621/100000000000000 : ℝ)*(sp1) + (6880203967/50000000000000 : ℝ)*(sp2) + (137733740279181/10000000000000 : ℝ)*(sp4) + (275464280961489/20000000000000 : ℝ)*(sp5) + (1377321011977973/100000000000000 : ℝ)*(sp6) + (22057955999797/3125000000000 : ℝ)*(sp7) + (22057955999797/3125000000000 : ℝ)*(f.failure) + (137733740279181/10000000000000 : ℝ)*(f.sum) + (14208372898739/8810000000000000000000000000 : ℝ)*base65 + (1849253551638835389/881000000000000000000000000000000 : ℝ)*base68 + (4010695427638835389/881000000000000000000000000000000 : ℝ)*base70 + (1893462630284835389/881000000000000000000000000000000 : ℝ)*base72 + (22035716158839/8810000000000000000000000000 : ℝ)*base73 + (10010372515788835389/881000000000000000000000000000000 : ℝ)*base76 + (3511422820793835389/881000000000000000000000000000000 : ℝ)*base78 + (6886209249821835389/881000000000000000000000000000000 : ℝ)*base80 + (22771664812459/8810000000000000000000000000 : ℝ)*base81 + (754453/312500000000000000000 : ℝ)*base89 + (754453/312500000000000000000 : ℝ)*base91 + (754453/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1044_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5639/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5083/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20897/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1044_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1044_s2_0 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2193591331/10000000000 : ℝ)*x 0 + (1382629633/2500000000 : ℝ)*x 1 + (257095133/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2193591331/10000000000 : ℝ)^8237 ≤ (13278156182017/100000000000000 : ℝ)^6189 := by
    have hnat : (2193591331 : ℕ)^8237*100000000000000^6189 ≤ 13278156182017^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2193591331 10000000000 13278156182017 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382629633/2500000000 : ℝ)^8237 ≤ (11365396499641/25000000000000 : ℝ)^6189 := by
    have hnat : (1382629633 : ℕ)^8237*25000000000000^6189 ≤ 11365396499641^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382629633 2500000000 11365396499641 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (257095133/500000000 : ℝ)^8237 ≤ (20630128903193/50000000000000 : ℝ)^6189 := by
    have hnat : (257095133 : ℕ)^8237*50000000000000^6189 ≤ 20630128903193^6189*500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257095133 500000000 20630128903193 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2193591331/10000000000 : ℝ), (1382629633/2500000000 : ℝ), (257095133/500000000 : ℝ)] ![(13278156182017/100000000000000 : ℝ), (11365396499641/25000000000000 : ℝ), (20630128903193/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2193591331/10000000000 : ℝ)|^8237 ≤ (13278156182017/100000000000000 : ℝ)^6189
        have hw : |(-2193591331/10000000000 : ℝ)|=(2193591331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1382629633/2500000000 : ℝ)|^8237 ≤ (11365396499641/25000000000000 : ℝ)^6189
        have hw : |(1382629633/2500000000 : ℝ)|=(1382629633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(257095133/500000000 : ℝ)|^8237 ≤ (20630128903193/50000000000000 : ℝ)^6189
        have hw : |(257095133/500000000 : ℝ)|=(257095133/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s2_1 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5378196739/10000000000 : ℝ)*x 0 + (-1198226507/5000000000 : ℝ)*x 1 + (32136887/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378196739/10000000000 : ℝ)^8237 ≤ (1095069708417/2500000000000 : ℝ)^6189 := by
    have hnat : (5378196739 : ℕ)^8237*2500000000000^6189 ≤ 1095069708417^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378196739 10000000000 1095069708417 2500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1198226507/5000000000 : ℝ)^8237 ≤ (933560109039/6250000000000 : ℝ)^6189 := by
    have hnat : (1198226507 : ℕ)^8237*6250000000000^6189 ≤ 933560109039^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198226507 5000000000 933560109039 6250000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32136887/62500000 : ℝ)^8237 ≤ (10315062475863/25000000000000 : ℝ)^6189 := by
    have hnat : (32136887 : ℕ)^8237*25000000000000^6189 ≤ 10315062475863^6189*62500000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32136887 62500000 10315062475863 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378196739/10000000000 : ℝ), (-1198226507/5000000000 : ℝ), (32136887/62500000 : ℝ)] ![(1095069708417/2500000000000 : ℝ), (933560109039/6250000000000 : ℝ), (10315062475863/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378196739/10000000000 : ℝ)|^8237 ≤ (1095069708417/2500000000000 : ℝ)^6189
        have hw : |(5378196739/10000000000 : ℝ)|=(5378196739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1198226507/5000000000 : ℝ)|^8237 ≤ (933560109039/6250000000000 : ℝ)^6189
        have hw : |(-1198226507/5000000000 : ℝ)|=(1198226507/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32136887/62500000 : ℝ)|^8237 ≤ (10315062475863/25000000000000 : ℝ)^6189
        have hw : |(32136887/62500000 : ℝ)|=(32136887/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s2_2 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5378196871/10000000000 : ℝ)*x 0 + (2570950613/5000000000 : ℝ)*x 1 + (-1198226867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378196871/10000000000 : ℝ)^8237 ≤ (43802789767509/100000000000000 : ℝ)^6189 := by
    have hnat : (5378196871 : ℕ)^8237*100000000000000^6189 ≤ 43802789767509^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378196871 10000000000 43802789767509 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2570950613/5000000000 : ℝ)^8237 ≤ (41260242491781/100000000000000 : ℝ)^6189 := by
    have hnat : (2570950613 : ℕ)^8237*100000000000000^6189 ≤ 41260242491781^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570950613 5000000000 41260242491781 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1198226867/5000000000 : ℝ)^8237 ≤ (29173765073/195312500000 : ℝ)^6189 := by
    have hnat : (1198226867 : ℕ)^8237*195312500000^6189 ≤ 29173765073^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198226867 5000000000 29173765073 195312500000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378196871/10000000000 : ℝ), (2570950613/5000000000 : ℝ), (-1198226867/5000000000 : ℝ)] ![(43802789767509/100000000000000 : ℝ), (41260242491781/100000000000000 : ℝ), (29173765073/195312500000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378196871/10000000000 : ℝ)|^8237 ≤ (43802789767509/100000000000000 : ℝ)^6189
        have hw : |(5378196871/10000000000 : ℝ)|=(5378196871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2570950613/5000000000 : ℝ)|^8237 ≤ (41260242491781/100000000000000 : ℝ)^6189
        have hw : |(2570950613/5000000000 : ℝ)|=(2570950613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1198226867/5000000000 : ℝ)|^8237 ≤ (29173765073/195312500000 : ℝ)^6189
        have hw : |(-1198226867/5000000000 : ℝ)|=(1198226867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s2_3 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (436558443/1000000000 : ℝ)*x 0 + (400311827/1000000000 : ℝ)*x 1 + (4761431791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (436558443/1000000000 : ℝ)^8237 ≤ (33184015340741/100000000000000 : ℝ)^6189 := by
    have hnat : (436558443 : ℕ)^8237*100000000000000^6189 ≤ 33184015340741^6189*1000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436558443 1000000000 33184015340741 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (400311827/1000000000 : ℝ)^8237 ≤ (29568426282553/100000000000000 : ℝ)^6189 := by
    have hnat : (400311827 : ℕ)^8237*100000000000000^6189 ≤ 29568426282553^6189*1000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400311827 1000000000 29568426282553 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4761431791/10000000000 : ℝ)^8237 ≤ (9311889590829/25000000000000 : ℝ)^6189 := by
    have hnat : (4761431791 : ℕ)^8237*25000000000000^6189 ≤ 9311889590829^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4761431791 10000000000 9311889590829 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(436558443/1000000000 : ℝ), (400311827/1000000000 : ℝ), (4761431791/10000000000 : ℝ)] ![(33184015340741/100000000000000 : ℝ), (29568426282553/100000000000000 : ℝ), (9311889590829/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(436558443/1000000000 : ℝ)|^8237 ≤ (33184015340741/100000000000000 : ℝ)^6189
        have hw : |(436558443/1000000000 : ℝ)|=(436558443/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(400311827/1000000000 : ℝ)|^8237 ≤ (29568426282553/100000000000000 : ℝ)^6189
        have hw : |(400311827/1000000000 : ℝ)|=(400311827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4761431791/10000000000 : ℝ)|^8237 ≤ (9311889590829/25000000000000 : ℝ)^6189
        have hw : |(4761431791/10000000000 : ℝ)|=(4761431791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s2_4 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1096862949/5000000000 : ℝ)*x 0 + (514477249/1000000000 : ℝ)*x 1 + (5527617461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1096862949/5000000000 : ℝ)^8237 ≤ (13279240292673/100000000000000 : ℝ)^6189 := by
    have hnat : (1096862949 : ℕ)^8237*100000000000000^6189 ≤ 13279240292673^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096862949 5000000000 13279240292673 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514477249/1000000000 : ℝ)^8237 ≤ (20645454695761/50000000000000 : ℝ)^6189 := by
    have hnat : (514477249 : ℕ)^8237*50000000000000^6189 ≤ 20645454695761^6189*1000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514477249 1000000000 20645454695761 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5527617461/10000000000 : ℝ)^8237 ≤ (11357462576631/25000000000000 : ℝ)^6189 := by
    have hnat : (5527617461 : ℕ)^8237*25000000000000^6189 ≤ 11357462576631^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527617461 10000000000 11357462576631 25000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1096862949/5000000000 : ℝ), (514477249/1000000000 : ℝ), (5527617461/10000000000 : ℝ)] ![(13279240292673/100000000000000 : ℝ), (20645454695761/50000000000000 : ℝ), (11357462576631/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1096862949/5000000000 : ℝ)|^8237 ≤ (13279240292673/100000000000000 : ℝ)^6189
        have hw : |(-1096862949/5000000000 : ℝ)|=(1096862949/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(514477249/1000000000 : ℝ)|^8237 ≤ (20645454695761/50000000000000 : ℝ)^6189
        have hw : |(514477249/1000000000 : ℝ)|=(514477249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5527617461/10000000000 : ℝ)|^8237 ≤ (11357462576631/25000000000000 : ℝ)^6189
        have hw : |(5527617461/10000000000 : ℝ)|=(5527617461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s2_5 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1320064669/2500000000 : ℝ)*x 0 + (-2010737879/10000000000 : ℝ)*x 1 + (2763808761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1320064669/2500000000 : ℝ)^8237 ≤ (42744389620579/100000000000000 : ℝ)^6189 := by
    have hnat : (1320064669 : ℕ)^8237*100000000000000^6189 ≤ 42744389620579^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320064669 2500000000 42744389620579 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2010737879/10000000000 : ℝ)^8237 ≤ (1478219923681/12500000000000 : ℝ)^6189 := by
    have hnat : (2010737879 : ℕ)^8237*12500000000000^6189 ≤ 1478219923681^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010737879 10000000000 1478219923681 12500000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2763808761/5000000000 : ℝ)^8237 ≤ (45429850973763/100000000000000 : ℝ)^6189 := by
    have hnat : (2763808761 : ℕ)^8237*100000000000000^6189 ≤ 45429850973763^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2763808761 5000000000 45429850973763 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1320064669/2500000000 : ℝ), (-2010737879/10000000000 : ℝ), (2763808761/5000000000 : ℝ)] ![(42744389620579/100000000000000 : ℝ), (1478219923681/12500000000000 : ℝ), (45429850973763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1320064669/2500000000 : ℝ)|^8237 ≤ (42744389620579/100000000000000 : ℝ)^6189
        have hw : |(1320064669/2500000000 : ℝ)|=(1320064669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2010737879/10000000000 : ℝ)|^8237 ≤ (1478219923681/12500000000000 : ℝ)^6189
        have hw : |(-2010737879/10000000000 : ℝ)|=(2010737879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2763808761/5000000000 : ℝ)|^8237 ≤ (45429850973763/100000000000000 : ℝ)^6189
        have hw : |(2763808761/5000000000 : ℝ)|=(2763808761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s2_6 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (330016181/625000000 : ℝ)*x 0 + (1105523473/2000000000 : ℝ)*x 1 + (-502684449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330016181/625000000 : ℝ)^8237 ≤ (8548878398167/20000000000000 : ℝ)^6189 := by
    have hnat : (330016181 : ℕ)^8237*20000000000000^6189 ≤ 8548878398167^6189*625000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330016181 625000000 8548878398167 20000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1105523473/2000000000 : ℝ)^8237 ≤ (22714924628221/50000000000000 : ℝ)^6189 := by
    have hnat : (1105523473 : ℕ)^8237*50000000000000^6189 ≤ 22714924628221^6189*2000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1105523473 2000000000 22714924628221 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (502684449/2500000000 : ℝ)^8237 ≤ (11825758739767/100000000000000 : ℝ)^6189 := by
    have hnat : (502684449 : ℕ)^8237*100000000000000^6189 ≤ 11825758739767^6189*2500000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502684449 2500000000 11825758739767 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330016181/625000000 : ℝ), (1105523473/2000000000 : ℝ), (-502684449/2500000000 : ℝ)] ![(8548878398167/20000000000000 : ℝ), (22714924628221/50000000000000 : ℝ), (11825758739767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330016181/625000000 : ℝ)|^8237 ≤ (8548878398167/20000000000000 : ℝ)^6189
        have hw : |(330016181/625000000 : ℝ)|=(330016181/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1105523473/2000000000 : ℝ)|^8237 ≤ (22714924628221/50000000000000 : ℝ)^6189
        have hw : |(1105523473/2000000000 : ℝ)|=(1105523473/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-502684449/2500000000 : ℝ)|^8237 ≤ (11825758739767/100000000000000 : ℝ)^6189
        have hw : |(-502684449/2500000000 : ℝ)|=(502684449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1044_s2_7 (p : ℝ) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2182923247/5000000000 : ℝ)*x 0 + (4755828193/10000000000 : ℝ)*x 1 + (2004390389/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2182923247/5000000000 : ℝ)^8237 ≤ (16593333283541/50000000000000 : ℝ)^6189 := by
    have hnat : (2182923247 : ℕ)^8237*50000000000000^6189 ≤ 16593333283541^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2182923247 5000000000 16593333283541 50000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4755828193/10000000000 : ℝ)^8237 ≤ (37189228467467/100000000000000 : ℝ)^6189 := by
    have hnat : (4755828193 : ℕ)^8237*100000000000000^6189 ≤ 37189228467467^6189*10000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4755828193 10000000000 37189228467467 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004390389/5000000000 : ℝ)^8237 ≤ (29624104945747/100000000000000 : ℝ)^6189 := by
    have hnat : (2004390389 : ℕ)^8237*100000000000000^6189 ≤ 29624104945747^6189*5000000000^8237 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004390389 5000000000 29624104945747 100000000000000 8237 6189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8237/2048 : ℝ)) 8237 6189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2182923247/5000000000 : ℝ), (4755828193/10000000000 : ℝ), (2004390389/5000000000 : ℝ)] ![(16593333283541/50000000000000 : ℝ), (37189228467467/100000000000000 : ℝ), (29624104945747/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2182923247/5000000000 : ℝ)|^8237 ≤ (16593333283541/50000000000000 : ℝ)^6189
        have hw : |(2182923247/5000000000 : ℝ)|=(2182923247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4755828193/10000000000 : ℝ)|^8237 ≤ (37189228467467/100000000000000 : ℝ)^6189
        have hw : |(4755828193/10000000000 : ℝ)|=(4755828193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2004390389/5000000000 : ℝ)|^8237 ≤ (29624104945747/100000000000000 : ℝ)^6189
        have hw : |(2004390389/5000000000 : ℝ)|=(2004390389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1044_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20897/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5083/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4301/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8407/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20897/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5083/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20897/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5083/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20897/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5083/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20897/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5083/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20897/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5083/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20897/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5083/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5083/100000 : ℝ) ^ (2059/512 : ℝ) ≤ (626155555320317/100000000000000000000 : ℝ) := by
    have hpowers : (5083/100000 : ℝ)^2059 ≤ (626155555320317/100000000000000000000 : ℝ)^512 := by
      have hnat : (5083 : ℕ)^2059*100000000000000000000^512 ≤ 626155555320317^512*100000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5083 100000 626155555320317 100000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5083/100000 : ℝ)) (X := (626155555320317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hpowhi : (20897/100000 : ℝ) ^ (2059/512 : ℝ) ≤ (92193054412146207/50000000000000000000 : ℝ) := by
    have hpowers : (20897/100000 : ℝ)^2059 ≤ (92193054412146207/50000000000000000000 : ℝ)^512 := by
      have hnat : (20897 : ℕ)^2059*50000000000000000000^512 ≤ 92193054412146207^512*100000^2059 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20897 100000 92193054412146207 50000000000000000000 2059 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20897/100000 : ℝ)) (X := (92193054412146207/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000626155555320317/50000000000000000000 : ℝ) ≤ (5000015570186309/5000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (50000626155555320317/50000000000000000000 : ℝ)^512 ≤ (5000015570186309/5000000000000000 : ℝ)^2059 := by
      have hnat : (50000626155555320317 : ℕ)^512*5000000000000000^2059 ≤ 5000015570186309^2059*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000626155555320317 50000000000000000000 5000015570186309 5000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000015570186309/5000000000000000 : ℝ)) (X := (50000626155555320317/50000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100185012264379612731/100000000000000000000 : ℝ) ≤ (5002298701132407/5000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (100185012264379612731/100000000000000000000 : ℝ)^512 ≤ (5002298701132407/5000000000000000 : ℝ)^2059 := by
      have hnat : (100185012264379612731 : ℕ)^512*5000000000000000^2059 ≤ 5002298701132407^2059*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100185012264379612731 100000000000000000000 5002298701132407 5000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002298701132407/5000000000000000 : ℝ)) (X := (100185012264379612731/100000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25092193054412146207/25000000000000000000 : ℝ) ≤ (1000916366415701/1000000000000000 : ℝ) ^ (2059/512 : ℝ) := by
    have hpowers : (25092193054412146207/25000000000000000000 : ℝ)^512 ≤ (1000916366415701/1000000000000000 : ℝ)^2059 := by
      have hnat : (25092193054412146207 : ℕ)^512*1000000000000000^2059 ≤ 1000916366415701^2059*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25092193054412146207 25000000000000000000 1000916366415701 1000000000000000 512 2059 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000916366415701/1000000000000000 : ℝ)) (X := (25092193054412146207/25000000000000000000 : ℝ)) (by norm_num) 2059 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(626155555320317/100000000000000000000 : ℝ) ≤ ((39523517958864129129/39535000000000000000 : ℝ)+2*(1141565473049/395350000000000 : ℝ)*(5083/100000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (39523517958864129129/39535000000000000000 : ℝ)+2*(1141565473049/395350000000000 : ℝ)*(5083/100000 : ℝ)=(5000015570186309/5000000000000000 : ℝ) by norm_num, show 1+2*(626155555320317/100000000000000000000 : ℝ)=(50000626155555320317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(92193054412146207/50000000000000000000 : ℝ)+(626155555320317/100000000000000000000 : ℝ) ≤ ((39523517958864129129/39535000000000000000 : ℝ)+(1141565473049/395350000000000 : ℝ)*((20897/100000 : ℝ)+(5083/100000 : ℝ)))^(2059/512 : ℝ) := by
    rw [show (39523517958864129129/39535000000000000000 : ℝ)+(1141565473049/395350000000000 : ℝ)*((20897/100000 : ℝ)+(5083/100000 : ℝ))=(5002298701132407/5000000000000000 : ℝ) by norm_num, show 1+(92193054412146207/50000000000000000000 : ℝ)+(626155555320317/100000000000000000000 : ℝ)=(100185012264379612731/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(92193054412146207/50000000000000000000 : ℝ) ≤ ((39523517958864129129/39535000000000000000 : ℝ)+2*(1141565473049/395350000000000 : ℝ)*(20897/100000 : ℝ))^(2059/512 : ℝ) := by
    rw [show (39523517958864129129/39535000000000000000 : ℝ)+2*(1141565473049/395350000000000 : ℝ)*(20897/100000 : ℝ)=(1000916366415701/1000000000000000 : ℝ) by norm_num, show 1+2*(92193054412146207/50000000000000000000 : ℝ)=(25092193054412146207/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (39523517958864129129/39535000000000000000 : ℝ)*(X 1 0+X 2 0)+(1141565473049/395350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5083/100000 : ℝ)) (hi := (20897/100000 : ℝ)) (c := (39523517958864129129/39535000000000000000 : ℝ)) (alpha := (1141565473049/395350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (39523517958864129129/39535000000000000000 : ℝ)*(X 0 1+X 2 1)+(1141565473049/395350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5083/100000 : ℝ)) (hi := (20897/100000 : ℝ)) (c := (39523517958864129129/39535000000000000000 : ℝ)) (alpha := (1141565473049/395350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (39523517958864129129/39535000000000000000 : ℝ)*(X 0 2+X 1 2)+(1141565473049/395350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2059/512 : ℝ)) (lo := (5083/100000 : ℝ)) (hi := (20897/100000 : ℝ)) (c := (39523517958864129129/39535000000000000000 : ℝ)) (alpha := (1141565473049/395350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2193591331/10000000000 : ℝ)*X 0 0+(1382629633/2500000000 : ℝ)*X 0 1+(257095133/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5378196739/10000000000 : ℝ)*X 1 0+(-1198226507/5000000000 : ℝ)*X 1 1+(32136887/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5378196871/10000000000 : ℝ)*X 2 0+(2570950613/5000000000 : ℝ)*X 2 1+(-1198226867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((436558443/1000000000 : ℝ)*X 0 0+(400311827/1000000000 : ℝ)*X 0 1+(4761431791/10000000000 : ℝ)*X 0 2+(436558443/1000000000 : ℝ)*X 1 0+(400311827/1000000000 : ℝ)*X 1 1+(4761431791/10000000000 : ℝ)*X 1 2+(436558443/1000000000 : ℝ)*X 2 0+(400311827/1000000000 : ℝ)*X 2 1+(4761431791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1096862949/5000000000 : ℝ)*X 0 0+(514477249/1000000000 : ℝ)*X 0 1+(5527617461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1320064669/2500000000 : ℝ)*X 1 0+(-2010737879/10000000000 : ℝ)*X 1 1+(2763808761/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((330016181/625000000 : ℝ)*X 2 0+(1105523473/2000000000 : ℝ)*X 2 1+(-502684449/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2182923247/5000000000 : ℝ)*X 0 0+(4755828193/10000000000 : ℝ)*X 0 1+(2004390389/5000000000 : ℝ)*X 0 2+(2182923247/5000000000 : ℝ)*X 1 0+(4755828193/10000000000 : ℝ)*X 1 1+(2004390389/5000000000 : ℝ)*X 1 2+(2182923247/5000000000 : ℝ)*X 2 0+(4755828193/10000000000 : ℝ)*X 2 1+(2004390389/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1044_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2726064110056217631917155527/247093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1628612903/100000000000000 : ℝ)*(base19) + (965748267/50000000000000 : ℝ)*(base23) + (168388779/100000000000000 : ℝ)*(upper3) + (6558189/5000000000000 : ℝ)*(lower4) + (243250012715157/12500000000000 : ℝ)*(major0) + (243250012715157/12500000000000 : ℝ)*(major1) + (243250012715157/12500000000000 : ℝ)*(major2) + (514649977630359/20000000000000 : ℝ)*(sp0) + (2573259469531903/100000000000000 : ℝ)*(sp1) + (2573258938542009/100000000000000 : ℝ)*(sp2) + (659363370105859/50000000000000 : ℝ)*(sp3) + (11209993011/100000000000000 : ℝ)*(sp4) + (228106263/100000000000000 : ℝ)*(sp6) + (2999333917/25000000000000 : ℝ)*(sp7) + (659369368773693/50000000000000 : ℝ)*(f.failure) + (1286630549072403/50000000000000 : ℝ)*(f.sum) + (14688350978773/39535000000000000000000000000 : ℝ)*base65 + (3539716629674566747/494187500000000000000000000000000 : ℝ)*base68 + (8614947285936629247/494187500000000000000000000000000 : ℝ)*base70 + (7600087115364879247/494187500000000000000000000000000 : ℝ)*base72 + (9128005897559/19767500000000000000000000000 : ℝ)*base73 + (4192519680375566747/494187500000000000000000000000000 : ℝ)*base76 + (1656916667189254247/494187500000000000000000000000000 : ℝ)*base78 + (8279976818174129247/494187500000000000000000000000000 : ℝ)*base80 + (4502974966281/1235468750000000000000000000 : ℝ)*base82 + (32194557/5000000000000000000000 : ℝ)*base89 + (32194557/5000000000000000000000 : ℝ)*base91 + (32194557/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4744687792117340806240152153/1976750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (50783231/12500000000000 : ℝ)*(base19) + (534449571/100000000000000 : ℝ)*(base23) + (119927/20000000000000 : ℝ)*(upper2) + (73177193/100000000000000 : ℝ)*(upper3) + (57845843/100000000000000 : ℝ)*(upper5) + (1975313517948581/100000000000000 : ℝ)*(major0) + (1975313517948581/100000000000000 : ℝ)*(major1) + (1975313517948581/100000000000000 : ℝ)*(major2) + (3226568379/100000000000000 : ℝ)*(sp1) + (2104422049/50000000000000 : ℝ)*(sp2) + (1306011751645551/50000000000000 : ℝ)*(sp4) + (653004967614219/25000000000000 : ℝ)*(sp5) + (1306009379998717/50000000000000 : ℝ)*(sp6) + (1338603452597827/100000000000000 : ℝ)*(sp7) + (1338603452597827/100000000000000 : ℝ)*(f.failure) + (1306011751645551/50000000000000 : ℝ)*(f.sum) + (1289967866879/4941875000000000000000000000 : ℝ)*base66 + (17751641203994715949/3953500000000000000000000000000000 : ℝ)*base67 + (25621949414915215949/3953500000000000000000000000000000 : ℝ)*base69 + (372073372519284051/3953500000000000000000000000000000 : ℝ)*base72 + (191835467676903/39535000000000000000000000000 : ℝ)*base73 + (7699797212160215949/3953500000000000000000000000000000 : ℝ)*base75 + (5459663452853215949/3953500000000000000000000000000000 : ℝ)*base77 + (2219549354628284051/3953500000000000000000000000000000 : ℝ)*base80 + (40416520867897/9883750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (61886077/10000000000000000000000 : ℝ)*base90 + (61886077/10000000000000000000000 : ℝ)*base92 + (61886077/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1044_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20897/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5083/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4301/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8407/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1044_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1044_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4301/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8407/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1044_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1044_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1044_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2059/512 : ℝ) ≤ p) (hpb : p ≤ (8237/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147565249/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4301/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8407/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1044_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
