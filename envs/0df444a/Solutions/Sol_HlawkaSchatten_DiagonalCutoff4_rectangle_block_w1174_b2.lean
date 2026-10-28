-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1174_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:46:50.781036+00:00
-- url     : https://prove2.me/submissions/b44d62b2-fb01-43f2-85e2-a7d17ca37667

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
theorem support_rectangle_w1174_s6_0 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151651817/10000000000 : ℝ)*x 0 + (1348185907/2500000000 : ℝ)*x 1 + (2632983563/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151651817/10000000000 : ℝ)^8367 ≤ (13077421459079/100000000000000 : ℝ)^6319 := by
    have hnat : (2151651817 : ℕ)^8367*100000000000000^6319 ≤ 13077421459079^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151651817 10000000000 13077421459079 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348185907/2500000000 : ℝ)^8367 ≤ (44145740763573/100000000000000 : ℝ)^6319 := by
    have hnat : (1348185907 : ℕ)^8367*100000000000000^6319 ≤ 44145740763573^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348185907 2500000000 44145740763573 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632983563/5000000000 : ℝ)^8367 ≤ (42776837761951/100000000000000 : ℝ)^6319 := by
    have hnat : (2632983563 : ℕ)^8367*100000000000000^6319 ≤ 42776837761951^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632983563 5000000000 42776837761951 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151651817/10000000000 : ℝ), (1348185907/2500000000 : ℝ), (2632983563/5000000000 : ℝ)] ![(13077421459079/100000000000000 : ℝ), (44145740763573/100000000000000 : ℝ), (42776837761951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151651817/10000000000 : ℝ)|^8367 ≤ (13077421459079/100000000000000 : ℝ)^6319
        have hw : |(-2151651817/10000000000 : ℝ)|=(2151651817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348185907/2500000000 : ℝ)|^8367 ≤ (44145740763573/100000000000000 : ℝ)^6319
        have hw : |(1348185907/2500000000 : ℝ)|=(1348185907/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632983563/5000000000 : ℝ)|^8367 ≤ (42776837761951/100000000000000 : ℝ)^6319
        have hw : |(2632983563/5000000000 : ℝ)|=(2632983563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s6_1 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (53447049/100000000 : ℝ)*x 0 + (-2215950979/10000000000 : ℝ)*x 1 + (5265967381/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53447049/100000000 : ℝ)^8367 ≤ (5453223588179/12500000000000 : ℝ)^6319 := by
    have hnat : (53447049 : ℕ)^8367*12500000000000^6319 ≤ 5453223588179^6319*100000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53447049 100000000 5453223588179 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2215950979/10000000000 : ℝ)^8367 ≤ (13597370765283/100000000000000 : ℝ)^6319 := by
    have hnat : (2215950979 : ℕ)^8367*100000000000000^6319 ≤ 13597370765283^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215950979 10000000000 13597370765283 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265967381/10000000000 : ℝ)^8367 ≤ (42776840504739/100000000000000 : ℝ)^6319 := by
    have hnat : (5265967381 : ℕ)^8367*100000000000000^6319 ≤ 42776840504739^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265967381 10000000000 42776840504739 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53447049/100000000 : ℝ), (-2215950979/10000000000 : ℝ), (5265967381/10000000000 : ℝ)] ![(5453223588179/12500000000000 : ℝ), (13597370765283/100000000000000 : ℝ), (42776840504739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53447049/100000000 : ℝ)|^8367 ≤ (5453223588179/12500000000000 : ℝ)^6319
        have hw : |(53447049/100000000 : ℝ)|=(53447049/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2215950979/10000000000 : ℝ)|^8367 ≤ (13597370765283/100000000000000 : ℝ)^6319
        have hw : |(-2215950979/10000000000 : ℝ)|=(2215950979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265967381/10000000000 : ℝ)|^8367 ≤ (42776840504739/100000000000000 : ℝ)^6319
        have hw : |(5265967381/10000000000 : ℝ)|=(5265967381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s6_2 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336176229/2500000000 : ℝ)*x 0 + (1316491721/2500000000 : ℝ)*x 1 + (-8656061/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336176229/2500000000 : ℝ)^8367 ≤ (21812894439179/50000000000000 : ℝ)^6319 := by
    have hnat : (1336176229 : ℕ)^8367*50000000000000^6319 ≤ 21812894439179^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336176229 2500000000 21812894439179 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316491721/2500000000 : ℝ)^8367 ≤ (42776835158993/100000000000000 : ℝ)^6319 := by
    have hnat : (1316491721 : ℕ)^8367*100000000000000^6319 ≤ 42776835158993^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316491721 2500000000 42776835158993 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8656061/39062500 : ℝ)^8367 ≤ (13597375940823/100000000000000 : ℝ)^6319 := by
    have hnat : (8656061 : ℕ)^8367*100000000000000^6319 ≤ 13597375940823^6319*39062500^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8656061 39062500 13597375940823 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336176229/2500000000 : ℝ), (1316491721/2500000000 : ℝ), (-8656061/39062500 : ℝ)] ![(21812894439179/50000000000000 : ℝ), (42776835158993/100000000000000 : ℝ), (13597375940823/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336176229/2500000000 : ℝ)|^8367 ≤ (21812894439179/50000000000000 : ℝ)^6319
        have hw : |(1336176229/2500000000 : ℝ)|=(1336176229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316491721/2500000000 : ℝ)|^8367 ≤ (42776835158993/100000000000000 : ℝ)^6319
        have hw : |(1316491721/2500000000 : ℝ)|=(1316491721/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8656061/39062500 : ℝ)|^8367 ≤ (13597375940823/100000000000000 : ℝ)^6319
        have hw : |(-8656061/39062500 : ℝ)|=(8656061/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s6_3 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180084981/5000000000 : ℝ)*x 0 + (4235092363/10000000000 : ℝ)*x 1 + (448889581/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180084981/5000000000 : ℝ)^8367 ≤ (33316992137387/100000000000000 : ℝ)^6319 := by
    have hnat : (2180084981 : ℕ)^8367*100000000000000^6319 ≤ 33316992137387^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180084981 5000000000 33316992137387 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235092363/10000000000 : ℝ)^8367 ≤ (32057410114363/100000000000000 : ℝ)^6319 := by
    have hnat : (4235092363 : ℕ)^8367*100000000000000^6319 ≤ 32057410114363^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235092363 10000000000 32057410114363 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448889581/1000000000 : ℝ)^8367 ≤ (4328199717273/12500000000000 : ℝ)^6319 := by
    have hnat : (448889581 : ℕ)^8367*12500000000000^6319 ≤ 4328199717273^6319*1000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448889581 1000000000 4328199717273 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180084981/5000000000 : ℝ), (4235092363/10000000000 : ℝ), (448889581/1000000000 : ℝ)] ![(33316992137387/100000000000000 : ℝ), (32057410114363/100000000000000 : ℝ), (4328199717273/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180084981/5000000000 : ℝ)|^8367 ≤ (33316992137387/100000000000000 : ℝ)^6319
        have hw : |(2180084981/5000000000 : ℝ)|=(2180084981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235092363/10000000000 : ℝ)|^8367 ≤ (32057410114363/100000000000000 : ℝ)^6319
        have hw : |(4235092363/10000000000 : ℝ)|=(4235092363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448889581/1000000000 : ℝ)|^8367 ≤ (4328199717273/12500000000000 : ℝ)^6319
        have hw : |(448889581/1000000000 : ℝ)|=(448889581/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s6_4 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-537914137/2500000000 : ℝ)*x 0 + (5266287427/10000000000 : ℝ)*x 1 + (5392422269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537914137/2500000000 : ℝ)^8367 ≤ (13077459532741/100000000000000 : ℝ)^6319 := by
    have hnat : (537914137 : ℕ)^8367*100000000000000^6319 ≤ 13077459532741^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537914137 2500000000 13077459532741 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266287427/10000000000 : ℝ)^8367 ≤ (10695070740653/25000000000000 : ℝ)^6319 := by
    have hnat : (5266287427 : ℕ)^8367*25000000000000^6319 ≤ 10695070740653^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266287427 10000000000 10695070740653 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392422269/10000000000 : ℝ)^8367 ≤ (44142257496927/100000000000000 : ℝ)^6319 := by
    have hnat : (5392422269 : ℕ)^8367*100000000000000^6319 ≤ 44142257496927^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392422269 10000000000 44142257496927 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-537914137/2500000000 : ℝ), (5266287427/10000000000 : ℝ), (5392422269/10000000000 : ℝ)] ![(13077459532741/100000000000000 : ℝ), (10695070740653/25000000000000 : ℝ), (44142257496927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-537914137/2500000000 : ℝ)|^8367 ≤ (13077459532741/100000000000000 : ℝ)^6319
        have hw : |(-537914137/2500000000 : ℝ)|=(537914137/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266287427/10000000000 : ℝ)|^8367 ≤ (10695070740653/25000000000000 : ℝ)^6319
        have hw : |(5266287427/10000000000 : ℝ)|=(5266287427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392422269/10000000000 : ℝ)|^8367 ≤ (44142257496927/100000000000000 : ℝ)^6319
        have hw : |(5392422269/10000000000 : ℝ)|=(5392422269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s6_5 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312510407/10000000000 : ℝ)*x 0 + (-2089495963/10000000000 : ℝ)*x 1 + (43139379/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312510407/10000000000 : ℝ)^8367 ≤ (43278174232407/100000000000000 : ℝ)^6319 := by
    have hnat : (5312510407 : ℕ)^8367*100000000000000^6319 ≤ 43278174232407^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312510407 10000000000 43278174232407 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2089495963/10000000000 : ℝ)^8367 ≤ (6289783554559/50000000000000 : ℝ)^6319 := by
    have hnat : (2089495963 : ℕ)^8367*50000000000000^6319 ≤ 6289783554559^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089495963 10000000000 6289783554559 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43139379/80000000 : ℝ)^8367 ≤ (44142258645869/100000000000000 : ℝ)^6319 := by
    have hnat : (43139379 : ℕ)^8367*100000000000000^6319 ≤ 44142258645869^6319*80000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43139379 80000000 44142258645869 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312510407/10000000000 : ℝ), (-2089495963/10000000000 : ℝ), (43139379/80000000 : ℝ)] ![(43278174232407/100000000000000 : ℝ), (6289783554559/50000000000000 : ℝ), (44142258645869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312510407/10000000000 : ℝ)|^8367 ≤ (43278174232407/100000000000000 : ℝ)^6319
        have hw : |(5312510407/10000000000 : ℝ)|=(5312510407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2089495963/10000000000 : ℝ)|^8367 ≤ (6289783554559/50000000000000 : ℝ)^6319
        have hw : |(-2089495963/10000000000 : ℝ)|=(2089495963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43139379/80000000 : ℝ)|^8367 ≤ (44142258645869/100000000000000 : ℝ)^6319
        have hw : |(43139379/80000000 : ℝ)|=(43139379/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s6_6 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656255189/5000000000 : ℝ)*x 0 + (1078484491/2000000000 : ℝ)*x 1 + (-522373973/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656255189/5000000000 : ℝ)^8367 ≤ (43278173919591/100000000000000 : ℝ)^6319 := by
    have hnat : (2656255189 : ℕ)^8367*100000000000000^6319 ≤ 43278173919591^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656255189 5000000000 43278173919591 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078484491/2000000000 : ℝ)^8367 ≤ (22071129756497/50000000000000 : ℝ)^6319 := by
    have hnat : (1078484491 : ℕ)^8367*50000000000000^6319 ≤ 22071129756497^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078484491 2000000000 22071129756497 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522373973/2500000000 : ℝ)^8367 ≤ (6289783271567/50000000000000 : ℝ)^6319 := by
    have hnat : (522373973 : ℕ)^8367*50000000000000^6319 ≤ 6289783271567^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522373973 2500000000 6289783271567 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656255189/5000000000 : ℝ), (1078484491/2000000000 : ℝ), (-522373973/2500000000 : ℝ)] ![(43278173919591/100000000000000 : ℝ), (22071129756497/50000000000000 : ℝ), (6289783271567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656255189/5000000000 : ℝ)|^8367 ≤ (43278173919591/100000000000000 : ℝ)^6319
        have hw : |(2656255189/5000000000 : ℝ)|=(2656255189/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078484491/2000000000 : ℝ)|^8367 ≤ (22071129756497/50000000000000 : ℝ)^6319
        have hw : |(1078484491/2000000000 : ℝ)|=(1078484491/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-522373973/2500000000 : ℝ)|^8367 ≤ (6289783271567/50000000000000 : ℝ)^6319
        have hw : |(-522373973/2500000000 : ℝ)|=(522373973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s6_7 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360179859/10000000000 : ℝ)*x 0 + (4488254361/10000000000 : ℝ)*x 1 + (1058934001/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360179859/10000000000 : ℝ)^8367 ≤ (16658546136379/50000000000000 : ℝ)^6319 := by
    have hnat : (4360179859 : ℕ)^8367*50000000000000^6319 ≤ 16658546136379^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360179859 10000000000 16658546136379 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488254361/10000000000 : ℝ)^8367 ≤ (34619046381531/100000000000000 : ℝ)^6319 := by
    have hnat : (4488254361 : ℕ)^8367*100000000000000^6319 ≤ 34619046381531^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488254361 10000000000 34619046381531 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058934001/2500000000 : ℝ)^8367 ≤ (32063861327001/100000000000000 : ℝ)^6319 := by
    have hnat : (1058934001 : ℕ)^8367*100000000000000^6319 ≤ 32063861327001^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058934001 2500000000 32063861327001 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360179859/10000000000 : ℝ), (4488254361/10000000000 : ℝ), (1058934001/2500000000 : ℝ)] ![(16658546136379/50000000000000 : ℝ), (34619046381531/100000000000000 : ℝ), (32063861327001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360179859/10000000000 : ℝ)|^8367 ≤ (16658546136379/50000000000000 : ℝ)^6319
        have hw : |(4360179859/10000000000 : ℝ)|=(4360179859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488254361/10000000000 : ℝ)|^8367 ≤ (34619046381531/100000000000000 : ℝ)^6319
        have hw : |(4488254361/10000000000 : ℝ)|=(4488254361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058934001/2500000000 : ℝ)|^8367 ≤ (32063861327001/100000000000000 : ℝ)^6319
        have hw : |(1058934001/2500000000 : ℝ)|=(1058934001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1174_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2847/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7037/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11361/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7051/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11361/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11361/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7051/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11361/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11361/100000 : ℝ) ^ (4183/1024 : ℝ) ≤ (13848844687064109/100000000000000000000 : ℝ) := by
    have hpowers : (11361/100000 : ℝ)^4183 ≤ (13848844687064109/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11361 : ℕ)^4183*100000000000000000000^1024 ≤ 13848844687064109^1024*100000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11361 100000 13848844687064109 100000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11361/100000 : ℝ)) (X := (13848844687064109/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7051/50000 : ℝ) ^ (4183/1024 : ℝ) ≤ (16742292970414049/50000000000000000000 : ℝ) := by
    have hpowers : (7051/50000 : ℝ)^4183 ≤ (16742292970414049/50000000000000000000 : ℝ)^1024 := by
      have hnat : (7051 : ℕ)^4183*50000000000000000000^1024 ≤ 16742292970414049^1024*50000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7051 50000 16742292970414049 50000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7051/50000 : ℝ)) (X := (16742292970414049/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013848844687064109/50000000000000000000 : ℝ) ≤ (10000677969592977/10000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (50013848844687064109/50000000000000000000 : ℝ)^1024 ≤ (10000677969592977/10000000000000000 : ℝ)^4183 := by
      have hnat : (50013848844687064109 : ℕ)^1024*10000000000000000^4183 ≤ 10000677969592977^4183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013848844687064109 50000000000000000000 10000677969592977 10000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000677969592977/10000000000000000 : ℝ)) (X := (50013848844687064109/50000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047333430627892207/100000000000000000000 : ℝ) ≤ (625072407321859/625000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (100047333430627892207/100000000000000000000 : ℝ)^1024 ≤ (625072407321859/625000000000000 : ℝ)^4183 := by
      have hnat : (100047333430627892207 : ℕ)^1024*625000000000000^4183 ≤ 625072407321859^4183*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047333430627892207 100000000000000000000 625072407321859 625000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625072407321859/625000000000000 : ℝ)) (X := (100047333430627892207/100000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016742292970414049/25000000000000000000 : ℝ) ≤ (10001639064706511/10000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (25016742292970414049/25000000000000000000 : ℝ)^1024 ≤ (10001639064706511/10000000000000000 : ℝ)^4183 := by
      have hnat : (25016742292970414049 : ℕ)^1024*10000000000000000^4183 ≤ 10001639064706511^4183*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016742292970414049 25000000000000000000 10001639064706511 10000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001639064706511/10000000000000000 : ℝ)) (X := (25016742292970414049/25000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13848844687064109/100000000000000000000 : ℝ) ≤ ((27400939313069490183/27410000000000000000 : ℝ)+2*(480547556767/274100000000000 : ℝ)*(11361/100000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (27400939313069490183/27410000000000000000 : ℝ)+2*(480547556767/274100000000000 : ℝ)*(11361/100000 : ℝ)=(10000677969592977/10000000000000000 : ℝ) by norm_num, show 1+2*(13848844687064109/100000000000000000000 : ℝ)=(50013848844687064109/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16742292970414049/50000000000000000000 : ℝ)+(13848844687064109/100000000000000000000 : ℝ) ≤ ((27400939313069490183/27410000000000000000 : ℝ)+(480547556767/274100000000000 : ℝ)*((7051/50000 : ℝ)+(11361/100000 : ℝ)))^(4183/1024 : ℝ) := by
    rw [show (27400939313069490183/27410000000000000000 : ℝ)+(480547556767/274100000000000 : ℝ)*((7051/50000 : ℝ)+(11361/100000 : ℝ))=(625072407321859/625000000000000 : ℝ) by norm_num, show 1+(16742292970414049/50000000000000000000 : ℝ)+(13848844687064109/100000000000000000000 : ℝ)=(100047333430627892207/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16742292970414049/50000000000000000000 : ℝ) ≤ ((27400939313069490183/27410000000000000000 : ℝ)+2*(480547556767/274100000000000 : ℝ)*(7051/50000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (27400939313069490183/27410000000000000000 : ℝ)+2*(480547556767/274100000000000 : ℝ)*(7051/50000 : ℝ)=(10001639064706511/10000000000000000 : ℝ) by norm_num, show 1+2*(16742292970414049/50000000000000000000 : ℝ)=(25016742292970414049/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27400939313069490183/27410000000000000000 : ℝ)*(X 1 0+X 2 0)+(480547556767/274100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (27400939313069490183/27410000000000000000 : ℝ)) (alpha := (480547556767/274100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27400939313069490183/27410000000000000000 : ℝ)*(X 0 1+X 2 1)+(480547556767/274100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (27400939313069490183/27410000000000000000 : ℝ)) (alpha := (480547556767/274100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27400939313069490183/27410000000000000000 : ℝ)*(X 0 2+X 1 2)+(480547556767/274100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (11361/100000 : ℝ)) (hi := (7051/50000 : ℝ)) (c := (27400939313069490183/27410000000000000000 : ℝ)) (alpha := (480547556767/274100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2151651817/10000000000 : ℝ)*X 0 0+(1348185907/2500000000 : ℝ)*X 0 1+(2632983563/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53447049/100000000 : ℝ)*X 1 0+(-2215950979/10000000000 : ℝ)*X 1 1+(5265967381/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336176229/2500000000 : ℝ)*X 2 0+(1316491721/2500000000 : ℝ)*X 2 1+(-8656061/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180084981/5000000000 : ℝ)*X 0 0+(4235092363/10000000000 : ℝ)*X 0 1+(448889581/1000000000 : ℝ)*X 0 2+(2180084981/5000000000 : ℝ)*X 1 0+(4235092363/10000000000 : ℝ)*X 1 1+(448889581/1000000000 : ℝ)*X 1 2+(2180084981/5000000000 : ℝ)*X 2 0+(4235092363/10000000000 : ℝ)*X 2 1+(448889581/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-537914137/2500000000 : ℝ)*X 0 0+(5266287427/10000000000 : ℝ)*X 0 1+(5392422269/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312510407/10000000000 : ℝ)*X 1 0+(-2089495963/10000000000 : ℝ)*X 1 1+(43139379/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656255189/5000000000 : ℝ)*X 2 0+(1078484491/2000000000 : ℝ)*X 2 1+(-522373973/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360179859/10000000000 : ℝ)*X 0 0+(4488254361/10000000000 : ℝ)*X 0 1+(1058934001/2500000000 : ℝ)*X 0 2+(4360179859/10000000000 : ℝ)*X 1 0+(4488254361/10000000000 : ℝ)*X 1 1+(1058934001/2500000000 : ℝ)*X 1 2+(4360179859/10000000000 : ℝ)*X 2 0+(4488254361/10000000000 : ℝ)*X 2 1+(1058934001/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (143666990854849007335983/13705000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1456711973/100000000000000 : ℝ)*(base19) + (1389999139/100000000000000 : ℝ)*(base23) + (4800727/20000000000000 : ℝ)*(upper2) + (438232931/100000000000000 : ℝ)*(upper3) + (1478513693006123/25000000000000 : ℝ)*(major0) + (1478513693006123/25000000000000 : ℝ)*(major1) + (5914054772024493/100000000000000 : ℝ)*(major2) + (7887956231981497/100000000000000 : ℝ)*(sp0) + (7887990560533447/100000000000000 : ℝ)*(sp1) + (7887968176089363/100000000000000 : ℝ)*(sp2) + (1970041435440877/50000000000000 : ℝ)*(sp3) + (8946315981/25000000000000 : ℝ)*(sp4) + (11225578459/50000000000000 : ℝ)*(sp6) + (6861298921/20000000000000 : ℝ)*(sp7) + (1970058588688179/50000000000000 : ℝ)*(f.failure) + (7887992017245421/100000000000000 : ℝ)*(f.sum) + (3446399290229/1096400000000000000000000000 : ℝ)*base66 + (13201687165917084491/685250000000000000000000000000000 : ℝ)*base68 + (38192657678422547781/2741000000000000000000000000000000 : ℝ)*base70 + (5301866533380084491/685250000000000000000000000000000 : ℝ)*base72 + (17062837565809/5482000000000000000000000000 : ℝ)*base74 + (19370257926988452219/2741000000000000000000000000000000 : ℝ)*base75 + (4095895199177740509/685250000000000000000000000000000 : ℝ)*base77 + (1220464132854240509/685250000000000000000000000000000 : ℝ)*base79 + (32460112859079/3426250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (12534371/5000000000000000000000 : ℝ)*base89 + (12534371/5000000000000000000000 : ℝ)*base91 + (37465629/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3243569368087624319274297303/342625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1180592359/100000000000000 : ℝ)*(base19) + (744914739/50000000000000 : ℝ)*(base23) + (43966109/20000000000000 : ℝ)*(upper3) + (136765041/100000000000000 : ℝ)*(lower4) + (30069963/25000000000000 : ℝ)*(upper5) + (2972031100968547/50000000000000 : ℝ)*(major0) + (2972031100968547/50000000000000 : ℝ)*(major1) + (2972031100968547/50000000000000 : ℝ)*(major2) + (32278164389/100000000000000 : ℝ)*(sp1) + (11991681169/25000000000000 : ℝ)*(sp2) + (3964007539417299/50000000000000 : ℝ)*(sp4) + (158559632401557/2000000000000 : ℝ)*(sp5) + (7927965622280443/100000000000000 : ℝ)*(sp6) + (1980054504739451/50000000000000 : ℝ)*(sp7) + (1980054504739451/50000000000000 : ℝ)*(f.failure) + (3964007539417299/50000000000000 : ℝ)*(f.sum) + (1228325212777/214140625000000000000000000 : ℝ)*base65 + (14186565014080825899/1370500000000000000000000000000000 : ℝ)*base68 + (690373711571825899/1370500000000000000000000000000000 : ℝ)*base70 + (7080296244530825899/1370500000000000000000000000000000 : ℝ)*base72 + (20071383712807/13705000000000000000000000000 : ℝ)*base74 + (3141959877510325899/1370500000000000000000000000000000 : ℝ)*base76 + (7807557030740825899/1370500000000000000000000000000000 : ℝ)*base78 + (8830306907674101/1370500000000000000000000000000000 : ℝ)*base79 + (14912302233359/6852500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (44211499/5000000000000000000000 : ℝ)*base89 + (44211499/5000000000000000000000 : ℝ)*base91 + (44211499/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1174_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2847/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1174_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1174_s7_0 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-430334987/2000000000 : ℝ)*x 0 + (2696235379/5000000000 : ℝ)*x 1 + (2633112403/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430334987/2000000000 : ℝ)^8367 ≤ (13077607506029/100000000000000 : ℝ)^6319 := by
    have hnat : (430334987 : ℕ)^8367*100000000000000^6319 ≤ 13077607506029^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430334987 2000000000 13077607506029 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696235379/5000000000 : ℝ)^8367 ≤ (8828556614681/20000000000000 : ℝ)^6319 := by
    have hnat : (2696235379 : ℕ)^8367*20000000000000^6319 ≤ 8828556614681^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696235379 5000000000 8828556614681 20000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633112403/5000000000 : ℝ)^8367 ≤ (5347451174671/12500000000000 : ℝ)^6319 := by
    have hnat : (2633112403 : ℕ)^8367*12500000000000^6319 ≤ 5347451174671^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633112403 5000000000 5347451174671 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430334987/2000000000 : ℝ), (2696235379/5000000000 : ℝ), (2633112403/5000000000 : ℝ)] ![(13077607506029/100000000000000 : ℝ), (8828556614681/20000000000000 : ℝ), (5347451174671/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430334987/2000000000 : ℝ)|^8367 ≤ (13077607506029/100000000000000 : ℝ)^6319
        have hw : |(-430334987/2000000000 : ℝ)|=(430334987/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696235379/5000000000 : ℝ)|^8367 ≤ (8828556614681/20000000000000 : ℝ)^6319
        have hw : |(2696235379/5000000000 : ℝ)|=(2696235379/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633112403/5000000000 : ℝ)|^8367 ≤ (5347451174671/12500000000000 : ℝ)^6319
        have hw : |(2633112403/5000000000 : ℝ)|=(2633112403/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s7_1 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344636021/10000000000 : ℝ)*x 0 + (-69240653/312500000 : ℝ)*x 1 + (1053245099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344636021/10000000000 : ℝ)^8367 ≤ (5453130533779/12500000000000 : ℝ)^6319 := by
    have hnat : (5344636021 : ℕ)^8367*12500000000000^6319 ≤ 5453130533779^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344636021 10000000000 5453130533779 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (69240653/312500000 : ℝ)^8367 ≤ (1699417363949/12500000000000 : ℝ)^6319 := by
    have hnat : (69240653 : ℕ)^8367*12500000000000^6319 ≤ 1699417363949^6319*312500000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      69240653 312500000 1699417363949 12500000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053245099/2000000000 : ℝ)^8367 ≤ (42779616808389/100000000000000 : ℝ)^6319 := by
    have hnat : (1053245099 : ℕ)^8367*100000000000000^6319 ≤ 42779616808389^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053245099 2000000000 42779616808389 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344636021/10000000000 : ℝ), (-69240653/312500000 : ℝ), (1053245099/2000000000 : ℝ)] ![(5453130533779/12500000000000 : ℝ), (1699417363949/12500000000000 : ℝ), (42779616808389/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344636021/10000000000 : ℝ)|^8367 ≤ (5453130533779/12500000000000 : ℝ)^6319
        have hw : |(5344636021/10000000000 : ℝ)|=(5344636021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-69240653/312500000 : ℝ)|^8367 ≤ (1699417363949/12500000000000 : ℝ)^6319
        have hw : |(-69240653/312500000 : ℝ)|=(69240653/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053245099/2000000000 : ℝ)|^8367 ≤ (42779616808389/100000000000000 : ℝ)^6319
        have hw : |(1053245099/2000000000 : ℝ)|=(1053245099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s7_2 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344637369/10000000000 : ℝ)*x 0 + (1316556039/2500000000 : ℝ)*x 1 + (-17725607/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344637369/10000000000 : ℝ)^8367 ≤ (43625058839209/100000000000000 : ℝ)^6319 := by
    have hnat : (5344637369 : ℕ)^8367*100000000000000^6319 ≤ 43625058839209^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344637369 10000000000 43625058839209 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316556039/2500000000 : ℝ)^8367 ≤ (42779602405839/100000000000000 : ℝ)^6319 := by
    have hnat : (1316556039 : ℕ)^8367*100000000000000^6319 ≤ 42779602405839^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316556039 2500000000 42779602405839 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (17725607/80000000 : ℝ)^8367 ≤ (849708671311/6250000000000 : ℝ)^6319 := by
    have hnat : (17725607 : ℕ)^8367*6250000000000^6319 ≤ 849708671311^6319*80000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17725607 80000000 849708671311 6250000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344637369/10000000000 : ℝ), (1316556039/2500000000 : ℝ), (-17725607/80000000 : ℝ)] ![(43625058839209/100000000000000 : ℝ), (42779602405839/100000000000000 : ℝ), (849708671311/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344637369/10000000000 : ℝ)|^8367 ≤ (43625058839209/100000000000000 : ℝ)^6319
        have hw : |(5344637369/10000000000 : ℝ)|=(5344637369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316556039/2500000000 : ℝ)|^8367 ≤ (42779602405839/100000000000000 : ℝ)^6319
        have hw : |(1316556039/2500000000 : ℝ)|=(1316556039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-17725607/80000000 : ℝ)|^8367 ≤ (849708671311/6250000000000 : ℝ)^6319
        have hw : |(-17725607/80000000 : ℝ)|=(17725607/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s7_3 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2180091751/5000000000 : ℝ)*x 0 + (4235622783/10000000000 : ℝ)*x 1 + (4488361867/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2180091751/5000000000 : ℝ)^8367 ≤ (1665856456587/5000000000000 : ℝ)^6319 := by
    have hnat : (2180091751 : ℕ)^8367*5000000000000^6319 ≤ 1665856456587^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2180091751 5000000000 1665856456587 5000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4235622783/10000000000 : ℝ)^8367 ≤ (16031363245041/50000000000000 : ℝ)^6319 := by
    have hnat : (4235622783 : ℕ)^8367*50000000000000^6319 ≤ 16031363245041^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235622783 10000000000 16031363245041 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488361867/10000000000 : ℝ)^8367 ≤ (17310072179517/50000000000000 : ℝ)^6319 := by
    have hnat : (4488361867 : ℕ)^8367*50000000000000^6319 ≤ 17310072179517^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488361867 10000000000 17310072179517 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2180091751/5000000000 : ℝ), (4235622783/10000000000 : ℝ), (4488361867/10000000000 : ℝ)] ![(1665856456587/5000000000000 : ℝ), (16031363245041/50000000000000 : ℝ), (17310072179517/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2180091751/5000000000 : ℝ)|^8367 ≤ (1665856456587/5000000000000 : ℝ)^6319
        have hw : |(2180091751/5000000000 : ℝ)|=(2180091751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4235622783/10000000000 : ℝ)|^8367 ≤ (16031363245041/50000000000000 : ℝ)^6319
        have hw : |(4235622783/10000000000 : ℝ)|=(4235622783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488361867/10000000000 : ℝ)|^8367 ≤ (17310072179517/50000000000000 : ℝ)^6319
        have hw : |(4488361867/10000000000 : ℝ)|=(4488361867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s7_4 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151679717/10000000000 : ℝ)*x 0 + (2633271221/5000000000 : ℝ)*x 1 + (1348037999/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151679717/10000000000 : ℝ)^8367 ≤ (13077645990257/100000000000000 : ℝ)^6319 := by
    have hnat : (2151679717 : ℕ)^8367*100000000000000^6319 ≤ 13077645990257^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151679717 10000000000 13077645990257 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633271221/5000000000 : ℝ)^8367 ≤ (42783025986831/100000000000000 : ℝ)^6319 := by
    have hnat : (2633271221 : ℕ)^8367*100000000000000^6319 ≤ 42783025986831^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633271221 5000000000 42783025986831 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348037999/2500000000 : ℝ)^8367 ≤ (44139328012493/100000000000000 : ℝ)^6319 := by
    have hnat : (1348037999 : ℕ)^8367*100000000000000^6319 ≤ 44139328012493^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348037999 2500000000 44139328012493 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151679717/10000000000 : ℝ), (2633271221/5000000000 : ℝ), (1348037999/2500000000 : ℝ)] ![(13077645990257/100000000000000 : ℝ), (42783025986831/100000000000000 : ℝ), (44139328012493/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151679717/10000000000 : ℝ)|^8367 ≤ (13077645990257/100000000000000 : ℝ)^6319
        have hw : |(-2151679717/10000000000 : ℝ)|=(2151679717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633271221/5000000000 : ℝ)|^8367 ≤ (42783025986831/100000000000000 : ℝ)^6319
        have hw : |(2633271221/5000000000 : ℝ)|=(2633271221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348037999/2500000000 : ℝ)|^8367 ≤ (44139328012493/100000000000000 : ℝ)^6319
        have hw : |(1348037999/2500000000 : ℝ)|=(1348037999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s7_5 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312577191/10000000000 : ℝ)*x 0 + (-1044886807/5000000000 : ℝ)*x 1 + (1348037927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312577191/10000000000 : ℝ)^8367 ≤ (21639447308041/50000000000000 : ℝ)^6319 := by
    have hnat : (5312577191 : ℕ)^8367*50000000000000^6319 ≤ 21639447308041^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312577191 10000000000 21639447308041 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044886807/5000000000 : ℝ)^8367 ≤ (1258178047987/10000000000000 : ℝ)^6319 := by
    have hnat : (1044886807 : ℕ)^8367*10000000000000^6319 ≤ 1258178047987^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044886807 5000000000 1258178047987 10000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348037927/2500000000 : ℝ)^8367 ≤ (44139324890891/100000000000000 : ℝ)^6319 := by
    have hnat : (1348037927 : ℕ)^8367*100000000000000^6319 ≤ 44139324890891^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348037927 2500000000 44139324890891 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312577191/10000000000 : ℝ), (-1044886807/5000000000 : ℝ), (1348037927/2500000000 : ℝ)] ![(21639447308041/50000000000000 : ℝ), (1258178047987/10000000000000 : ℝ), (44139324890891/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312577191/10000000000 : ℝ)|^8367 ≤ (21639447308041/50000000000000 : ℝ)^6319
        have hw : |(5312577191/10000000000 : ℝ)|=(5312577191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1044886807/5000000000 : ℝ)|^8367 ≤ (1258178047987/10000000000000 : ℝ)^6319
        have hw : |(-1044886807/5000000000 : ℝ)|=(1044886807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348037927/2500000000 : ℝ)|^8367 ≤ (44139324890891/100000000000000 : ℝ)^6319
        have hw : |(1348037927/2500000000 : ℝ)|=(1348037927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s7_6 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656288601/5000000000 : ℝ)*x 0 + (107843031/200000000 : ℝ)*x 1 + (-2089773813/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656288601/5000000000 : ℝ)^8367 ≤ (43278894734737/100000000000000 : ℝ)^6319 := by
    have hnat : (2656288601 : ℕ)^8367*100000000000000^6319 ≤ 43278894734737^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656288601 5000000000 43278894734737 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (107843031/200000000 : ℝ)^8367 ≤ (22069661589173/50000000000000 : ℝ)^6319 := by
    have hnat : (107843031 : ℕ)^8367*50000000000000^6319 ≤ 22069661589173^6319*200000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107843031 200000000 22069661589173 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2089773813/10000000000 : ℝ)^8367 ≤ (12581782066287/100000000000000 : ℝ)^6319 := by
    have hnat : (2089773813 : ℕ)^8367*100000000000000^6319 ≤ 12581782066287^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2089773813 10000000000 12581782066287 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656288601/5000000000 : ℝ), (107843031/200000000 : ℝ), (-2089773813/10000000000 : ℝ)] ![(43278894734737/100000000000000 : ℝ), (22069661589173/50000000000000 : ℝ), (12581782066287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656288601/5000000000 : ℝ)|^8367 ≤ (43278894734737/100000000000000 : ℝ)^6319
        have hw : |(2656288601/5000000000 : ℝ)|=(2656288601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(107843031/200000000 : ℝ)|^8367 ≤ (22069661589173/50000000000000 : ℝ)^6319
        have hw : |(107843031/200000000 : ℝ)|=(107843031/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2089773813/10000000000 : ℝ)|^8367 ≤ (12581782066287/100000000000000 : ℝ)^6319
        have hw : |(-2089773813/10000000000 : ℝ)|=(2089773813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s7_7 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360193261/10000000000 : ℝ)*x 0 + (2243863169/5000000000 : ℝ)*x 1 + (2118130241/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360193261/10000000000 : ℝ)^8367 ≤ (416465348387/1250000000000 : ℝ)^6319 := by
    have hnat : (4360193261 : ℕ)^8367*1250000000000^6319 ≤ 416465348387^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360193261 10000000000 416465348387 1250000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243863169/5000000000 : ℝ)^8367 ≤ (3461365371441/10000000000000 : ℝ)^6319 := by
    have hnat : (2243863169 : ℕ)^8367*10000000000000^6319 ≤ 3461365371441^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243863169 5000000000 3461365371441 10000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2118130241/5000000000 : ℝ)^8367 ≤ (3206911840403/10000000000000 : ℝ)^6319 := by
    have hnat : (2118130241 : ℕ)^8367*10000000000000^6319 ≤ 3206911840403^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118130241 5000000000 3206911840403 10000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360193261/10000000000 : ℝ), (2243863169/5000000000 : ℝ), (2118130241/5000000000 : ℝ)] ![(416465348387/1250000000000 : ℝ), (3461365371441/10000000000000 : ℝ), (3206911840403/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360193261/10000000000 : ℝ)|^8367 ≤ (416465348387/1250000000000 : ℝ)^6319
        have hw : |(4360193261/10000000000 : ℝ)|=(4360193261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243863169/5000000000 : ℝ)|^8367 ≤ (3461365371441/10000000000000 : ℝ)^6319
        have hw : |(2243863169/5000000000 : ℝ)|=(2243863169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2118130241/5000000000 : ℝ)|^8367 ≤ (3206911840403/10000000000000 : ℝ)^6319
        have hw : |(2118130241/5000000000 : ℝ)|=(2118130241/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s7_8 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-36415167/10000000000 : ℝ)*x 0 + (1163517399/2000000000 : ℝ)*x 1 + (1205117637/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36415167/10000000000 : ℝ)^8367 ≤ (59005056633/100000000000000 : ℝ)^6319 := by
    have hnat : (36415167 : ℕ)^8367*100000000000000^6319 ≤ 59005056633^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36415167 10000000000 59005056633 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1163517399/2000000000 : ℝ)^8367 ≤ (24404258112627/50000000000000 : ℝ)^6319 := by
    have hnat : (1163517399 : ℕ)^8367*50000000000000^6319 ≤ 24404258112627^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1163517399 2000000000 24404258112627 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205117637/2000000000 : ℝ)^8367 ≤ (10226495742031/20000000000000 : ℝ)^6319 := by
    have hnat : (1205117637 : ℕ)^8367*20000000000000^6319 ≤ 10226495742031^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205117637 2000000000 10226495742031 20000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-36415167/10000000000 : ℝ), (1163517399/2000000000 : ℝ), (1205117637/2000000000 : ℝ)] ![(59005056633/100000000000000 : ℝ), (24404258112627/50000000000000 : ℝ), (10226495742031/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-36415167/10000000000 : ℝ)|^8367 ≤ (59005056633/100000000000000 : ℝ)^6319
        have hw : |(-36415167/10000000000 : ℝ)|=(36415167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1163517399/2000000000 : ℝ)|^8367 ≤ (24404258112627/50000000000000 : ℝ)^6319
        have hw : |(1163517399/2000000000 : ℝ)|=(1163517399/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1205117637/2000000000 : ℝ)|^8367 ≤ (10226495742031/20000000000000 : ℝ)^6319
        have hw : |(1205117637/2000000000 : ℝ)|=(1205117637/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1174_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2847/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5697/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3517/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2847/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2847/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2847/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2847/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2847/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2847/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2847/25000 : ℝ) ^ (4183/1024 : ℝ) ≤ (13983784591255727/100000000000000000000 : ℝ) := by
    have hpowers : (2847/25000 : ℝ)^4183 ≤ (13983784591255727/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2847 : ℕ)^4183*100000000000000000000^1024 ≤ 13983784591255727^1024*25000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 25000 13983784591255727 100000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/25000 : ℝ)) (X := (13983784591255727/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7037/50000 : ℝ) ^ (4183/1024 : ℝ) ≤ (8303457207666087/25000000000000000000 : ℝ) := by
    have hpowers : (7037/50000 : ℝ)^4183 ≤ (8303457207666087/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7037 : ℕ)^4183*25000000000000000000^1024 ≤ 8303457207666087^1024*50000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7037 50000 8303457207666087 25000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7037/50000 : ℝ)) (X := (8303457207666087/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013983784591255727/50000000000000000000 : ℝ) ≤ (250017114371817/250000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (50013983784591255727/50000000000000000000 : ℝ)^1024 ≤ (250017114371817/250000000000000 : ℝ)^4183 := by
      have hnat : (50013983784591255727 : ℕ)^1024*250000000000000^4183 ≤ 250017114371817^4183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013983784591255727 50000000000000000000 250017114371817 250000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250017114371817/250000000000000 : ℝ)) (X := (50013983784591255727/50000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001887904536876803/4000000000000000000 : ℝ) ≤ (5000577596762821/5000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (4001887904536876803/4000000000000000000 : ℝ)^1024 ≤ (5000577596762821/5000000000000000 : ℝ)^4183 := by
      have hnat : (4001887904536876803 : ℕ)^1024*5000000000000000^4183 ≤ 5000577596762821^4183*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001887904536876803 4000000000000000000 5000577596762821 5000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000577596762821/5000000000000000 : ℝ)) (X := (4001887904536876803/4000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508303457207666087/12500000000000000000 : ℝ) ≤ (2500406453044651/2500000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (12508303457207666087/12500000000000000000 : ℝ)^1024 ≤ (2500406453044651/2500000000000000 : ℝ)^4183 := by
      have hnat : (12508303457207666087 : ℕ)^1024*2500000000000000^4183 ≤ 2500406453044651^4183*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508303457207666087 12500000000000000000 2500406453044651 2500000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500406453044651/2500000000000000 : ℝ)) (X := (12508303457207666087/12500000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13983784591255727/100000000000000000000 : ℝ) ≤ ((419548749338564937/419687500000000000 : ℝ)+2*(235309326481/134300000000000 : ℝ)*(2847/25000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (419548749338564937/419687500000000000 : ℝ)+2*(235309326481/134300000000000 : ℝ)*(2847/25000 : ℝ)=(250017114371817/250000000000000 : ℝ) by norm_num, show 1+2*(13983784591255727/100000000000000000000 : ℝ)=(50013983784591255727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8303457207666087/25000000000000000000 : ℝ)+(13983784591255727/100000000000000000000 : ℝ) ≤ ((419548749338564937/419687500000000000 : ℝ)+(235309326481/134300000000000 : ℝ)*((7037/50000 : ℝ)+(2847/25000 : ℝ)))^(4183/1024 : ℝ) := by
    rw [show (419548749338564937/419687500000000000 : ℝ)+(235309326481/134300000000000 : ℝ)*((7037/50000 : ℝ)+(2847/25000 : ℝ))=(5000577596762821/5000000000000000 : ℝ) by norm_num, show 1+(8303457207666087/25000000000000000000 : ℝ)+(13983784591255727/100000000000000000000 : ℝ)=(4001887904536876803/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8303457207666087/25000000000000000000 : ℝ) ≤ ((419548749338564937/419687500000000000 : ℝ)+2*(235309326481/134300000000000 : ℝ)*(7037/50000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (419548749338564937/419687500000000000 : ℝ)+2*(235309326481/134300000000000 : ℝ)*(7037/50000 : ℝ)=(2500406453044651/2500000000000000 : ℝ) by norm_num, show 1+2*(8303457207666087/25000000000000000000 : ℝ)=(12508303457207666087/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (419548749338564937/419687500000000000 : ℝ)*(X 1 0+X 2 0)+(235309326481/134300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (2847/25000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (419548749338564937/419687500000000000 : ℝ)) (alpha := (235309326481/134300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (419548749338564937/419687500000000000 : ℝ)*(X 0 1+X 2 1)+(235309326481/134300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (2847/25000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (419548749338564937/419687500000000000 : ℝ)) (alpha := (235309326481/134300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (419548749338564937/419687500000000000 : ℝ)*(X 0 2+X 1 2)+(235309326481/134300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (2847/25000 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (419548749338564937/419687500000000000 : ℝ)) (alpha := (235309326481/134300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-430334987/2000000000 : ℝ)*X 0 0+(2696235379/5000000000 : ℝ)*X 0 1+(2633112403/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344636021/10000000000 : ℝ)*X 1 0+(-69240653/312500000 : ℝ)*X 1 1+(1053245099/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344637369/10000000000 : ℝ)*X 2 0+(1316556039/2500000000 : ℝ)*X 2 1+(-17725607/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2180091751/5000000000 : ℝ)*X 0 0+(4235622783/10000000000 : ℝ)*X 0 1+(4488361867/10000000000 : ℝ)*X 0 2+(2180091751/5000000000 : ℝ)*X 1 0+(4235622783/10000000000 : ℝ)*X 1 1+(4488361867/10000000000 : ℝ)*X 1 2+(2180091751/5000000000 : ℝ)*X 2 0+(4235622783/10000000000 : ℝ)*X 2 1+(4488361867/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2151679717/10000000000 : ℝ)*X 0 0+(2633271221/5000000000 : ℝ)*X 0 1+(1348037999/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312577191/10000000000 : ℝ)*X 1 0+(-1044886807/5000000000 : ℝ)*X 1 1+(1348037927/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656288601/5000000000 : ℝ)*X 2 0+(107843031/200000000 : ℝ)*X 2 1+(-2089773813/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4360193261/10000000000 : ℝ)*X 0 0+(2243863169/5000000000 : ℝ)*X 0 1+(2118130241/5000000000 : ℝ)*X 0 2+(4360193261/10000000000 : ℝ)*X 1 0+(2243863169/5000000000 : ℝ)*X 1 1+(2118130241/5000000000 : ℝ)*X 1 2+(4360193261/10000000000 : ℝ)*X 2 0+(2243863169/5000000000 : ℝ)*X 2 1+(2118130241/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-36415167/10000000000 : ℝ)*X 0 0+(1163517399/2000000000 : ℝ)*X 0 1+(1205117637/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s7_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15044601387481695019981323/2623046875000000000000000000000 : ℝ) := by norm_num
    linear_combination (974498533/100000000000000 : ℝ)*(lower2) + (11907173/50000000000000 : ℝ)*(upper4) + (693603/160000000000 : ℝ)*(lower5) + (2969418814042803/50000000000000 : ℝ)*(major0) + (2969418814042803/50000000000000 : ℝ)*(major1) + (5938837628085607/100000000000000 : ℝ)*(major2) + (316841375029041/4000000000000 : ℝ)*(sp0) + (7921046820223113/100000000000000 : ℝ)*(sp1) + (990128144953373/12500000000000 : ℝ)*(sp2) + (395662462059021/10000000000000 : ℝ)*(sp3) + (6302598679/100000000000000 : ℝ)*(sp4) + (21660596129/100000000000000 : ℝ)*(sp6) + (362417307/10000000000000 : ℝ)*(sp7) + (614189841/10000000000000 : ℝ)*(sp8) + (49457853059541/1250000000000 : ℝ)*(f.failure) + (7921046820223113/100000000000000 : ℝ)*(f.sum) + (34711225285407/13430000000000000000000000000 : ℝ)*base66 + (1021639603441106303/41968750000000000000000000000000 : ℝ)*base68 + (968636564160231991/41968750000000000000000000000000 : ℝ)*base70 + (596688758646262553/41968750000000000000000000000000 : ℝ)*base72 + (44835133176607/13430000000000000000000000000 : ℝ)*base74 + (231287203044388241/41968750000000000000000000000000 : ℝ)*base76 + (91076779095402357/10492187500000000000000000000000 : ℝ)*base78 + (178955508799308607/10492187500000000000000000000000 : ℝ)*base80 + (14432217932609/6715000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1251909/125000000000000000000 : ℝ)*base89 + (1251909/125000000000000000000 : ℝ)*base91 + (1909/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21294999424375097484093/3357500000000000000000000000 : ℝ) := by norm_num
    linear_combination (865562137/100000000000000 : ℝ)*(lower2) + (294869971/100000000000000 : ℝ)*(lower3) + (214201193/25000000000000 : ℝ)*(lower4) + (614486967/100000000000000 : ℝ)*(lower5) + (2984486662394021/50000000000000 : ℝ)*(major0) + (2984486662394021/50000000000000 : ℝ)*(major1) + (5968973324788043/100000000000000 : ℝ)*(major2) + (21112795939/50000000000000 : ℝ)*(sp0) + (8030017331/100000000000000 : ℝ)*(sp3) + (7961189250737709/100000000000000 : ℝ)*(sp4) + (7961240906186273/100000000000000 : ℝ)*(sp5) + (7961240906186273/100000000000000 : ℝ)*(sp6) + (3976697501955249/100000000000000 : ℝ)*(sp7) + (4714928343/50000000000000 : ℝ)*(sp8) + (198835276598629/5000000000000 : ℝ)*(f.failure) + (7961240906186273/100000000000000 : ℝ)*(f.sum) + (117489035622539/2686000000000000000000000000 : ℝ)*base66 + (255889048911436479/41968750000000000000000000000000 : ℝ)*base67 + (113249783926189209/41968750000000000000000000000000 : ℝ)*base70 + (132498219746094771/41968750000000000000000000000000 : ℝ)*base72 + (9864075532259/2686000000000000000000000000 : ℝ)*base73 + (797232594639248291/41968750000000000000000000000000 : ℝ)*base75 + (65946308993002073/20984375000000000000000000000000 : ℝ)*base78 + (132977692921310427/20984375000000000000000000000000 : ℝ)*base79 + (501869888709/209843750000000000000000000 : ℝ)*base82 + (1573579/500000000000000000000 : ℝ)*base90 + (1573579/500000000000000000000 : ℝ)*base92 + (6573579/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1174_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2847/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1174_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1174_s8_0 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-430335737/2000000000 : ℝ)*x 0 + (539241217/1000000000 : ℝ)*x 1 + (65828513/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430335737/2000000000 : ℝ)^8367 ≤ (13077637685001/100000000000000 : ℝ)^6319 := by
    have hnat : (430335737 : ℕ)^8367*100000000000000^6319 ≤ 13077637685001^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430335737 2000000000 13077637685001 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539241217/1000000000 : ℝ)^8367 ≤ (22071074016591/50000000000000 : ℝ)^6319 := by
    have hnat : (539241217 : ℕ)^8367*50000000000000^6319 ≤ 22071074016591^6319*1000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539241217 1000000000 22071074016591 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65828513/125000000 : ℝ)^8367 ≤ (42780214262517/100000000000000 : ℝ)^6319 := by
    have hnat : (65828513 : ℕ)^8367*100000000000000^6319 ≤ 42780214262517^6319*125000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65828513 125000000 42780214262517 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430335737/2000000000 : ℝ), (539241217/1000000000 : ℝ), (65828513/125000000 : ℝ)] ![(13077637685001/100000000000000 : ℝ), (22071074016591/50000000000000 : ℝ), (42780214262517/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430335737/2000000000 : ℝ)|^8367 ≤ (13077637685001/100000000000000 : ℝ)^6319
        have hw : |(-430335737/2000000000 : ℝ)|=(430335737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539241217/1000000000 : ℝ)|^8367 ≤ (22071074016591/50000000000000 : ℝ)^6319
        have hw : |(539241217/1000000000 : ℝ)|=(539241217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65828513/125000000 : ℝ)|^8367 ≤ (42780214262517/100000000000000 : ℝ)^6319
        have hw : |(65828513/125000000 : ℝ)|=(65828513/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s8_1 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344621941/10000000000 : ℝ)*x 0 + (-88625843/400000000 : ℝ)*x 1 + (105325621/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344621941/10000000000 : ℝ)^8367 ≤ (43624892095821/100000000000000 : ℝ)^6319 := by
    have hnat : (5344621941 : ℕ)^8367*100000000000000^6319 ≤ 43624892095821^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344621941 10000000000 43624892095821 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (88625843/400000000 : ℝ)^8367 ≤ (13594893516393/100000000000000 : ℝ)^6319 := by
    have hnat : (88625843 : ℕ)^8367*100000000000000^6319 ≤ 13594893516393^6319*400000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      88625843 400000000 13594893516393 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (105325621/200000000 : ℝ)^8367 ≤ (42780214370079/100000000000000 : ℝ)^6319 := by
    have hnat : (105325621 : ℕ)^8367*100000000000000^6319 ≤ 42780214370079^6319*200000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105325621 200000000 42780214370079 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344621941/10000000000 : ℝ), (-88625843/400000000 : ℝ), (105325621/200000000 : ℝ)] ![(43624892095821/100000000000000 : ℝ), (13594893516393/100000000000000 : ℝ), (42780214370079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344621941/10000000000 : ℝ)|^8367 ≤ (43624892095821/100000000000000 : ℝ)^6319
        have hw : |(5344621941/10000000000 : ℝ)|=(5344621941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-88625843/400000000 : ℝ)|^8367 ≤ (13594893516393/100000000000000 : ℝ)^6319
        have hw : |(-88625843/400000000 : ℝ)|=(88625843/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(105325621/200000000 : ℝ)|^8367 ≤ (42780214370079/100000000000000 : ℝ)^6319
        have hw : |(105325621/200000000 : ℝ)|=(105325621/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s8_2 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344621929/10000000000 : ℝ)*x 0 + (1053256211/2000000000 : ℝ)*x 1 + (-443129217/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344621929/10000000000 : ℝ)^8367 ≤ (43624891966127/100000000000000 : ℝ)^6319 := by
    have hnat : (5344621929 : ℕ)^8367*100000000000000^6319 ≤ 43624891966127^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344621929 10000000000 43624891966127 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053256211/2000000000 : ℝ)^8367 ≤ (2139010721193/5000000000000 : ℝ)^6319 := by
    have hnat : (1053256211 : ℕ)^8367*5000000000000^6319 ≤ 2139010721193^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053256211 2000000000 2139010721193 5000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (443129217/2000000000 : ℝ)^8367 ≤ (6797446798819/50000000000000 : ℝ)^6319 := by
    have hnat : (443129217 : ℕ)^8367*50000000000000^6319 ≤ 6797446798819^6319*2000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      443129217 2000000000 6797446798819 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344621929/10000000000 : ℝ), (1053256211/2000000000 : ℝ), (-443129217/2000000000 : ℝ)] ![(43624891966127/100000000000000 : ℝ), (2139010721193/5000000000000 : ℝ), (6797446798819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344621929/10000000000 : ℝ)|^8367 ≤ (43624891966127/100000000000000 : ℝ)^6319
        have hw : |(5344621929/10000000000 : ℝ)|=(5344621929/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053256211/2000000000 : ℝ)|^8367 ≤ (2139010721193/5000000000000 : ℝ)^6319
        have hw : |(1053256211/2000000000 : ℝ)|=(1053256211/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-443129217/2000000000 : ℝ)|^8367 ≤ (6797446798819/50000000000000 : ℝ)^6319
        have hw : |(-443129217/2000000000 : ℝ)|=(443129217/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s8_3 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4360186471/10000000000 : ℝ)*x 0 + (33885893/80000000 : ℝ)*x 1 + (4488247201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4360186471/10000000000 : ℝ)^8367 ≤ (16658579585681/50000000000000 : ℝ)^6319 := by
    have hnat : (4360186471 : ℕ)^8367*50000000000000^6319 ≤ 16658579585681^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4360186471 10000000000 16658579585681 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33885893/80000000 : ℝ)^8367 ≤ (8015966887859/25000000000000 : ℝ)^6319 := by
    have hnat : (33885893 : ℕ)^8367*25000000000000^6319 ≤ 8015966887859^6319*80000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33885893 80000000 8015966887859 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488247201/10000000000 : ℝ)^8367 ≤ (34618973255507/100000000000000 : ℝ)^6319 := by
    have hnat : (4488247201 : ℕ)^8367*100000000000000^6319 ≤ 34618973255507^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488247201 10000000000 34618973255507 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4360186471/10000000000 : ℝ), (33885893/80000000 : ℝ), (4488247201/10000000000 : ℝ)] ![(16658579585681/50000000000000 : ℝ), (8015966887859/25000000000000 : ℝ), (34618973255507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4360186471/10000000000 : ℝ)|^8367 ≤ (16658579585681/50000000000000 : ℝ)^6319
        have hw : |(4360186471/10000000000 : ℝ)|=(4360186471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33885893/80000000 : ℝ)|^8367 ≤ (8015966887859/25000000000000 : ℝ)^6319
        have hw : |(33885893/80000000 : ℝ)|=(33885893/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488247201/10000000000 : ℝ)|^8367 ≤ (34618973255507/100000000000000 : ℝ)^6319
        have hw : |(4488247201/10000000000 : ℝ)|=(4488247201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s8_4 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151683403/10000000000 : ℝ)*x 0 + (5266597513/10000000000 : ℝ)*x 1 + (2696047303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151683403/10000000000 : ℝ)^8367 ≤ (3269418913549/25000000000000 : ℝ)^6319 := by
    have hnat : (2151683403 : ℕ)^8367*25000000000000^6319 ≤ 3269418913549^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151683403 10000000000 3269418913549 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266597513/10000000000 : ℝ)^8367 ≤ (42783618354057/100000000000000 : ℝ)^6319 := by
    have hnat : (5266597513 : ℕ)^8367*100000000000000^6319 ≤ 42783618354057^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266597513 10000000000 42783618354057 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696047303/5000000000 : ℝ)^8367 ≤ (44138705969387/100000000000000 : ℝ)^6319 := by
    have hnat : (2696047303 : ℕ)^8367*100000000000000^6319 ≤ 44138705969387^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696047303 5000000000 44138705969387 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151683403/10000000000 : ℝ), (5266597513/10000000000 : ℝ), (2696047303/5000000000 : ℝ)] ![(3269418913549/25000000000000 : ℝ), (42783618354057/100000000000000 : ℝ), (44138705969387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151683403/10000000000 : ℝ)|^8367 ≤ (3269418913549/25000000000000 : ℝ)^6319
        have hw : |(-2151683403/10000000000 : ℝ)|=(2151683403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266597513/10000000000 : ℝ)|^8367 ≤ (42783618354057/100000000000000 : ℝ)^6319
        have hw : |(5266597513/10000000000 : ℝ)|=(5266597513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696047303/5000000000 : ℝ)|^8367 ≤ (44138705969387/100000000000000 : ℝ)^6319
        have hw : |(2696047303/5000000000 : ℝ)|=(2696047303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s8_5 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (265629551/500000000 : ℝ)*x 0 + (-1044916907/5000000000 : ℝ)*x 1 + (1348023417/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265629551/500000000 : ℝ)^8367 ≤ (43279043786697/100000000000000 : ℝ)^6319 := by
    have hnat : (265629551 : ℕ)^8367*100000000000000^6319 ≤ 43279043786697^6319*500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265629551 500000000 43279043786697 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044916907/5000000000 : ℝ)^8367 ≤ (629113019659/5000000000000 : ℝ)^6319 := by
    have hnat : (1044916907 : ℕ)^8367*5000000000000^6319 ≤ 629113019659^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044916907 5000000000 629113019659 5000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348023417/2500000000 : ℝ)^8367 ≤ (44138695802539/100000000000000 : ℝ)^6319 := by
    have hnat : (1348023417 : ℕ)^8367*100000000000000^6319 ≤ 44138695802539^6319*2500000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348023417 2500000000 44138695802539 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265629551/500000000 : ℝ), (-1044916907/5000000000 : ℝ), (1348023417/2500000000 : ℝ)] ![(43279043786697/100000000000000 : ℝ), (629113019659/5000000000000 : ℝ), (44138695802539/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265629551/500000000 : ℝ)|^8367 ≤ (43279043786697/100000000000000 : ℝ)^6319
        have hw : |(265629551/500000000 : ℝ)|=(265629551/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1044916907/5000000000 : ℝ)|^8367 ≤ (629113019659/5000000000000 : ℝ)^6319
        have hw : |(-1044916907/5000000000 : ℝ)|=(1044916907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348023417/2500000000 : ℝ)|^8367 ≤ (44138695802539/100000000000000 : ℝ)^6319
        have hw : |(1348023417/2500000000 : ℝ)|=(1348023417/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s8_6 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312590799/10000000000 : ℝ)*x 0 + (2696047103/5000000000 : ℝ)*x 1 + (-1044916691/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312590799/10000000000 : ℝ)^8367 ≤ (21639520701407/50000000000000 : ℝ)^6319 := by
    have hnat : (5312590799 : ℕ)^8367*50000000000000^6319 ≤ 21639520701407^6319*10000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312590799 10000000000 21639520701407 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696047103/5000000000 : ℝ)^8367 ≤ (8827740326769/20000000000000 : ℝ)^6319 := by
    have hnat : (2696047103 : ℕ)^8367*20000000000000^6319 ≤ 8827740326769^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696047103 5000000000 8827740326769 20000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044916691/5000000000 : ℝ)^8367 ≤ (3145564237317/25000000000000 : ℝ)^6319 := by
    have hnat : (1044916691 : ℕ)^8367*25000000000000^6319 ≤ 3145564237317^6319*5000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044916691 5000000000 3145564237317 25000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312590799/10000000000 : ℝ), (2696047103/5000000000 : ℝ), (-1044916691/5000000000 : ℝ)] ![(21639520701407/50000000000000 : ℝ), (8827740326769/20000000000000 : ℝ), (3145564237317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312590799/10000000000 : ℝ)|^8367 ≤ (21639520701407/50000000000000 : ℝ)^6319
        have hw : |(5312590799/10000000000 : ℝ)|=(5312590799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696047103/5000000000 : ℝ)|^8367 ≤ (8827740326769/20000000000000 : ℝ)^6319
        have hw : |(2696047103/5000000000 : ℝ)|=(2696047103/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1044916691/5000000000 : ℝ)|^8367 ≤ (3145564237317/25000000000000 : ℝ)^6319
        have hw : |(-1044916691/5000000000 : ℝ)|=(1044916691/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1174_s8_7 (p : ℝ) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (545024549/1250000000 : ℝ)*x 0 + (448761231/1000000000 : ℝ)*x 1 + (8472747/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (545024549/1250000000 : ℝ)^8367 ≤ (16658629774841/50000000000000 : ℝ)^6319 := by
    have hnat : (545024549 : ℕ)^8367*50000000000000^6319 ≤ 16658629774841^6319*1250000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545024549 1250000000 16658629774841 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448761231/1000000000 : ℝ)^8367 ≤ (34612489180307/100000000000000 : ℝ)^6319 := by
    have hnat : (448761231 : ℕ)^8367*100000000000000^6319 ≤ 34612489180307^6319*1000000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448761231 1000000000 34612489180307 100000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8472747/20000000 : ℝ)^8367 ≤ (16035125630751/50000000000000 : ℝ)^6319 := by
    have hnat : (8472747 : ℕ)^8367*50000000000000^6319 ≤ 16035125630751^6319*20000000^8367 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8472747 20000000 16035125630751 50000000000000 8367 6319 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8367/2048 : ℝ)) 8367 6319 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(545024549/1250000000 : ℝ), (448761231/1000000000 : ℝ), (8472747/20000000 : ℝ)] ![(16658629774841/50000000000000 : ℝ), (34612489180307/100000000000000 : ℝ), (16035125630751/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(545024549/1250000000 : ℝ)|^8367 ≤ (16658629774841/50000000000000 : ℝ)^6319
        have hw : |(545024549/1250000000 : ℝ)|=(545024549/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(448761231/1000000000 : ℝ)|^8367 ≤ (34612489180307/100000000000000 : ℝ)^6319
        have hw : |(448761231/1000000000 : ℝ)|=(448761231/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(8472747/20000000 : ℝ)|^8367 ≤ (16035125630751/50000000000000 : ℝ)^6319
        have hw : |(8472747/20000000 : ℝ)|=(8472747/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1174_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2279/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14067/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5697/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5697/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5697/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5697/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5697/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5697/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5697/50000 : ℝ) ^ (4183/1024 : ℝ) ≤ (14013905589213817/100000000000000000000 : ℝ) := by
    have hpowers : (5697/50000 : ℝ)^4183 ≤ (14013905589213817/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5697 : ℕ)^4183*100000000000000000000^1024 ≤ 14013905589213817^1024*50000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5697 50000 14013905589213817 100000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5697/50000 : ℝ)) (X := (14013905589213817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3517/25000 : ℝ) ^ (4183/1024 : ℝ) ≤ (16578012610543541/50000000000000000000 : ℝ) := by
    have hpowers : (3517/25000 : ℝ)^4183 ≤ (16578012610543541/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3517 : ℕ)^4183*50000000000000000000^1024 ≤ 16578012610543541^1024*25000^4183 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3517 25000 16578012610543541 50000000000000000000 4183 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3517/25000 : ℝ)) (X := (16578012610543541/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014013905589213817/50000000000000000000 : ℝ) ≤ (10000686049287307/10000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (50014013905589213817/50000000000000000000 : ℝ)^1024 ≤ (10000686049287307/10000000000000000 : ℝ)^4183 := by
      have hnat : (50014013905589213817 : ℕ)^1024*10000000000000000^4183 ≤ 10000686049287307^4183*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014013905589213817 50000000000000000000 10000686049287307 10000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000686049287307/10000000000000000 : ℝ)) (X := (50014013905589213817/50000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047169930810300899/100000000000000000000 : ℝ) ≤ (10001154516095627/10000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (100047169930810300899/100000000000000000000 : ℝ)^1024 ≤ (10001154516095627/10000000000000000 : ℝ)^4183 := by
      have hnat : (100047169930810300899 : ℕ)^1024*10000000000000000^4183 ≤ 10001154516095627^4183*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047169930810300899 100000000000000000000 10001154516095627 10000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001154516095627/10000000000000000 : ℝ)) (X := (100047169930810300899/100000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016578012610543541/25000000000000000000 : ℝ) ≤ (10001622982903947/10000000000000000 : ℝ) ^ (4183/1024 : ℝ) := by
    have hpowers : (25016578012610543541/25000000000000000000 : ℝ)^1024 ≤ (10001622982903947/10000000000000000 : ℝ)^4183 := by
      have hnat : (25016578012610543541 : ℕ)^1024*10000000000000000^4183 ≤ 10001622982903947^4183*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016578012610543541 25000000000000000000 10001622982903947 10000000000000000 1024 4183 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001622982903947/10000000000000000 : ℝ)) (X := (25016578012610543541/25000000000000000000 : ℝ)) (by norm_num) 4183 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14013905589213817/100000000000000000000 : ℝ) ≤ ((1909368505297590197/1910000000000000000 : ℝ)+2*(26142121/14921875000 : ℝ)*(5697/50000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (1909368505297590197/1910000000000000000 : ℝ)+2*(26142121/14921875000 : ℝ)*(5697/50000 : ℝ)=(10000686049287307/10000000000000000 : ℝ) by norm_num, show 1+2*(14013905589213817/100000000000000000000 : ℝ)=(50014013905589213817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16578012610543541/50000000000000000000 : ℝ)+(14013905589213817/100000000000000000000 : ℝ) ≤ ((1909368505297590197/1910000000000000000 : ℝ)+(26142121/14921875000 : ℝ)*((3517/25000 : ℝ)+(5697/50000 : ℝ)))^(4183/1024 : ℝ) := by
    rw [show (1909368505297590197/1910000000000000000 : ℝ)+(26142121/14921875000 : ℝ)*((3517/25000 : ℝ)+(5697/50000 : ℝ))=(10001154516095627/10000000000000000 : ℝ) by norm_num, show 1+(16578012610543541/50000000000000000000 : ℝ)+(14013905589213817/100000000000000000000 : ℝ)=(100047169930810300899/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16578012610543541/50000000000000000000 : ℝ) ≤ ((1909368505297590197/1910000000000000000 : ℝ)+2*(26142121/14921875000 : ℝ)*(3517/25000 : ℝ))^(4183/1024 : ℝ) := by
    rw [show (1909368505297590197/1910000000000000000 : ℝ)+2*(26142121/14921875000 : ℝ)*(3517/25000 : ℝ)=(10001622982903947/10000000000000000 : ℝ) by norm_num, show 1+2*(16578012610543541/50000000000000000000 : ℝ)=(25016578012610543541/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1909368505297590197/1910000000000000000 : ℝ)*(X 1 0+X 2 0)+(26142121/14921875000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (5697/50000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (1909368505297590197/1910000000000000000 : ℝ)) (alpha := (26142121/14921875000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1909368505297590197/1910000000000000000 : ℝ)*(X 0 1+X 2 1)+(26142121/14921875000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (5697/50000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (1909368505297590197/1910000000000000000 : ℝ)) (alpha := (26142121/14921875000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1909368505297590197/1910000000000000000 : ℝ)*(X 0 2+X 1 2)+(26142121/14921875000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4183/1024 : ℝ)) (lo := (5697/50000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (1909368505297590197/1910000000000000000 : ℝ)) (alpha := (26142121/14921875000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-430335737/2000000000 : ℝ)*X 0 0+(539241217/1000000000 : ℝ)*X 0 1+(65828513/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344621941/10000000000 : ℝ)*X 1 0+(-88625843/400000000 : ℝ)*X 1 1+(105325621/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344621929/10000000000 : ℝ)*X 2 0+(1053256211/2000000000 : ℝ)*X 2 1+(-443129217/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4360186471/10000000000 : ℝ)*X 0 0+(33885893/80000000 : ℝ)*X 0 1+(4488247201/10000000000 : ℝ)*X 0 2+(4360186471/10000000000 : ℝ)*X 1 0+(33885893/80000000 : ℝ)*X 1 1+(4488247201/10000000000 : ℝ)*X 1 2+(4360186471/10000000000 : ℝ)*X 2 0+(33885893/80000000 : ℝ)*X 2 1+(4488247201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2151683403/10000000000 : ℝ)*X 0 0+(5266597513/10000000000 : ℝ)*X 0 1+(2696047303/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265629551/500000000 : ℝ)*X 1 0+(-1044916907/5000000000 : ℝ)*X 1 1+(1348023417/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312590799/10000000000 : ℝ)*X 2 0+(2696047103/5000000000 : ℝ)*X 2 1+(-1044916691/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((545024549/1250000000 : ℝ)*X 0 0+(448761231/1000000000 : ℝ)*X 0 1+(8472747/20000000 : ℝ)*X 0 2+(545024549/1250000000 : ℝ)*X 1 0+(448761231/1000000000 : ℝ)*X 1 1+(8472747/20000000 : ℝ)*X 1 2+(545024549/1250000000 : ℝ)*X 2 0+(448761231/1000000000 : ℝ)*X 2 1+(8472747/20000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1174_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (610399909718360547766660701/95500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1254367727/100000000000000 : ℝ)*(base19) + (1141889089/100000000000000 : ℝ)*(base23) + (12650397/25000000000000 : ℝ)*(lower2) + (173677251/100000000000000 : ℝ)*(upper3) + (84811489/100000000000000 : ℝ)*(upper5) + (5944296661226211/100000000000000 : ℝ)*(major0) + (5944296661226211/100000000000000 : ℝ)*(major1) + (1486074165306553/25000000000000 : ℝ)*(major2) + (7928293874995373/100000000000000 : ℝ)*(sp0) + (3964163320939803/50000000000000 : ℝ)*(sp1) + (1982081688589561/25000000000000 : ℝ)*(sp2) + (1980123266368561/50000000000000 : ℝ)*(sp3) + (34021251961/100000000000000 : ℝ)*(sp4) + (18680413889/100000000000000 : ℝ)*(sp7) + (3960265213151011/100000000000000 : ℝ)*(f.failure) + (7928327896247333/100000000000000 : ℝ)*(f.sum) + (267234111259/95500000000000000000000000 : ℝ)*base66 + (10934496563946433/191000000000000000000000000000000 : ℝ)*base68 + (542906406707660941/47750000000000000000000000000000 : ℝ)*base69 + (3552890248586946433/191000000000000000000000000000000 : ℝ)*base72 + (91674859533/95500000000000000000000000 : ℝ)*base74 + (138324507960839059/47750000000000000000000000000000 : ℝ)*base76 + (2696029249204946433/191000000000000000000000000000000 : ℝ)*base78 + (3031709953701053567/191000000000000000000000000000000 : ℝ)*base79 + (154632894037/95500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (53881939/10000000000000000000000 : ℝ)*base89 + (53881939/10000000000000000000000 : ℝ)*base91 + (46118061/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (253574119132024689531745407/23875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1178779947/100000000000000 : ℝ)*(base19) + (19537917/4000000000000 : ℝ)*(base23) + (28809761/12500000000000 : ℝ)*(lower2) + (6889973/12500000000000 : ℝ)*(upper3) + (39834003/100000000000000 : ℝ)*(lower4) + (441806821/100000000000000 : ℝ)*(upper5) + (2987161273658977/50000000000000 : ℝ)*(major0) + (2987161273658977/50000000000000 : ℝ)*(major1) + (2987161273658977/50000000000000 : ℝ)*(major2) + (20616428423/100000000000000 : ℝ)*(sp0) + (7968354782874529/100000000000000 : ℝ)*(sp4) + (3984187110261503/50000000000000 : ℝ)*(sp5) + (7968374910855027/100000000000000 : ℝ)*(sp6) + (3980269341302757/100000000000000 : ℝ)*(sp7) + (3980269341302757/100000000000000 : ℝ)*(f.failure) + (7968375399302953/100000000000000 : ℝ)*(f.sum) + (1438721594039/95500000000000000000000000 : ℝ)*base66 + (1196725841258748469/95500000000000000000000000000000 : ℝ)*base67 + (1992700745774751531/95500000000000000000000000000000 : ℝ)*base70 + (2088700102859751531/95500000000000000000000000000000 : ℝ)*base72 + (166028141011/95500000000000000000000000 : ℝ)*base74 + (2063679737361751531/95500000000000000000000000000000 : ℝ)*base76 + (1160830741121251531/95500000000000000000000000000000 : ℝ)*base78 + (527156049503751531/95500000000000000000000000000000 : ℝ)*base80 + (414157616211/95500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (65123893/10000000000000000000000 : ℝ)*base89 + (65123893/10000000000000000000000 : ℝ)*base91 + (65123893/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1174_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1174_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1174_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1174_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1174_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1174_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4183/1024 : ℝ) ≤ p) (hpb : p ≤ (8367/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150098449/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7051/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11361/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2279/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14067/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1174_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
