-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1198_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:02:15.928902+00:00
-- url     : https://prove2.me/submissions/775a039b-d889-44db-bdf7-2f9dfccd7a11

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
theorem support_rectangle_w1198_box_0 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-80612599/400000000 : ℝ)*x 0 + (5375498131/10000000000 : ℝ)*x 1 + (5375498033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80612599/400000000 : ℝ)^8391 ≤ (12015233942537/100000000000000 : ℝ)^6343 := by
    have hnat : (80612599 : ℕ)^8391*100000000000000^6343 ≤ 12015233942537^6343*400000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80612599 400000000 12015233942537 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5375498131/10000000000 : ℝ)^8391 ≤ (43992383556563/100000000000000 : ℝ)^6343 := by
    have hnat : (5375498131 : ℕ)^8391*100000000000000^6343 ≤ 43992383556563^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375498131 10000000000 43992383556563 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5375498033/10000000000 : ℝ)^8391 ≤ (43992382495591/100000000000000 : ℝ)^6343 := by
    have hnat : (5375498033 : ℕ)^8391*100000000000000^6343 ≤ 43992382495591^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375498033 10000000000 43992382495591 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-80612599/400000000 : ℝ), (5375498131/10000000000 : ℝ), (5375498033/10000000000 : ℝ)] ![(12015233942537/100000000000000 : ℝ), (43992383556563/100000000000000 : ℝ), (43992382495591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-80612599/400000000 : ℝ)|^8391 ≤ (12015233942537/100000000000000 : ℝ)^6343
        have hw : |(-80612599/400000000 : ℝ)|=(80612599/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5375498131/10000000000 : ℝ)|^8391 ≤ (43992383556563/100000000000000 : ℝ)^6343
        have hw : |(5375498131/10000000000 : ℝ)|=(5375498131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5375498033/10000000000 : ℝ)|^8391 ≤ (43992382495591/100000000000000 : ℝ)^6343
        have hw : |(5375498033/10000000000 : ℝ)|=(5375498033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_1 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1059293423/2000000000 : ℝ)*x 0 + (-1061314623/5000000000 : ℝ)*x 1 + (2687749033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059293423/2000000000 : ℝ)^8391 ≤ (21569406042127/50000000000000 : ℝ)^6343 := by
    have hnat : (1059293423 : ℕ)^8391*50000000000000^6343 ≤ 21569406042127^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059293423 2000000000 21569406042127 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061314623/5000000000 : ℝ)^8391 ≤ (3217201261621/25000000000000 : ℝ)^6343 := by
    have hnat : (1061314623 : ℕ)^8391*25000000000000^6343 ≤ 3217201261621^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061314623 5000000000 3217201261621 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687749033/5000000000 : ℝ)^8391 ≤ (43992382852857/100000000000000 : ℝ)^6343 := by
    have hnat : (2687749033 : ℕ)^8391*100000000000000^6343 ≤ 43992382852857^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687749033 5000000000 43992382852857 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059293423/2000000000 : ℝ), (-1061314623/5000000000 : ℝ), (2687749033/5000000000 : ℝ)] ![(21569406042127/50000000000000 : ℝ), (3217201261621/25000000000000 : ℝ), (43992382852857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059293423/2000000000 : ℝ)|^8391 ≤ (21569406042127/50000000000000 : ℝ)^6343
        have hw : |(1059293423/2000000000 : ℝ)|=(1059293423/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1061314623/5000000000 : ℝ)|^8391 ≤ (3217201261621/25000000000000 : ℝ)^6343
        have hw : |(-1061314623/5000000000 : ℝ)|=(1061314623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687749033/5000000000 : ℝ)|^8391 ≤ (43992382852857/100000000000000 : ℝ)^6343
        have hw : |(2687749033/5000000000 : ℝ)|=(2687749033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_2 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2648233441/5000000000 : ℝ)*x 0 + (2687749089/5000000000 : ℝ)*x 1 + (-2122629407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648233441/5000000000 : ℝ)^8391 ≤ (21569404786887/50000000000000 : ℝ)^6343 := by
    have hnat : (2648233441 : ℕ)^8391*50000000000000^6343 ≤ 21569404786887^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648233441 5000000000 21569404786887 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2687749089/5000000000 : ℝ)^8391 ≤ (10998096016349/25000000000000 : ℝ)^6343 := by
    have hnat : (2687749089 : ℕ)^8391*25000000000000^6343 ≤ 10998096016349^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687749089 5000000000 10998096016349 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2122629407/10000000000 : ℝ)^8391 ≤ (1286880633773/10000000000000 : ℝ)^6343 := by
    have hnat : (2122629407 : ℕ)^8391*10000000000000^6343 ≤ 1286880633773^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122629407 10000000000 1286880633773 10000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648233441/5000000000 : ℝ), (2687749089/5000000000 : ℝ), (-2122629407/10000000000 : ℝ)] ![(21569404786887/50000000000000 : ℝ), (10998096016349/25000000000000 : ℝ), (1286880633773/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648233441/5000000000 : ℝ)|^8391 ≤ (21569404786887/50000000000000 : ℝ)^6343
        have hw : |(2648233441/5000000000 : ℝ)|=(2648233441/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2687749089/5000000000 : ℝ)|^8391 ≤ (10998096016349/25000000000000 : ℝ)^6343
        have hw : |(2687749089/5000000000 : ℝ)|=(2687749089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2122629407/10000000000 : ℝ)|^8391 ≤ (1286880633773/10000000000000 : ℝ)^6343
        have hw : |(-2122629407/10000000000 : ℝ)|=(2122629407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_3 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2231904643/5000000000 : ℝ)*x 0 + (4305433613/10000000000 : ℝ)*x 1 + (861086747/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2231904643/5000000000 : ℝ)^8391 ≤ (17201809245017/50000000000000 : ℝ)^6343 := by
    have hnat : (2231904643 : ℕ)^8391*50000000000000^6343 ≤ 17201809245017^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2231904643 5000000000 17201809245017 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4305433613/10000000000 : ℝ)^8391 ≤ (32798190130711/100000000000000 : ℝ)^6343 := by
    have hnat : (4305433613 : ℕ)^8391*100000000000000^6343 ≤ 32798190130711^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4305433613 10000000000 32798190130711 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (861086747/2000000000 : ℝ)^8391 ≤ (8199547840041/25000000000000 : ℝ)^6343 := by
    have hnat : (861086747 : ℕ)^8391*25000000000000^6343 ≤ 8199547840041^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      861086747 2000000000 8199547840041 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2231904643/5000000000 : ℝ), (4305433613/10000000000 : ℝ), (861086747/2000000000 : ℝ)] ![(17201809245017/50000000000000 : ℝ), (32798190130711/100000000000000 : ℝ), (8199547840041/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2231904643/5000000000 : ℝ)|^8391 ≤ (17201809245017/50000000000000 : ℝ)^6343
        have hw : |(2231904643/5000000000 : ℝ)|=(2231904643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4305433613/10000000000 : ℝ)|^8391 ≤ (32798190130711/100000000000000 : ℝ)^6343
        have hw : |(4305433613/10000000000 : ℝ)|=(4305433613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(861086747/2000000000 : ℝ)|^8391 ≤ (8199547840041/25000000000000 : ℝ)^6343
        have hw : |(861086747/2000000000 : ℝ)|=(861086747/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_4 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2266855557/10000000000 : ℝ)*x 0 + (330113301/625000000 : ℝ)*x 1 + (528181287/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2266855557/10000000000 : ℝ)^8391 ≤ (877376396019/6250000000000 : ℝ)^6343 := by
    have hnat : (2266855557 : ℕ)^8391*6250000000000^6343 ≤ 877376396019^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2266855557 10000000000 877376396019 6250000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (330113301/625000000 : ℝ)^8391 ≤ (10745247133379/25000000000000 : ℝ)^6343 := by
    have hnat : (330113301 : ℕ)^8391*25000000000000^6343 ≤ 10745247133379^6343*625000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330113301 625000000 10745247133379 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (528181287/1000000000 : ℝ)^8391 ≤ (5372623639353/12500000000000 : ℝ)^6343 := by
    have hnat : (528181287 : ℕ)^8391*12500000000000^6343 ≤ 5372623639353^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528181287 1000000000 5372623639353 12500000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2266855557/10000000000 : ℝ), (330113301/625000000 : ℝ), (528181287/1000000000 : ℝ)] ![(877376396019/6250000000000 : ℝ), (10745247133379/25000000000000 : ℝ), (5372623639353/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2266855557/10000000000 : ℝ)|^8391 ≤ (877376396019/6250000000000 : ℝ)^6343
        have hw : |(-2266855557/10000000000 : ℝ)|=(2266855557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(330113301/625000000 : ℝ)|^8391 ≤ (10745247133379/25000000000000 : ℝ)^6343
        have hw : |(330113301/625000000 : ℝ)|=(330113301/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(528181287/1000000000 : ℝ)|^8391 ≤ (5372623639353/12500000000000 : ℝ)^6343
        have hw : |(528181287/1000000000 : ℝ)|=(528181287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_5 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (167580381/312500000 : ℝ)*x 0 + (-1079822729/5000000000 : ℝ)*x 1 + (1320453189/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167580381/312500000 : ℝ)^8391 ≤ (2192624927381/5000000000000 : ℝ)^6343 := by
    have hnat : (167580381 : ℕ)^8391*5000000000000^6343 ≤ 2192624927381^6343*312500000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167580381 312500000 2192624927381 5000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079822729/5000000000 : ℝ)^8391 ≤ (13166513552993/100000000000000 : ℝ)^6343 := by
    have hnat : (1079822729 : ℕ)^8391*100000000000000^6343 ≤ 13166513552993^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079822729 5000000000 13166513552993 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1320453189/2500000000 : ℝ)^8391 ≤ (42980987887619/100000000000000 : ℝ)^6343 := by
    have hnat : (1320453189 : ℕ)^8391*100000000000000^6343 ≤ 42980987887619^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1320453189 2500000000 42980987887619 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167580381/312500000 : ℝ), (-1079822729/5000000000 : ℝ), (1320453189/2500000000 : ℝ)] ![(2192624927381/5000000000000 : ℝ), (13166513552993/100000000000000 : ℝ), (42980987887619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167580381/312500000 : ℝ)|^8391 ≤ (2192624927381/5000000000000 : ℝ)^6343
        have hw : |(167580381/312500000 : ℝ)|=(167580381/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1079822729/5000000000 : ℝ)|^8391 ≤ (13166513552993/100000000000000 : ℝ)^6343
        have hw : |(-1079822729/5000000000 : ℝ)|=(1079822729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1320453189/2500000000 : ℝ)|^8391 ≤ (42980987887619/100000000000000 : ℝ)^6343
        have hw : |(1320453189/2500000000 : ℝ)|=(1320453189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_6 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1340643199/2500000000 : ℝ)*x 0 + (1056362567/2000000000 : ℝ)*x 1 + (-1079822271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1340643199/2500000000 : ℝ)^8391 ≤ (43852505081591/100000000000000 : ℝ)^6343 := by
    have hnat : (1340643199 : ℕ)^8391*100000000000000^6343 ≤ 43852505081591^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1340643199 2500000000 43852505081591 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056362567/2000000000 : ℝ)^8391 ≤ (859619774761/2000000000000 : ℝ)^6343 := by
    have hnat : (1056362567 : ℕ)^8391*2000000000000^6343 ≤ 859619774761^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056362567 2000000000 859619774761 2000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079822271/5000000000 : ℝ)^8391 ≤ (13166506165403/100000000000000 : ℝ)^6343 := by
    have hnat : (1079822271 : ℕ)^8391*100000000000000^6343 ≤ 13166506165403^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079822271 5000000000 13166506165403 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1340643199/2500000000 : ℝ), (1056362567/2000000000 : ℝ), (-1079822271/5000000000 : ℝ)] ![(43852505081591/100000000000000 : ℝ), (859619774761/2000000000000 : ℝ), (13166506165403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1340643199/2500000000 : ℝ)|^8391 ≤ (43852505081591/100000000000000 : ℝ)^6343
        have hw : |(1340643199/2500000000 : ℝ)|=(1340643199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056362567/2000000000 : ℝ)|^8391 ≤ (859619774761/2000000000000 : ℝ)^6343
        have hw : |(1056362567/2000000000 : ℝ)|=(1056362567/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1079822271/5000000000 : ℝ)|^8391 ≤ (13166506165403/100000000000000 : ℝ)^6343
        have hw : |(-1079822271/5000000000 : ℝ)|=(1079822271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_7 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4249496649/10000000000 : ℝ)*x 0 + (4412570259/10000000000 : ℝ)*x 1 + (4412568891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4249496649/10000000000 : ℝ)^8391 ≤ (32235672248471/100000000000000 : ℝ)^6343 := by
    have hnat : (4249496649 : ℕ)^8391*100000000000000^6343 ≤ 32235672248471^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249496649 10000000000 32235672248471 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4412570259/10000000000 : ℝ)^8391 ≤ (16941085407319/50000000000000 : ℝ)^6343 := by
    have hnat : (4412570259 : ℕ)^8391*50000000000000^6343 ≤ 16941085407319^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412570259 10000000000 16941085407319 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4412568891/10000000000 : ℝ)^8391 ≤ (16941078459401/50000000000000 : ℝ)^6343 := by
    have hnat : (4412568891 : ℕ)^8391*50000000000000^6343 ≤ 16941078459401^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4412568891 10000000000 16941078459401 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4249496649/10000000000 : ℝ), (4412570259/10000000000 : ℝ), (4412568891/10000000000 : ℝ)] ![(32235672248471/100000000000000 : ℝ), (16941085407319/50000000000000 : ℝ), (16941078459401/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4249496649/10000000000 : ℝ)|^8391 ≤ (32235672248471/100000000000000 : ℝ)^6343
        have hw : |(4249496649/10000000000 : ℝ)|=(4249496649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4412570259/10000000000 : ℝ)|^8391 ≤ (16941085407319/50000000000000 : ℝ)^6343
        have hw : |(4412570259/10000000000 : ℝ)|=(4412570259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4412568891/10000000000 : ℝ)|^8391 ≤ (16941078459401/50000000000000 : ℝ)^6343
        have hw : |(4412568891/10000000000 : ℝ)|=(4412568891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_8 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-553548097/2500000000 : ℝ)*x 0 + (1304497969/2500000000 : ℝ)*x 1 + (1346277551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (553548097/2500000000 : ℝ)^8391 ≤ (850513826091/6250000000000 : ℝ)^6343 := by
    have hnat : (553548097 : ℕ)^8391*6250000000000^6343 ≤ 850513826091^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553548097 2500000000 850513826091 6250000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304497969/2500000000 : ℝ)^8391 ≤ (845906050827/2000000000000 : ℝ)^6343 := by
    have hnat : (1304497969 : ℕ)^8391*2000000000000^6343 ≤ 845906050827^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304497969 2500000000 845906050827 2000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1346277551/2500000000 : ℝ)^8391 ≤ (22048238113209/50000000000000 : ℝ)^6343 := by
    have hnat : (1346277551 : ℕ)^8391*50000000000000^6343 ≤ 22048238113209^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346277551 2500000000 22048238113209 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-553548097/2500000000 : ℝ), (1304497969/2500000000 : ℝ), (1346277551/2500000000 : ℝ)] ![(850513826091/6250000000000 : ℝ), (845906050827/2000000000000 : ℝ), (22048238113209/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-553548097/2500000000 : ℝ)|^8391 ≤ (850513826091/6250000000000 : ℝ)^6343
        have hw : |(-553548097/2500000000 : ℝ)|=(553548097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304497969/2500000000 : ℝ)|^8391 ≤ (845906050827/2000000000000 : ℝ)^6343
        have hw : |(1304497969/2500000000 : ℝ)|=(1304497969/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1346277551/2500000000 : ℝ)|^8391 ≤ (22048238113209/50000000000000 : ℝ)^6343
        have hw : |(1346277551/2500000000 : ℝ)|=(1346277551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_9 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289681307/10000000000 : ℝ)*x 0 + (-2118763603/10000000000 : ℝ)*x 1 + (1077022037/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289681307/10000000000 : ℝ)^8391 ≤ (43065712885471/100000000000000 : ℝ)^6343 := by
    have hnat : (5289681307 : ℕ)^8391*100000000000000^6343 ≤ 43065712885471^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289681307 10000000000 43065712885471 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2118763603/10000000000 : ℝ)^8391 ≤ (12837811085951/100000000000000 : ℝ)^6343 := by
    have hnat : (2118763603 : ℕ)^8391*100000000000000^6343 ≤ 12837811085951^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118763603 10000000000 12837811085951 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1077022037/2000000000 : ℝ)^8391 ≤ (44096476020601/100000000000000 : ℝ)^6343 := by
    have hnat : (1077022037 : ℕ)^8391*100000000000000^6343 ≤ 44096476020601^6343*2000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077022037 2000000000 44096476020601 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289681307/10000000000 : ℝ), (-2118763603/10000000000 : ℝ), (1077022037/2000000000 : ℝ)] ![(43065712885471/100000000000000 : ℝ), (12837811085951/100000000000000 : ℝ), (44096476020601/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289681307/10000000000 : ℝ)|^8391 ≤ (43065712885471/100000000000000 : ℝ)^6343
        have hw : |(5289681307/10000000000 : ℝ)|=(5289681307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2118763603/10000000000 : ℝ)|^8391 ≤ (12837811085951/100000000000000 : ℝ)^6343
        have hw : |(-2118763603/10000000000 : ℝ)|=(2118763603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1077022037/2000000000 : ℝ)|^8391 ≤ (44096476020601/100000000000000 : ℝ)^6343
        have hw : |(1077022037/2000000000 : ℝ)|=(1077022037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_10 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (528968137/1000000000 : ℝ)*x 0 + (5385110191/10000000000 : ℝ)*x 1 + (-211876351/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528968137/1000000000 : ℝ)^8391 ≤ (43065713563989/100000000000000 : ℝ)^6343 := by
    have hnat : (528968137 : ℕ)^8391*100000000000000^6343 ≤ 43065713563989^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528968137 1000000000 43065713563989 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385110191/10000000000 : ℝ)^8391 ≤ (11024119021399/25000000000000 : ℝ)^6343 := by
    have hnat : (5385110191 : ℕ)^8391*25000000000000^6343 ≤ 11024119021399^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385110191 10000000000 11024119021399 25000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (211876351/1000000000 : ℝ)^8391 ≤ (2567562068103/20000000000000 : ℝ)^6343 := by
    have hnat : (211876351 : ℕ)^8391*20000000000000^6343 ≤ 2567562068103^6343*1000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211876351 1000000000 2567562068103 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528968137/1000000000 : ℝ), (5385110191/10000000000 : ℝ), (-211876351/1000000000 : ℝ)] ![(43065713563989/100000000000000 : ℝ), (11024119021399/25000000000000 : ℝ), (2567562068103/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528968137/1000000000 : ℝ)|^8391 ≤ (43065713563989/100000000000000 : ℝ)^6343
        have hw : |(528968137/1000000000 : ℝ)|=(528968137/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385110191/10000000000 : ℝ)|^8391 ≤ (11024119021399/25000000000000 : ℝ)^6343
        have hw : |(5385110191/10000000000 : ℝ)|=(5385110191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-211876351/1000000000 : ℝ)|^8391 ≤ (2567562068103/20000000000000 : ℝ)^6343
        have hw : |(-211876351/1000000000 : ℝ)|=(211876351/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_11 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4485524771/10000000000 : ℝ)*x 0 + (536804417/1250000000 : ℝ)*x 1 + (536804431/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4485524771/10000000000 : ℝ)^8391 ≤ (17312598491781/50000000000000 : ℝ)^6343 := by
    have hnat : (4485524771 : ℕ)^8391*50000000000000^6343 ≤ 17312598491781^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4485524771 10000000000 17312598491781 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (536804417/1250000000 : ℝ)^8391 ≤ (16343700468183/50000000000000 : ℝ)^6343 := by
    have hnat : (536804417 : ℕ)^8391*50000000000000^6343 ≤ 16343700468183^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536804417 1250000000 16343700468183 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536804431/1250000000 : ℝ)^8391 ≤ (32687402064113/100000000000000 : ℝ)^6343 := by
    have hnat : (536804431 : ℕ)^8391*100000000000000^6343 ≤ 32687402064113^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536804431 1250000000 32687402064113 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4485524771/10000000000 : ℝ), (536804417/1250000000 : ℝ), (536804431/1250000000 : ℝ)] ![(17312598491781/50000000000000 : ℝ), (16343700468183/50000000000000 : ℝ), (32687402064113/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4485524771/10000000000 : ℝ)|^8391 ≤ (17312598491781/50000000000000 : ℝ)^6343
        have hw : |(4485524771/10000000000 : ℝ)|=(4485524771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(536804417/1250000000 : ℝ)|^8391 ≤ (16343700468183/50000000000000 : ℝ)^6343
        have hw : |(536804417/1250000000 : ℝ)|=(536804417/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(536804431/1250000000 : ℝ)|^8391 ≤ (32687402064113/100000000000000 : ℝ)^6343
        have hw : |(536804431/1250000000 : ℝ)|=(536804431/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_12 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-103413169/500000000 : ℝ)*x 0 + (679760083/1250000000 : ℝ)*x 1 + (329609393/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103413169/500000000 : ℝ)^8391 ≤ (12434595463001/100000000000000 : ℝ)^6343 := by
    have hnat : (103413169 : ℕ)^8391*100000000000000^6343 ≤ 12434595463001^6343*500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103413169 500000000 12434595463001 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679760083/1250000000 : ℝ)^8391 ≤ (44671187379573/100000000000000 : ℝ)^6343 := by
    have hnat : (679760083 : ℕ)^8391*100000000000000^6343 ≤ 44671187379573^6343*1250000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679760083 1250000000 44671187379573 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (329609393/625000000 : ℝ)^8391 ≤ (21447108570607/50000000000000 : ℝ)^6343 := by
    have hnat : (329609393 : ℕ)^8391*50000000000000^6343 ≤ 21447108570607^6343*625000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      329609393 625000000 21447108570607 50000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103413169/500000000 : ℝ), (679760083/1250000000 : ℝ), (329609393/625000000 : ℝ)] ![(12434595463001/100000000000000 : ℝ), (44671187379573/100000000000000 : ℝ), (21447108570607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103413169/500000000 : ℝ)|^8391 ≤ (12434595463001/100000000000000 : ℝ)^6343
        have hw : |(-103413169/500000000 : ℝ)|=(103413169/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679760083/1250000000 : ℝ)|^8391 ≤ (44671187379573/100000000000000 : ℝ)^6343
        have hw : |(679760083/1250000000 : ℝ)|=(679760083/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(329609393/625000000 : ℝ)|^8391 ≤ (21447108570607/50000000000000 : ℝ)^6343
        have hw : |(329609393/625000000 : ℝ)|=(329609393/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_13 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5368259797/10000000000 : ℝ)*x 0 + (-1081386777/5000000000 : ℝ)*x 1 + (1318437537/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368259797/10000000000 : ℝ)^8391 ≤ (43914036630877/100000000000000 : ℝ)^6343 := by
    have hnat : (5368259797 : ℕ)^8391*100000000000000^6343 ≤ 43914036630877^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368259797 10000000000 43914036630877 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1081386777/5000000000 : ℝ)^8391 ≤ (1319174771689/10000000000000 : ℝ)^6343 := by
    have hnat : (1081386777 : ℕ)^8391*10000000000000^6343 ≤ 1319174771689^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081386777 5000000000 1319174771689 10000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1318437537/2500000000 : ℝ)^8391 ≤ (42894215634863/100000000000000 : ℝ)^6343 := by
    have hnat : (1318437537 : ℕ)^8391*100000000000000^6343 ≤ 42894215634863^6343*2500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318437537 2500000000 42894215634863 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368259797/10000000000 : ℝ), (-1081386777/5000000000 : ℝ), (1318437537/2500000000 : ℝ)] ![(43914036630877/100000000000000 : ℝ), (1319174771689/10000000000000 : ℝ), (42894215634863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368259797/10000000000 : ℝ)|^8391 ≤ (43914036630877/100000000000000 : ℝ)^6343
        have hw : |(5368259797/10000000000 : ℝ)|=(5368259797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1081386777/5000000000 : ℝ)|^8391 ≤ (1319174771689/10000000000000 : ℝ)^6343
        have hw : |(-1081386777/5000000000 : ℝ)|=(1081386777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1318437537/2500000000 : ℝ)|^8391 ≤ (42894215634863/100000000000000 : ℝ)^6343
        have hw : |(1318437537/2500000000 : ℝ)|=(1318437537/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_14 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2684129931/5000000000 : ℝ)*x 0 + (2636875047/5000000000 : ℝ)*x 1 + (-108138677/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684129931/5000000000 : ℝ)^8391 ≤ (43914037334277/100000000000000 : ℝ)^6343 := by
    have hnat : (2684129931 : ℕ)^8391*100000000000000^6343 ≤ 43914037334277^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684129931 5000000000 43914037334277 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2636875047/5000000000 : ℝ)^8391 ≤ (42894215053841/100000000000000 : ℝ)^6343 := by
    have hnat : (2636875047 : ℕ)^8391*100000000000000^6343 ≤ 42894215053841^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2636875047 5000000000 42894215053841 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108138677/500000000 : ℝ)^8391 ≤ (13191747603927/100000000000000 : ℝ)^6343 := by
    have hnat : (108138677 : ℕ)^8391*100000000000000^6343 ≤ 13191747603927^6343*500000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108138677 500000000 13191747603927 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684129931/5000000000 : ℝ), (2636875047/5000000000 : ℝ), (-108138677/500000000 : ℝ)] ![(43914037334277/100000000000000 : ℝ), (42894215053841/100000000000000 : ℝ), (13191747603927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684129931/5000000000 : ℝ)|^8391 ≤ (43914037334277/100000000000000 : ℝ)^6343
        have hw : |(2684129931/5000000000 : ℝ)|=(2684129931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2636875047/5000000000 : ℝ)|^8391 ≤ (42894215053841/100000000000000 : ℝ)^6343
        have hw : |(2636875047/5000000000 : ℝ)|=(2636875047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-108138677/500000000 : ℝ)|^8391 ≤ (13191747603927/100000000000000 : ℝ)^6343
        have hw : |(-108138677/500000000 : ℝ)|=(108138677/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1198_box_15 (p : ℝ) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4230821271/10000000000 : ℝ)*x 0 + (2210892419/5000000000 : ℝ)*x 1 + (4421784689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4230821271/10000000000 : ℝ)^8391 ≤ (6409679509341/20000000000000 : ℝ)^6343 := by
    have hnat : (4230821271 : ℕ)^8391*20000000000000^6343 ≤ 6409679509341^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4230821271 10000000000 6409679509341 20000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210892419/5000000000 : ℝ)^8391 ≤ (33975801977861/100000000000000 : ℝ)^6343 := by
    have hnat : (2210892419 : ℕ)^8391*100000000000000^6343 ≤ 33975801977861^6343*5000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210892419 5000000000 33975801977861 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4421784689/10000000000 : ℝ)^8391 ≤ (33975800463333/100000000000000 : ℝ)^6343 := by
    have hnat : (4421784689 : ℕ)^8391*100000000000000^6343 ≤ 33975800463333^6343*10000000000^8391 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4421784689 10000000000 33975800463333 100000000000000 8391 6343 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8391/2048 : ℝ)) 8391 6343 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4230821271/10000000000 : ℝ), (2210892419/5000000000 : ℝ), (4421784689/10000000000 : ℝ)] ![(6409679509341/20000000000000 : ℝ), (33975801977861/100000000000000 : ℝ), (33975800463333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4230821271/10000000000 : ℝ)|^8391 ≤ (6409679509341/20000000000000 : ℝ)^6343
        have hw : |(4230821271/10000000000 : ℝ)|=(4230821271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2210892419/5000000000 : ℝ)|^8391 ≤ (33975801977861/100000000000000 : ℝ)^6343
        have hw : |(2210892419/5000000000 : ℝ)|=(2210892419/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4421784689/10000000000 : ℝ)|^8391 ≤ (33975800463333/100000000000000 : ℝ)^6343
        have hw : |(4421784689/10000000000 : ℝ)|=(4421784689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1198_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h) :
    -(62239/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29671/50000 : ℝ) ∧ (39989/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83249/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (457/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (88/625 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (457/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (457/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (88/625 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (457/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (457/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (88/625 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (457/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (457/4000 : ℝ) ^ (4195/1024 : ℝ) ≤ (3453652808411729/25000000000000000000 : ℝ) := by
    have hpowers : (457/4000 : ℝ)^4195 ≤ (3453652808411729/25000000000000000000 : ℝ)^1024 := by
      have hnat : (457 : ℕ)^4195*25000000000000000000^1024 ≤ 3453652808411729^1024*4000^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        457 4000 3453652808411729 25000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (457/4000 : ℝ)) (X := (3453652808411729/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (88/625 : ℝ) ^ (4195/1024 : ℝ) ≤ (16258025271617359/50000000000000000000 : ℝ) := by
    have hpowers : (88/625 : ℝ)^4195 ≤ (16258025271617359/50000000000000000000 : ℝ)^1024 := by
      have hnat : (88 : ℕ)^4195*50000000000000000000^1024 ≤ 16258025271617359^1024*625^4195 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        88 625 16258025271617359 50000000000000000000 4195 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (88/625 : ℝ)) (X := (16258025271617359/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503453652808411729/12500000000000000000 : ℝ) ≤ (10000674359234059/10000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (12503453652808411729/12500000000000000000 : ℝ)^1024 ≤ (10000674359234059/10000000000000000 : ℝ)^4195 := by
      have hnat : (12503453652808411729 : ℕ)^1024*10000000000000000^4195 ≤ 10000674359234059^4195*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503453652808411729 12500000000000000000 10000674359234059 10000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000674359234059/10000000000000000 : ℝ)) (X := (12503453652808411729/12500000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023165330888440817/50000000000000000000 : ℝ) ≤ (1000113073402609/1000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (50023165330888440817/50000000000000000000 : ℝ)^1024 ≤ (1000113073402609/1000000000000000 : ℝ)^4195 := by
      have hnat : (50023165330888440817 : ℕ)^1024*1000000000000000^4195 ≤ 1000113073402609^4195*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023165330888440817 50000000000000000000 1000113073402609 1000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000113073402609/1000000000000000 : ℝ)) (X := (50023165330888440817/50000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016258025271617359/25000000000000000000 : ℝ) ≤ (10001587108818121/10000000000000000 : ℝ) ^ (4195/1024 : ℝ) := by
    have hpowers : (25016258025271617359/25000000000000000000 : ℝ)^1024 ≤ (10001587108818121/10000000000000000 : ℝ)^4195 := by
      have hnat : (25016258025271617359 : ℕ)^1024*10000000000000000^4195 ≤ 10001587108818121^4195*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016258025271617359 25000000000000000000 10001587108818121 10000000000000000 1024 4195 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001587108818121/10000000000000000 : ℝ)) (X := (25016258025271617359/25000000000000000000 : ℝ)) (by norm_num) 4195 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3453652808411729/25000000000000000000 : ℝ) ≤ ((1769424150651234553/1770000000000000000 : ℝ)+2*(152124930677/88500000000000 : ℝ)*(457/4000 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (1769424150651234553/1770000000000000000 : ℝ)+2*(152124930677/88500000000000 : ℝ)*(457/4000 : ℝ)=(10000674359234059/10000000000000000 : ℝ) by norm_num, show 1+2*(3453652808411729/25000000000000000000 : ℝ)=(12503453652808411729/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16258025271617359/50000000000000000000 : ℝ)+(3453652808411729/25000000000000000000 : ℝ) ≤ ((1769424150651234553/1770000000000000000 : ℝ)+(152124930677/88500000000000 : ℝ)*((88/625 : ℝ)+(457/4000 : ℝ)))^(4195/1024 : ℝ) := by
    rw [show (1769424150651234553/1770000000000000000 : ℝ)+(152124930677/88500000000000 : ℝ)*((88/625 : ℝ)+(457/4000 : ℝ))=(1000113073402609/1000000000000000 : ℝ) by norm_num, show 1+(16258025271617359/50000000000000000000 : ℝ)+(3453652808411729/25000000000000000000 : ℝ)=(50023165330888440817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16258025271617359/50000000000000000000 : ℝ) ≤ ((1769424150651234553/1770000000000000000 : ℝ)+2*(152124930677/88500000000000 : ℝ)*(88/625 : ℝ))^(4195/1024 : ℝ) := by
    rw [show (1769424150651234553/1770000000000000000 : ℝ)+2*(152124930677/88500000000000 : ℝ)*(88/625 : ℝ)=(10001587108818121/10000000000000000 : ℝ) by norm_num, show 1+2*(16258025271617359/50000000000000000000 : ℝ)=(25016258025271617359/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1769424150651234553/1770000000000000000 : ℝ)*(X 1 0+X 2 0)+(152124930677/88500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (457/4000 : ℝ)) (hi := (88/625 : ℝ)) (c := (1769424150651234553/1770000000000000000 : ℝ)) (alpha := (152124930677/88500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1769424150651234553/1770000000000000000 : ℝ)*(X 0 1+X 2 1)+(152124930677/88500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (457/4000 : ℝ)) (hi := (88/625 : ℝ)) (c := (1769424150651234553/1770000000000000000 : ℝ)) (alpha := (152124930677/88500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1769424150651234553/1770000000000000000 : ℝ)*(X 0 2+X 1 2)+(152124930677/88500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4195/1024 : ℝ)) (lo := (457/4000 : ℝ)) (hi := (88/625 : ℝ)) (c := (1769424150651234553/1770000000000000000 : ℝ)) (alpha := (152124930677/88500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-80612599/400000000 : ℝ)*X 0 0+(5375498131/10000000000 : ℝ)*X 0 1+(5375498033/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1059293423/2000000000 : ℝ)*X 1 0+(-1061314623/5000000000 : ℝ)*X 1 1+(2687749033/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2648233441/5000000000 : ℝ)*X 2 0+(2687749089/5000000000 : ℝ)*X 2 1+(-2122629407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2231904643/5000000000 : ℝ)*X 0 0+(4305433613/10000000000 : ℝ)*X 0 1+(861086747/2000000000 : ℝ)*X 0 2+(2231904643/5000000000 : ℝ)*X 1 0+(4305433613/10000000000 : ℝ)*X 1 1+(861086747/2000000000 : ℝ)*X 1 2+(2231904643/5000000000 : ℝ)*X 2 0+(4305433613/10000000000 : ℝ)*X 2 1+(861086747/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2266855557/10000000000 : ℝ)*X 0 0+(330113301/625000000 : ℝ)*X 0 1+(528181287/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((167580381/312500000 : ℝ)*X 1 0+(-1079822729/5000000000 : ℝ)*X 1 1+(1320453189/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1340643199/2500000000 : ℝ)*X 2 0+(1056362567/2000000000 : ℝ)*X 2 1+(-1079822271/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4249496649/10000000000 : ℝ)*X 0 0+(4412570259/10000000000 : ℝ)*X 0 1+(4412568891/10000000000 : ℝ)*X 0 2+(4249496649/10000000000 : ℝ)*X 1 0+(4412570259/10000000000 : ℝ)*X 1 1+(4412568891/10000000000 : ℝ)*X 1 2+(4249496649/10000000000 : ℝ)*X 2 0+(4412570259/10000000000 : ℝ)*X 2 1+(4412568891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-553548097/2500000000 : ℝ)*X 0 0+(1304497969/2500000000 : ℝ)*X 0 1+(1346277551/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5289681307/10000000000 : ℝ)*X 1 0+(-2118763603/10000000000 : ℝ)*X 1 1+(1077022037/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((528968137/1000000000 : ℝ)*X 2 0+(5385110191/10000000000 : ℝ)*X 2 1+(-211876351/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4485524771/10000000000 : ℝ)*X 0 0+(536804417/1250000000 : ℝ)*X 0 1+(536804431/1250000000 : ℝ)*X 0 2+(4485524771/10000000000 : ℝ)*X 1 0+(536804417/1250000000 : ℝ)*X 1 1+(536804431/1250000000 : ℝ)*X 1 2+(4485524771/10000000000 : ℝ)*X 2 0+(536804417/1250000000 : ℝ)*X 2 1+(536804431/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-103413169/500000000 : ℝ)*X 0 0+(679760083/1250000000 : ℝ)*X 0 1+(329609393/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5368259797/10000000000 : ℝ)*X 1 0+(-1081386777/5000000000 : ℝ)*X 1 1+(1318437537/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2684129931/5000000000 : ℝ)*X 2 0+(2636875047/5000000000 : ℝ)*X 2 1+(-108138677/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4230821271/10000000000 : ℝ)*X 0 0+(2210892419/5000000000 : ℝ)*X 0 1+(4421784689/10000000000 : ℝ)*X 0 2+(4230821271/10000000000 : ℝ)*X 1 0+(2210892419/5000000000 : ℝ)*X 1 1+(4421784689/10000000000 : ℝ)*X 1 2+(4230821271/10000000000 : ℝ)*X 2 0+(2210892419/5000000000 : ℝ)*X 2 1+(4421784689/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1198_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62239/100000 : ℝ) ≤ (-18359743002583644435971884889789/29500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (537551/390625000000 : ℝ)*(upper1) + (577651877/100000000000000 : ℝ)*(upper4) + (121655081/100000000000000 : ℝ)*(upper5) + (3966977065250071/100000000000000 : ℝ)*(major0) + (3966977065250071/100000000000000 : ℝ)*(major1) + (3966977065250071/100000000000000 : ℝ)*(major2) + (28191830133/100000000000000 : ℝ)*(sp1) + (960564459/20000000000000 : ℝ)*(sp3) + (212799325800893/4000000000000 : ℝ)*(sp4) + (2659993986262559/50000000000000 : ℝ)*(sp5) + (5319893147336169/100000000000000 : ℝ)*(sp6) + (1317339317820947/50000000000000 : ℝ)*(sp7) + (16509666463/50000000000000 : ℝ)*(sp8) + (61508509541/50000000000000 : ℝ)*(sp14) + (2634683438464189/100000000000000 : ℝ)*(f.failure) + (5320016164355251/100000000000000 : ℝ)*(f.sum) + (78439797323/1106250000000000000000000000 : ℝ)*base65 + (1694092518393243263/177000000000000000000000000000000 : ℝ)*base67 + (699019355541243263/177000000000000000000000000000000 : ℝ)*base69 + (1798402022103243263/177000000000000000000000000000000 : ℝ)*base71 + (336531665969/138281250000000000000000000 : ℝ)*base74 + (517288440777243263/177000000000000000000000000000000 : ℝ)*base75 + (1510591126614243263/177000000000000000000000000000000 : ℝ)*base77 + (1838737547274243263/177000000000000000000000000000000 : ℝ)*base79 + (8462012031929/2212500000000000000000000000 : ℝ)*base82 + (7349933/10000000000000000000000 : ℝ)*base90 + (7349933/10000000000000000000000 : ℝ)*base92 + (7349933/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29671/50000 : ℝ) ≤ (4376672943043026890071461965001/7375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8267517/25000000000000 : ℝ)*(lower0) + (13148621/100000000000000 : ℝ)*(upper2) + (128444303/100000000000000 : ℝ)*(lower4) + (2846927/25000000000000 : ℝ)*(lower5) + (1008005701500261/25000000000000 : ℝ)*(major0) + (1008005701500261/25000000000000 : ℝ)*(major1) + (1008005701500261/25000000000000 : ℝ)*(major2) + (5366379650473419/100000000000000 : ℝ)*(sp0) + (1341594427882267/25000000000000 : ℝ)*(sp1) + (268319010803333/5000000000000 : ℝ)*(sp2) + (669470809684319/25000000000000 : ℝ)*(sp3) + (313067199/12500000000000 : ℝ)*(sp5) + (116914843/20000000000000 : ℝ)*(sp7) + (565593241/100000000000000 : ℝ)*(sp12) + (267788382331149/10000000000000 : ℝ)*(f.failure) + (268319010803333/5000000000000 : ℝ)*(f.sum) + (2608456257127/737500000000000000000000000 : ℝ)*base66 + (280100647668386111/14750000000000000000000000000000 : ℝ)*base67 + (122851814026886111/14750000000000000000000000000000 : ℝ)*base69 + (69215632425636111/14750000000000000000000000000000 : ℝ)*base71 + (7006476387679/1475000000000000000000000000 : ℝ)*base74 + (74530551403136111/14750000000000000000000000000000 : ℝ)*base75 + (79718906294636111/14750000000000000000000000000000 : ℝ)*base77 + (95936962555136111/14750000000000000000000000000000 : ℝ)*base79 + (207555688221/1475000000000000000000000000 : ℝ)*base81 + (15949053/1000000000000000000000 : ℝ)*base90 + (15949053/1000000000000000000000 : ℝ)*base92 + (15949053/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (39989/50000 : ℝ) ≤ (471884179234030894693557446667/590000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10449511/100000000000000 : ℝ)*(upper0) + (2011529/25000000000000 : ℝ)*(lower1) + (69773627/100000000000000 : ℝ)*(lower3) + (4897923/12500000000000 : ℝ)*(upper4) + (89987123644739/2000000000000 : ℝ)*(major0) + (89987123644739/2000000000000 : ℝ)*(major1) + (89987123644739/2000000000000 : ℝ)*(major2) + (130976103/250000000000 : ℝ)*(sp1) + (54581988443/100000000000000 : ℝ)*(sp2) + (5197272619/20000000000000 : ℝ)*(sp3) + (299189355800909/5000000000000 : ℝ)*(sp8) + (299186736278849/5000000000000 : ℝ)*(sp9) + (5983732534029737/100000000000000 : ℝ)*(sp10) + (747059784743013/25000000000000 : ℝ)*(sp11) + (2988265125335147/100000000000000 : ℝ)*(f.failure) + (299189355800909/5000000000000 : ℝ)*(f.sum) + (13645335011/22125000000000000000000000 : ℝ)*base66 + (1818883250453333/3540000000000000000000000000000 : ℝ)*base68 + (39487564657613333/3540000000000000000000000000000 : ℝ)*base70 + (10878021527646667/3540000000000000000000000000000 : ℝ)*base71 + (461987797247/177000000000000000000000000 : ℝ)*base73 + (37783945958813333/3540000000000000000000000000000 : ℝ)*base76 + (27546885660593333/3540000000000000000000000000000 : ℝ)*base78 + (14921773418406667/3540000000000000000000000000000 : ℝ)*base79 + (221175235943/22125000000000000000000000 : ℝ)*base82 + (121927941/10000000000000000000000 : ℝ)*base89 + (121927941/10000000000000000000000 : ℝ)*base91 + (121927941/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-83249/100000 : ℝ) ≤ (-12278872450392628820325231204029/14750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76878643/100000000000000 : ℝ)*(upper1) + (1561413/10000000000000 : ℝ)*(upper3) + (38945829/50000000000000 : ℝ)*(upper5) + (4534626169800293/100000000000000 : ℝ)*(major0) + (4534626169800293/100000000000000 : ℝ)*(major1) + (4534626169800293/100000000000000 : ℝ)*(major2) + (16223905587/100000000000000 : ℝ)*(sp4) + (36723113/80000000000 : ℝ)*(sp5) + (28864991187/25000000000000 : ℝ)*(sp6) + (29932646187/25000000000000 : ℝ)*(sp7) + (1521323788383339/25000000000000 : ℝ)*(sp12) + (1521316368386923/25000000000000 : ℝ)*(sp13) + (1217039183494839/20000000000000 : ℝ)*(sp14) + (1505785047935779/50000000000000 : ℝ)*(sp15) + (1505844913228153/50000000000000 : ℝ)*(f.failure) + (6085311377438943/100000000000000 : ℝ)*(f.sum) + (6229131653093/2212500000000000000000000000 : ℝ)*base65 + (777091599654344029/177000000000000000000000000000000 : ℝ)*base67 + (3109583008482344029/177000000000000000000000000000000 : ℝ)*base69 + (2020729091340344029/177000000000000000000000000000000 : ℝ)*base71 + (3076354257539/4425000000000000000000000000 : ℝ)*base74 + (4599250590563655971/177000000000000000000000000000000 : ℝ)*base76 + (885239049942344029/177000000000000000000000000000000 : ℝ)*base77 + (1268349164136344029/177000000000000000000000000000000 : ℝ)*base79 + (34228268641411/4425000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (16511959/5000000000000000000000 : ℝ)*base89 + (16511959/5000000000000000000000 : ℝ)*base91 + (16511959/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1198_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62239/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29671/50000 : ℝ) else (39989/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83249/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1198_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1198_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62239/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29671/50000 : ℝ) else (39989/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83249/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1198_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4195/1024 : ℝ) ≤ p) (hpb : p ≤ (8391/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (150567503/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (88/625 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (457/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62239/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29671/50000 : ℝ) else (39989/50000 : ℝ) ≤ X j i ∧ X j i ≤ (83249/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1198_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
