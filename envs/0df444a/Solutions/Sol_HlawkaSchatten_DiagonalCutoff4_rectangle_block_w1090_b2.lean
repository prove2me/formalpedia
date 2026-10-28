-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1090_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:57:02.272443+00:00
-- url     : https://prove2.me/submissions/16af9afb-42dd-45f3-84ad-6d8bbd86955b

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
theorem support_rectangle_w1090_s6_0 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2191962759/10000000000 : ℝ)*x 0 + (5394431857/10000000000 : ℝ)*x 1 + (5264417187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2191962759/10000000000 : ℝ)^8283 ≤ (266285637959/2000000000000 : ℝ)^6235 := by
    have hnat : (2191962759 : ℕ)^8283*2000000000000^6235 ≤ 266285637959^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2191962759 10000000000 266285637959 2000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394431857/10000000000 : ℝ)^8283 ≤ (44045177905559/100000000000000 : ℝ)^6235 := by
    have hnat : (5394431857 : ℕ)^8283*100000000000000^6235 ≤ 44045177905559^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394431857 10000000000 44045177905559 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264417187/10000000000 : ℝ)^8283 ≤ (4264054018341/10000000000000 : ℝ)^6235 := by
    have hnat : (5264417187 : ℕ)^8283*10000000000000^6235 ≤ 4264054018341^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264417187 10000000000 4264054018341 10000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2191962759/10000000000 : ℝ), (5394431857/10000000000 : ℝ), (5264417187/10000000000 : ℝ)] ![(266285637959/2000000000000 : ℝ), (44045177905559/100000000000000 : ℝ), (4264054018341/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2191962759/10000000000 : ℝ)|^8283 ≤ (266285637959/2000000000000 : ℝ)^6235
        have hw : |(-2191962759/10000000000 : ℝ)|=(2191962759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394431857/10000000000 : ℝ)|^8283 ≤ (44045177905559/100000000000000 : ℝ)^6235
        have hw : |(5394431857/10000000000 : ℝ)|=(5394431857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264417187/10000000000 : ℝ)|^8283 ≤ (4264054018341/10000000000000 : ℝ)^6235
        have hw : |(5264417187/10000000000 : ℝ)|=(5264417187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s6_1 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345042417/10000000000 : ℝ)*x 0 + (-2257928779/10000000000 : ℝ)*x 1 + (5264417187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345042417/10000000000 : ℝ)^8283 ≤ (43510264981543/100000000000000 : ℝ)^6235 := by
    have hnat : (5345042417 : ℕ)^8283*100000000000000^6235 ≤ 43510264981543^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345042417 10000000000 43510264981543 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257928779/10000000000 : ℝ)^8283 ≤ (2769838962647/20000000000000 : ℝ)^6235 := by
    have hnat : (2257928779 : ℕ)^8283*20000000000000^6235 ≤ 2769838962647^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257928779 10000000000 2769838962647 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264417187/10000000000 : ℝ)^8283 ≤ (4264054018341/10000000000000 : ℝ)^6235 := by
    have hnat : (5264417187 : ℕ)^8283*10000000000000^6235 ≤ 4264054018341^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264417187 10000000000 4264054018341 10000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345042417/10000000000 : ℝ), (-2257928779/10000000000 : ℝ), (5264417187/10000000000 : ℝ)] ![(43510264981543/100000000000000 : ℝ), (2769838962647/20000000000000 : ℝ), (4264054018341/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345042417/10000000000 : ℝ)|^8283 ≤ (43510264981543/100000000000000 : ℝ)^6235
        have hw : |(5345042417/10000000000 : ℝ)|=(5345042417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2257928779/10000000000 : ℝ)|^8283 ≤ (2769838962647/20000000000000 : ℝ)^6235
        have hw : |(-2257928779/10000000000 : ℝ)|=(2257928779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264417187/10000000000 : ℝ)|^8283 ≤ (4264054018341/10000000000000 : ℝ)^6235
        have hw : |(5264417187/10000000000 : ℝ)|=(5264417187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s6_2 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672521209/5000000000 : ℝ)*x 0 + (5264417187/10000000000 : ℝ)*x 1 + (-2257928779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672521209/5000000000 : ℝ)^8283 ≤ (43510264992357/100000000000000 : ℝ)^6235 := by
    have hnat : (2672521209 : ℕ)^8283*100000000000000^6235 ≤ 43510264992357^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672521209 5000000000 43510264992357 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264417187/10000000000 : ℝ)^8283 ≤ (4264054018341/10000000000000 : ℝ)^6235 := by
    have hnat : (5264417187 : ℕ)^8283*10000000000000^6235 ≤ 4264054018341^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264417187 10000000000 4264054018341 10000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2257928779/10000000000 : ℝ)^8283 ≤ (2769838962647/20000000000000 : ℝ)^6235 := by
    have hnat : (2257928779 : ℕ)^8283*20000000000000^6235 ≤ 2769838962647^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257928779 10000000000 2769838962647 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672521209/5000000000 : ℝ), (5264417187/10000000000 : ℝ), (-2257928779/10000000000 : ℝ)] ![(43510264992357/100000000000000 : ℝ), (4264054018341/10000000000000 : ℝ), (2769838962647/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672521209/5000000000 : ℝ)|^8283 ≤ (43510264992357/100000000000000 : ℝ)^6235
        have hw : |(2672521209/5000000000 : ℝ)|=(2672521209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264417187/10000000000 : ℝ)|^8283 ≤ (4264054018341/10000000000000 : ℝ)^6235
        have hw : |(5264417187/10000000000 : ℝ)|=(5264417187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2257928779/10000000000 : ℝ)|^8283 ≤ (2769838962647/20000000000000 : ℝ)^6235
        have hw : |(-2257928779/10000000000 : ℝ)|=(2257928779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s6_3 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372027243/10000000000 : ℝ)*x 0 + (2122951229/5000000000 : ℝ)*x 1 + (4501927717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372027243/10000000000 : ℝ)^8283 ≤ (33316437812997/100000000000000 : ℝ)^6235 := by
    have hnat : (4372027243 : ℕ)^8283*100000000000000^6235 ≤ 33316437812997^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372027243 10000000000 33316437812997 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2122951229/5000000000 : ℝ)^8283 ≤ (16022856780271/50000000000000 : ℝ)^6235 := by
    have hnat : (2122951229 : ℕ)^8283*50000000000000^6235 ≤ 16022856780271^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122951229 5000000000 16022856780271 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4501927717/10000000000 : ℝ)^8283 ≤ (8659462151759/25000000000000 : ℝ)^6235 := by
    have hnat : (4501927717 : ℕ)^8283*25000000000000^6235 ≤ 8659462151759^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501927717 10000000000 8659462151759 25000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372027243/10000000000 : ℝ), (2122951229/5000000000 : ℝ), (4501927717/10000000000 : ℝ)] ![(33316437812997/100000000000000 : ℝ), (16022856780271/50000000000000 : ℝ), (8659462151759/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372027243/10000000000 : ℝ)|^8283 ≤ (33316437812997/100000000000000 : ℝ)^6235
        have hw : |(4372027243/10000000000 : ℝ)|=(4372027243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2122951229/5000000000 : ℝ)|^8283 ≤ (16022856780271/50000000000000 : ℝ)^6235
        have hw : |(2122951229/5000000000 : ℝ)|=(2122951229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4501927717/10000000000 : ℝ)|^8283 ≤ (8659462151759/25000000000000 : ℝ)^6235
        have hw : |(4501927717/10000000000 : ℝ)|=(4501927717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s6_4 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-273995991/1250000000 : ℝ)*x 0 + (164523297/312500000 : ℝ)*x 1 + (1348525577/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (273995991/1250000000 : ℝ)^8283 ≤ (1331432360817/10000000000000 : ℝ)^6235 := by
    have hnat : (273995991 : ℕ)^8283*10000000000000^6235 ≤ 1331432360817^6235*1250000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273995991 1250000000 1331432360817 10000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164523297/312500000 : ℝ)^8283 ≤ (42644073002691/100000000000000 : ℝ)^6235 := by
    have hnat : (164523297 : ℕ)^8283*100000000000000^6235 ≤ 42644073002691^6235*312500000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164523297 312500000 42644073002691 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1348525577/2500000000 : ℝ)^8283 ≤ (44041603370991/100000000000000 : ℝ)^6235 := by
    have hnat : (1348525577 : ℕ)^8283*100000000000000^6235 ≤ 44041603370991^6235*2500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348525577 2500000000 44041603370991 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-273995991/1250000000 : ℝ), (164523297/312500000 : ℝ), (1348525577/2500000000 : ℝ)] ![(1331432360817/10000000000000 : ℝ), (42644073002691/100000000000000 : ℝ), (44041603370991/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-273995991/1250000000 : ℝ)|^8283 ≤ (1331432360817/10000000000000 : ℝ)^6235
        have hw : |(-273995991/1250000000 : ℝ)|=(273995991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164523297/312500000 : ℝ)|^8283 ≤ (42644073002691/100000000000000 : ℝ)^6235
        have hw : |(164523297/312500000 : ℝ)|=(164523297/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1348525577/2500000000 : ℝ)|^8283 ≤ (44041603370991/100000000000000 : ℝ)^6235
        have hw : |(1348525577/2500000000 : ℝ)|=(1348525577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s6_5 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312232537/10000000000 : ℝ)*x 0 + (-425648723/2000000000 : ℝ)*x 1 + (2697051149/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312232537/10000000000 : ℝ)^8283 ≤ (43155812707179/100000000000000 : ℝ)^6235 := by
    have hnat : (5312232537 : ℕ)^8283*100000000000000^6235 ≤ 43155812707179^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312232537 10000000000 43155812707179 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425648723/2000000000 : ℝ)^8283 ≤ (12802584019003/100000000000000 : ℝ)^6235 := by
    have hnat : (425648723 : ℕ)^8283*100000000000000^6235 ≤ 12802584019003^6235*2000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425648723 2000000000 12802584019003 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697051149/5000000000 : ℝ)^8283 ≤ (1761664130501/4000000000000 : ℝ)^6235 := by
    have hnat : (2697051149 : ℕ)^8283*4000000000000^6235 ≤ 1761664130501^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697051149 5000000000 1761664130501 4000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312232537/10000000000 : ℝ), (-425648723/2000000000 : ℝ), (2697051149/5000000000 : ℝ)] ![(43155812707179/100000000000000 : ℝ), (12802584019003/100000000000000 : ℝ), (1761664130501/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312232537/10000000000 : ℝ)|^8283 ≤ (43155812707179/100000000000000 : ℝ)^6235
        have hw : |(5312232537/10000000000 : ℝ)|=(5312232537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-425648723/2000000000 : ℝ)|^8283 ≤ (12802584019003/100000000000000 : ℝ)^6235
        have hw : |(-425648723/2000000000 : ℝ)|=(425648723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697051149/5000000000 : ℝ)|^8283 ≤ (1761664130501/4000000000000 : ℝ)^6235
        have hw : |(2697051149/5000000000 : ℝ)|=(2697051149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s6_6 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312232523/10000000000 : ℝ)*x 0 + (1078820459/2000000000 : ℝ)*x 1 + (-2128243637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312232523/10000000000 : ℝ)^8283 ≤ (43155812556087/100000000000000 : ℝ)^6235 := by
    have hnat : (5312232523 : ℕ)^8283*100000000000000^6235 ≤ 43155812556087^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312232523 10000000000 43155812556087 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078820459/2000000000 : ℝ)^8283 ≤ (8808320645997/20000000000000 : ℝ)^6235 := by
    have hnat : (1078820459 : ℕ)^8283*20000000000000^6235 ≤ 8808320645997^6235*2000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078820459 2000000000 8808320645997 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2128243637/10000000000 : ℝ)^8283 ≤ (50010094511/390625000000 : ℝ)^6235 := by
    have hnat : (2128243637 : ℕ)^8283*390625000000^6235 ≤ 50010094511^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128243637 10000000000 50010094511 390625000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312232523/10000000000 : ℝ), (1078820459/2000000000 : ℝ), (-2128243637/10000000000 : ℝ)] ![(43155812556087/100000000000000 : ℝ), (8808320645997/20000000000000 : ℝ), (50010094511/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312232523/10000000000 : ℝ)|^8283 ≤ (43155812556087/100000000000000 : ℝ)^6235
        have hw : |(5312232523/10000000000 : ℝ)|=(5312232523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078820459/2000000000 : ℝ)|^8283 ≤ (8808320645997/20000000000000 : ℝ)^6235
        have hw : |(1078820459/2000000000 : ℝ)|=(1078820459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2128243637/10000000000 : ℝ)|^8283 ≤ (50010094511/390625000000 : ℝ)^6235
        have hw : |(-2128243637/10000000000 : ℝ)|=(2128243637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s6_7 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372037347/10000000000 : ℝ)*x 0 + (4501281111/10000000000 : ℝ)*x 1 + (2123275693/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372037347/10000000000 : ℝ)^8283 ≤ (33316540099989/100000000000000 : ℝ)^6235 := by
    have hnat : (4372037347 : ℕ)^8283*100000000000000^6235 ≤ 33316540099989^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372037347 10000000000 33316540099989 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4501281111/10000000000 : ℝ)^8283 ≤ (34631239647683/100000000000000 : ℝ)^6235 := by
    have hnat : (4501281111 : ℕ)^8283*100000000000000^6235 ≤ 34631239647683^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4501281111 10000000000 34631239647683 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2123275693/5000000000 : ℝ)^8283 ≤ (32052220227101/100000000000000 : ℝ)^6235 := by
    have hnat : (2123275693 : ℕ)^8283*100000000000000^6235 ≤ 32052220227101^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123275693 5000000000 32052220227101 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372037347/10000000000 : ℝ), (4501281111/10000000000 : ℝ), (2123275693/5000000000 : ℝ)] ![(33316540099989/100000000000000 : ℝ), (34631239647683/100000000000000 : ℝ), (32052220227101/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372037347/10000000000 : ℝ)|^8283 ≤ (33316540099989/100000000000000 : ℝ)^6235
        have hw : |(4372037347/10000000000 : ℝ)|=(4372037347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4501281111/10000000000 : ℝ)|^8283 ≤ (34631239647683/100000000000000 : ℝ)^6235
        have hw : |(4501281111/10000000000 : ℝ)|=(4501281111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2123275693/5000000000 : ℝ)|^8283 ≤ (32052220227101/100000000000000 : ℝ)^6235
        have hw : |(2123275693/5000000000 : ℝ)|=(2123275693/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1090_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (5637/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3507/25000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (2809/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2809/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2809/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3517/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2809/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2809/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3517/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2809/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2809/25000 : ℝ) ^ (4141/1024 : ℝ) ≤ (14478572926043457/100000000000000000000 : ℝ) := by
    have hpowers : (2809/25000 : ℝ)^4141 ≤ (14478572926043457/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2809 : ℕ)^4141*100000000000000000000^1024 ≤ 14478572926043457^1024*25000^4141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2809 25000 14478572926043457 100000000000000000000 4141 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2809/25000 : ℝ)) (X := (14478572926043457/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3517/25000 : ℝ) ^ (4141/1024 : ℝ) ≤ (35933394338565809/100000000000000000000 : ℝ) := by
    have hpowers : (3517/25000 : ℝ)^4141 ≤ (35933394338565809/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3517 : ℕ)^4141*100000000000000000000^1024 ≤ 35933394338565809^1024*25000^4141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3517 25000 35933394338565809 100000000000000000000 4141 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3517/25000 : ℝ)) (X := (35933394338565809/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014478572926043457/50000000000000000000 : ℝ) ≤ (5000357991865891/5000000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (50014478572926043457/50000000000000000000 : ℝ)^1024 ≤ (5000357991865891/5000000000000000 : ℝ)^4141 := by
      have hnat : (50014478572926043457 : ℕ)^1024*5000000000000000^4141 ≤ 5000357991865891^4141*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014478572926043457 50000000000000000000 5000357991865891 5000000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000357991865891/5000000000000000 : ℝ)) (X := (50014478572926043457/50000000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025205983632304633/50000000000000000000 : ℝ) ≤ (2500311591784387/2500000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (50025205983632304633/50000000000000000000 : ℝ)^1024 ≤ (2500311591784387/2500000000000000 : ℝ)^4141 := by
      have hnat : (50025205983632304633 : ℕ)^1024*2500000000000000^4141 ≤ 2500311591784387^4141*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025205983632304633 50000000000000000000 2500311591784387 2500000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500311591784387/2500000000000000 : ℝ)) (X := (50025205983632304633/50000000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035933394338565809/50000000000000000000 : ℝ) ≤ (5000888375271657/5000000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (50035933394338565809/50000000000000000000 : ℝ)^1024 ≤ (5000888375271657/5000000000000000 : ℝ)^4141 := by
      have hnat : (50035933394338565809 : ℕ)^1024*5000000000000000^4141 ≤ 5000888375271657^4141*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035933394338565809 50000000000000000000 5000888375271657 5000000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000888375271657/5000000000000000 : ℝ)) (X := (50035933394338565809/50000000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14478572926043457/100000000000000000000 : ℝ) ≤ ((1769381805627127067/1770000000000000000 : ℝ)+2*(265191702883/141600000000000 : ℝ)*(2809/25000 : ℝ))^(4141/1024 : ℝ) := by
    rw [show (1769381805627127067/1770000000000000000 : ℝ)+2*(265191702883/141600000000000 : ℝ)*(2809/25000 : ℝ)=(5000357991865891/5000000000000000 : ℝ) by norm_num, show 1+2*(14478572926043457/100000000000000000000 : ℝ)=(50014478572926043457/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35933394338565809/100000000000000000000 : ℝ)+(14478572926043457/100000000000000000000 : ℝ) ≤ ((1769381805627127067/1770000000000000000 : ℝ)+(265191702883/141600000000000 : ℝ)*((3517/25000 : ℝ)+(2809/25000 : ℝ)))^(4141/1024 : ℝ) := by
    rw [show (1769381805627127067/1770000000000000000 : ℝ)+(265191702883/141600000000000 : ℝ)*((3517/25000 : ℝ)+(2809/25000 : ℝ))=(2500311591784387/2500000000000000 : ℝ) by norm_num, show 1+(35933394338565809/100000000000000000000 : ℝ)+(14478572926043457/100000000000000000000 : ℝ)=(50025205983632304633/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35933394338565809/100000000000000000000 : ℝ) ≤ ((1769381805627127067/1770000000000000000 : ℝ)+2*(265191702883/141600000000000 : ℝ)*(3517/25000 : ℝ))^(4141/1024 : ℝ) := by
    rw [show (1769381805627127067/1770000000000000000 : ℝ)+2*(265191702883/141600000000000 : ℝ)*(3517/25000 : ℝ)=(5000888375271657/5000000000000000 : ℝ) by norm_num, show 1+2*(35933394338565809/100000000000000000000 : ℝ)=(50035933394338565809/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1769381805627127067/1770000000000000000 : ℝ)*(X 1 0+X 2 0)+(265191702883/141600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (1769381805627127067/1770000000000000000 : ℝ)) (alpha := (265191702883/141600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1769381805627127067/1770000000000000000 : ℝ)*(X 0 1+X 2 1)+(265191702883/141600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (1769381805627127067/1770000000000000000 : ℝ)) (alpha := (265191702883/141600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1769381805627127067/1770000000000000000 : ℝ)*(X 0 2+X 1 2)+(265191702883/141600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (2809/25000 : ℝ)) (hi := (3517/25000 : ℝ)) (c := (1769381805627127067/1770000000000000000 : ℝ)) (alpha := (265191702883/141600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2191962759/10000000000 : ℝ)*X 0 0+(5394431857/10000000000 : ℝ)*X 0 1+(5264417187/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345042417/10000000000 : ℝ)*X 1 0+(-2257928779/10000000000 : ℝ)*X 1 1+(5264417187/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672521209/5000000000 : ℝ)*X 2 0+(5264417187/10000000000 : ℝ)*X 2 1+(-2257928779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4372027243/10000000000 : ℝ)*X 0 0+(2122951229/5000000000 : ℝ)*X 0 1+(4501927717/10000000000 : ℝ)*X 0 2+(4372027243/10000000000 : ℝ)*X 1 0+(2122951229/5000000000 : ℝ)*X 1 1+(4501927717/10000000000 : ℝ)*X 1 2+(4372027243/10000000000 : ℝ)*X 2 0+(2122951229/5000000000 : ℝ)*X 2 1+(4501927717/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-273995991/1250000000 : ℝ)*X 0 0+(164523297/312500000 : ℝ)*X 0 1+(1348525577/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312232537/10000000000 : ℝ)*X 1 0+(-425648723/2000000000 : ℝ)*X 1 1+(2697051149/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312232523/10000000000 : ℝ)*X 2 0+(1078820459/2000000000 : ℝ)*X 2 1+(-2128243637/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4372037347/10000000000 : ℝ)*X 0 0+(4501281111/10000000000 : ℝ)*X 0 1+(2123275693/5000000000 : ℝ)*X 0 2+(4372037347/10000000000 : ℝ)*X 1 0+(4501281111/10000000000 : ℝ)*X 1 1+(2123275693/5000000000 : ℝ)*X 1 2+(4372037347/10000000000 : ℝ)*X 2 0+(4501281111/10000000000 : ℝ)*X 2 1+(2123275693/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (708302605597321332453/73750000000000000000000000 : ℝ) := by norm_num
    linear_combination (960225559/50000000000000 : ℝ)*(base19) + (447285361/25000000000000 : ℝ)*(base23) + (7095473/10000000000000 : ℝ)*(lower2) + (243224509/100000000000000 : ℝ)*(upper3) + (14563677/10000000000000 : ℝ)*(upper5) + (724841466291377/12500000000000 : ℝ)*(major0) + (724841466291377/12500000000000 : ℝ)*(major1) + (724841466291377/12500000000000 : ℝ)*(major2) + (240359174322739/3125000000000 : ℝ)*(sp0) + (7691543030078171/100000000000000 : ℝ)*(sp1) + (1922885790346961/25000000000000 : ℝ)*(sp2) + (976472501255447/25000000000000 : ℝ)*(sp3) + (1284305041/2500000000000 : ℝ)*(sp4) + (28184974173/100000000000000 : ℝ)*(sp7) + (3905918189995961/100000000000000 : ℝ)*(f.failure) + (961443118816161/12500000000000 : ℝ)*(f.sum) + (929181513659/221250000000000000000000000 : ℝ)*base65 + (338241341057663759/22125000000000000000000000000000 : ℝ)*base67 + (89611364450288759/22125000000000000000000000000000 : ℝ)*base69 + (269698559687288759/22125000000000000000000000000000 : ℝ)*base71 + (1013961600161/885000000000000000000000000 : ℝ)*base73 + (732377823241836241/22125000000000000000000000000000 : ℝ)*base76 + (64583363418336241/22125000000000000000000000000000 : ℝ)*base78 + (33457905187836241/22125000000000000000000000000000 : ℝ)*base80 + (5682184911161/885000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (60517577/10000000000000000000000 : ℝ)*base90 + (60517577/10000000000000000000000 : ℝ)*base92 + (60517577/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (525271650506262162411/147500000000000000000000000 : ℝ) := by norm_num
    linear_combination (483500299/50000000000000 : ℝ)*(base19) + (14653687/1562500000000 : ℝ)*(base23) + (1282193/50000000000000 : ℝ)*(upper2) + (43865451/50000000000000 : ℝ)*(upper3) + (27129903/25000000000000 : ℝ)*(upper5) + (728517844385653/12500000000000 : ℝ)*(major0) + (728517844385653/12500000000000 : ℝ)*(major1) + (728517844385653/12500000000000 : ℝ)*(major2) + (6745745953/25000000000000 : ℝ)*(sp1) + (24777985093/100000000000000 : ℝ)*(sp2) + (309222259217999/4000000000000 : ℝ)*(sp4) + (1546105706093113/20000000000000 : ℝ)*(sp5) + (1546106152925783/20000000000000 : ℝ)*(sp6) + (122679028469219/3125000000000 : ℝ)*(sp7) + (122679028469219/3125000000000 : ℝ)*(f.failure) + (309222259217999/4000000000000 : ℝ)*(f.sum) + (2523871311161/885000000000000000000000000 : ℝ)*base66 + (200216113330757251/22125000000000000000000000000000 : ℝ)*base67 + (149048408756742749/22125000000000000000000000000000 : ℝ)*base70 + (129388025709632251/22125000000000000000000000000000 : ℝ)*base71 + (1619594638963/442500000000000000000000000 : ℝ)*base74 + (73511510728992749/22125000000000000000000000000000 : ℝ)*base76 + (145635357736617749/22125000000000000000000000000000 : ℝ)*base78 + (17337701814257251/22125000000000000000000000000000 : ℝ)*base79 + (4569499083011/885000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (1161683/312500000000000000000 : ℝ)*base90 + (1161683/312500000000000000000 : ℝ)*base92 + (1161683/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1090_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1090_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1090_s7_0 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1095999737/5000000000 : ℝ)*x 0 + (337126023/625000000 : ℝ)*x 1 + (1316202119/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1095999737/5000000000 : ℝ)^8283 ≤ (6657289081529/50000000000000 : ℝ)^6235 := by
    have hnat : (1095999737 : ℕ)^8283*50000000000000^6235 ≤ 6657289081529^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1095999737 5000000000 6657289081529 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337126023/625000000 : ℝ)^8283 ≤ (44040671213361/100000000000000 : ℝ)^6235 := by
    have hnat : (337126023 : ℕ)^8283*100000000000000^6235 ≤ 44040671213361^6235*625000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337126023 625000000 44040671213361 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316202119/2500000000 : ℝ)^8283 ≤ (21322375307151/50000000000000 : ℝ)^6235 := by
    have hnat : (1316202119 : ℕ)^8283*50000000000000^6235 ≤ 21322375307151^6235*2500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316202119 2500000000 21322375307151 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1095999737/5000000000 : ℝ), (337126023/625000000 : ℝ), (1316202119/2500000000 : ℝ)] ![(6657289081529/50000000000000 : ℝ), (44040671213361/100000000000000 : ℝ), (21322375307151/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1095999737/5000000000 : ℝ)|^8283 ≤ (6657289081529/50000000000000 : ℝ)^6235
        have hw : |(-1095999737/5000000000 : ℝ)|=(1095999737/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337126023/625000000 : ℝ)|^8283 ≤ (44040671213361/100000000000000 : ℝ)^6235
        have hw : |(337126023/625000000 : ℝ)|=(337126023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316202119/2500000000 : ℝ)|^8283 ≤ (21322375307151/50000000000000 : ℝ)^6235
        have hw : |(1316202119/2500000000 : ℝ)|=(1316202119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s7_1 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068987603/2000000000 : ℝ)*x 0 + (-2257550281/10000000000 : ℝ)*x 1 + (2632404359/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068987603/2000000000 : ℝ)^8283 ≤ (43509135967871/100000000000000 : ℝ)^6235 := by
    have hnat : (1068987603 : ℕ)^8283*100000000000000^6235 ≤ 43509135967871^6235*2000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068987603 2000000000 43509135967871 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2257550281/10000000000 : ℝ)^8283 ≤ (432690962303/3125000000000 : ℝ)^6235 := by
    have hnat : (2257550281 : ℕ)^8283*3125000000000^6235 ≤ 432690962303^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2257550281 10000000000 432690962303 3125000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632404359/5000000000 : ℝ)^8283 ≤ (21322376609177/50000000000000 : ℝ)^6235 := by
    have hnat : (2632404359 : ℕ)^8283*50000000000000^6235 ≤ 21322376609177^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632404359 5000000000 21322376609177 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068987603/2000000000 : ℝ), (-2257550281/10000000000 : ℝ), (2632404359/5000000000 : ℝ)] ![(43509135967871/100000000000000 : ℝ), (432690962303/3125000000000 : ℝ), (21322376609177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068987603/2000000000 : ℝ)|^8283 ≤ (43509135967871/100000000000000 : ℝ)^6235
        have hw : |(1068987603/2000000000 : ℝ)|=(1068987603/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2257550281/10000000000 : ℝ)|^8283 ≤ (432690962303/3125000000000 : ℝ)^6235
        have hw : |(-2257550281/10000000000 : ℝ)|=(2257550281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632404359/5000000000 : ℝ)|^8283 ≤ (21322376609177/50000000000000 : ℝ)^6235
        have hw : |(2632404359/5000000000 : ℝ)|=(2632404359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s7_2 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344938523/10000000000 : ℝ)*x 0 + (1316202087/2500000000 : ℝ)*x 1 + (-141096881/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344938523/10000000000 : ℝ)^8283 ≤ (43509141461417/100000000000000 : ℝ)^6235 := by
    have hnat : (5344938523 : ℕ)^8283*100000000000000^6235 ≤ 43509141461417^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344938523 10000000000 43509141461417 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316202087/2500000000 : ℝ)^8283 ≤ (42644749236953/100000000000000 : ℝ)^6235 := by
    have hnat : (1316202087 : ℕ)^8283*100000000000000^6235 ≤ 42644749236953^6235*2500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316202087 2500000000 42644749236953 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (141096881/625000000 : ℝ)^8283 ≤ (13846109286349/100000000000000 : ℝ)^6235 := by
    have hnat : (141096881 : ℕ)^8283*100000000000000^6235 ≤ 13846109286349^6235*625000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141096881 625000000 13846109286349 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344938523/10000000000 : ℝ), (1316202087/2500000000 : ℝ), (-141096881/625000000 : ℝ)] ![(43509141461417/100000000000000 : ℝ), (42644749236953/100000000000000 : ℝ), (13846109286349/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344938523/10000000000 : ℝ)|^8283 ≤ (43509141461417/100000000000000 : ℝ)^6235
        have hw : |(5344938523/10000000000 : ℝ)|=(5344938523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316202087/2500000000 : ℝ)|^8283 ≤ (42644749236953/100000000000000 : ℝ)^6235
        have hw : |(1316202087/2500000000 : ℝ)|=(1316202087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-141096881/625000000 : ℝ)|^8283 ≤ (13846109286349/100000000000000 : ℝ)^6235
        have hw : |(-141096881/625000000 : ℝ)|=(141096881/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s7_3 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372048031/10000000000 : ℝ)*x 0 + (1061673601/2500000000 : ℝ)*x 1 + (225056511/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372048031/10000000000 : ℝ)^8283 ≤ (33316648258647/100000000000000 : ℝ)^6235 := by
    have hnat : (4372048031 : ℕ)^8283*100000000000000^6235 ≤ 33316648258647^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372048031 10000000000 33316648258647 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061673601/2500000000 : ℝ)^8283 ≤ (32053654282869/100000000000000 : ℝ)^6235 := by
    have hnat : (1061673601 : ℕ)^8283*100000000000000^6235 ≤ 32053654282869^6235*2500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061673601 2500000000 32053654282869 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (225056511/500000000 : ℝ)^8283 ≤ (34629697435779/100000000000000 : ℝ)^6235 := by
    have hnat : (225056511 : ℕ)^8283*100000000000000^6235 ≤ 34629697435779^6235*500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225056511 500000000 34629697435779 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372048031/10000000000 : ℝ), (1061673601/2500000000 : ℝ), (225056511/500000000 : ℝ)] ![(33316648258647/100000000000000 : ℝ), (32053654282869/100000000000000 : ℝ), (34629697435779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372048031/10000000000 : ℝ)|^8283 ≤ (33316648258647/100000000000000 : ℝ)^6235
        have hw : |(4372048031/10000000000 : ℝ)|=(4372048031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061673601/2500000000 : ℝ)|^8283 ≤ (32053654282869/100000000000000 : ℝ)^6235
        have hw : |(1061673601/2500000000 : ℝ)|=(1061673601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(225056511/500000000 : ℝ)|^8283 ≤ (34629697435779/100000000000000 : ℝ)^6235
        have hw : |(225056511/500000000 : ℝ)|=(225056511/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s7_4 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-137000293/625000000 : ℝ)*x 0 + (5265132861/10000000000 : ℝ)*x 1 + (539369067/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137000293/625000000 : ℝ)^8283 ≤ (3328655059157/25000000000000 : ℝ)^6235 := by
    have hnat : (137000293 : ℕ)^8283*25000000000000^6235 ≤ 3328655059157^6235*625000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137000293 625000000 3328655059157 25000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265132861/10000000000 : ℝ)^8283 ≤ (42648241208511/100000000000000 : ℝ)^6235 := by
    have hnat : (5265132861 : ℕ)^8283*100000000000000^6235 ≤ 42648241208511^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265132861 10000000000 42648241208511 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (539369067/1000000000 : ℝ)^8283 ≤ (22018569269291/50000000000000 : ℝ)^6235 := by
    have hnat : (539369067 : ℕ)^8283*50000000000000^6235 ≤ 22018569269291^6235*1000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539369067 1000000000 22018569269291 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-137000293/625000000 : ℝ), (5265132861/10000000000 : ℝ), (539369067/1000000000 : ℝ)] ![(3328655059157/25000000000000 : ℝ), (42648241208511/100000000000000 : ℝ), (22018569269291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-137000293/625000000 : ℝ)|^8283 ≤ (3328655059157/25000000000000 : ℝ)^6235
        have hw : |(-137000293/625000000 : ℝ)|=(137000293/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265132861/10000000000 : ℝ)|^8283 ≤ (42648241208511/100000000000000 : ℝ)^6235
        have hw : |(5265132861/10000000000 : ℝ)|=(5265132861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(539369067/1000000000 : ℝ)|^8283 ≤ (22018569269291/50000000000000 : ℝ)^6235
        have hw : |(539369067/1000000000 : ℝ)|=(539369067/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s7_5 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (16601037/31250000 : ℝ)*x 0 + (-106433409/500000000 : ℝ)*x 1 + (5393690669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (16601037/31250000 : ℝ)^8283 ≤ (10789221104199/25000000000000 : ℝ)^6235 := by
    have hnat : (16601037 : ℕ)^8283*25000000000000^6235 ≤ 10789221104199^6235*31250000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16601037 31250000 10789221104199 25000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (106433409/500000000 : ℝ)^8283 ≤ (12805977035071/100000000000000 : ℝ)^6235 := by
    have hnat : (106433409 : ℕ)^8283*100000000000000^6235 ≤ 12805977035071^6235*500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      106433409 500000000 12805977035071 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393690669/10000000000 : ℝ)^8283 ≤ (5504642315967/12500000000000 : ℝ)^6235 := by
    have hnat : (5393690669 : ℕ)^8283*12500000000000^6235 ≤ 5504642315967^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393690669 10000000000 5504642315967 12500000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(16601037/31250000 : ℝ), (-106433409/500000000 : ℝ), (5393690669/10000000000 : ℝ)] ![(10789221104199/25000000000000 : ℝ), (12805977035071/100000000000000 : ℝ), (5504642315967/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(16601037/31250000 : ℝ)|^8283 ≤ (10789221104199/25000000000000 : ℝ)^6235
        have hw : |(16601037/31250000 : ℝ)|=(16601037/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-106433409/500000000 : ℝ)|^8283 ≤ (12805977035071/100000000000000 : ℝ)^6235
        have hw : |(-106433409/500000000 : ℝ)|=(106433409/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393690669/10000000000 : ℝ)|^8283 ≤ (5504642315967/12500000000000 : ℝ)^6235
        have hw : |(5393690669/10000000000 : ℝ)|=(5393690669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s7_6 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656165921/5000000000 : ℝ)*x 0 + (1348422667/2500000000 : ℝ)*x 1 + (-2128668179/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656165921/5000000000 : ℝ)^8283 ≤ (43156884438381/100000000000000 : ℝ)^6235 := by
    have hnat : (2656165921 : ℕ)^8283*100000000000000^6235 ≤ 43156884438381^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656165921 5000000000 43156884438381 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348422667/2500000000 : ℝ)^8283 ≤ (44037138516889/100000000000000 : ℝ)^6235 := by
    have hnat : (1348422667 : ℕ)^8283*100000000000000^6235 ≤ 44037138516889^6235*2500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348422667 2500000000 44037138516889 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2128668179/10000000000 : ℝ)^8283 ≤ (12805977027079/100000000000000 : ℝ)^6235 := by
    have hnat : (2128668179 : ℕ)^8283*100000000000000^6235 ≤ 12805977027079^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128668179 10000000000 12805977027079 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656165921/5000000000 : ℝ), (1348422667/2500000000 : ℝ), (-2128668179/10000000000 : ℝ)] ![(43156884438381/100000000000000 : ℝ), (44037138516889/100000000000000 : ℝ), (12805977027079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656165921/5000000000 : ℝ)|^8283 ≤ (43156884438381/100000000000000 : ℝ)^6235
        have hw : |(2656165921/5000000000 : ℝ)|=(2656165921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348422667/2500000000 : ℝ)|^8283 ≤ (44037138516889/100000000000000 : ℝ)^6235
        have hw : |(1348422667/2500000000 : ℝ)|=(1348422667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2128668179/10000000000 : ℝ)|^8283 ≤ (12805977027079/100000000000000 : ℝ)^6235
        have hw : |(-2128668179/10000000000 : ℝ)|=(2128668179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s7_7 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174882311/400000000 : ℝ)*x 0 + (2250245871/5000000000 : ℝ)*x 1 + (849467067/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174882311/400000000 : ℝ)^8283 ≤ (16658373450681/50000000000000 : ℝ)^6235 := by
    have hnat : (174882311 : ℕ)^8283*50000000000000^6235 ≤ 16658373450681^6235*400000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174882311 400000000 16658373450681 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2250245871/5000000000 : ℝ)^8283 ≤ (34623171930541/100000000000000 : ℝ)^6235 := by
    have hnat : (2250245871 : ℕ)^8283*100000000000000^6235 ≤ 34623171930541^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2250245871 5000000000 34623171930541 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (849467067/2000000000 : ℝ)^8283 ≤ (2003755072303/6250000000000 : ℝ)^6235 := by
    have hnat : (849467067 : ℕ)^8283*6250000000000^6235 ≤ 2003755072303^6235*2000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      849467067 2000000000 2003755072303 6250000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174882311/400000000 : ℝ), (2250245871/5000000000 : ℝ), (849467067/2000000000 : ℝ)] ![(16658373450681/50000000000000 : ℝ), (34623171930541/100000000000000 : ℝ), (2003755072303/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174882311/400000000 : ℝ)|^8283 ≤ (16658373450681/50000000000000 : ℝ)^6235
        have hw : |(174882311/400000000 : ℝ)|=(174882311/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2250245871/5000000000 : ℝ)|^8283 ≤ (34623171930541/100000000000000 : ℝ)^6235
        have hw : |(2250245871/5000000000 : ℝ)|=(2250245871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(849467067/2000000000 : ℝ)|^8283 ≤ (2003755072303/6250000000000 : ℝ)^6235
        have hw : |(849467067/2000000000 : ℝ)|=(849467067/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1090_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11283/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (701/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3507/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5637/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3507/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5637/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3507/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5637/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3507/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5637/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3507/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5637/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3507/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5637/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5637/50000 : ℝ) ^ (4141/1024 : ℝ) ≤ (1467761172087073/10000000000000000000 : ℝ) := by
    have hpowers : (5637/50000 : ℝ)^4141 ≤ (1467761172087073/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5637 : ℕ)^4141*10000000000000000000^1024 ≤ 1467761172087073^1024*50000^4141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5637 50000 1467761172087073 10000000000000000000 4141 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5637/50000 : ℝ)) (X := (1467761172087073/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3507/25000 : ℝ) ^ (4141/1024 : ℝ) ≤ (7104401323210749/20000000000000000000 : ℝ) := by
    have hpowers : (3507/25000 : ℝ)^4141 ≤ (7104401323210749/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3507 : ℕ)^4141*20000000000000000000^1024 ≤ 7104401323210749^1024*25000^4141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3507 25000 7104401323210749 20000000000000000000 4141 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3507/25000 : ℝ)) (X := (7104401323210749/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5001467761172087073/5000000000000000000 : ℝ) ≤ (10000725825364587/10000000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (5001467761172087073/5000000000000000000 : ℝ)^1024 ≤ (10000725825364587/10000000000000000 : ℝ)^4141 := by
      have hnat : (5001467761172087073 : ℕ)^1024*10000000000000000^4141 ≤ 10000725825364587^4141*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5001467761172087073 5000000000000000000 10000725825364587 10000000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000725825364587/10000000000000000 : ℝ)) (X := (5001467761172087073/5000000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4002007984733476979/4000000000000000000 : ℝ) ≤ (2000248223618283/2000000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (4002007984733476979/4000000000000000000 : ℝ)^1024 ≤ (2000248223618283/2000000000000000 : ℝ)^4141 := by
      have hnat : (4002007984733476979 : ℕ)^1024*2000000000000000^4141 ≤ 2000248223618283^4141*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4002007984733476979 4000000000000000000 2000248223618283 2000000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000248223618283/2000000000000000 : ℝ)) (X := (4002007984733476979/4000000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10007104401323210749/10000000000000000000 : ℝ) ≤ (10001756410818243/10000000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (10007104401323210749/10000000000000000000 : ℝ)^1024 ≤ (10001756410818243/10000000000000000 : ℝ)^4141 := by
      have hnat : (10007104401323210749 : ℕ)^1024*10000000000000000^4141 ≤ 10001756410818243^4141*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10007104401323210749 10000000000000000000 10001756410818243 10000000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001756410818243/10000000000000000 : ℝ)) (X := (10007104401323210749/10000000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1467761172087073/10000000000000000000 : ℝ) ≤ ((1529465561258308603/1530000000000000000 : ℝ)+2*(42941060569/22950000000000 : ℝ)*(5637/50000 : ℝ))^(4141/1024 : ℝ) := by
    rw [show (1529465561258308603/1530000000000000000 : ℝ)+2*(42941060569/22950000000000 : ℝ)*(5637/50000 : ℝ)=(10000725825364587/10000000000000000 : ℝ) by norm_num, show 1+2*(1467761172087073/10000000000000000000 : ℝ)=(5001467761172087073/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7104401323210749/20000000000000000000 : ℝ)+(1467761172087073/10000000000000000000 : ℝ) ≤ ((1529465561258308603/1530000000000000000 : ℝ)+(42941060569/22950000000000 : ℝ)*((3507/25000 : ℝ)+(5637/50000 : ℝ)))^(4141/1024 : ℝ) := by
    rw [show (1529465561258308603/1530000000000000000 : ℝ)+(42941060569/22950000000000 : ℝ)*((3507/25000 : ℝ)+(5637/50000 : ℝ))=(2000248223618283/2000000000000000 : ℝ) by norm_num, show 1+(7104401323210749/20000000000000000000 : ℝ)+(1467761172087073/10000000000000000000 : ℝ)=(4002007984733476979/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7104401323210749/20000000000000000000 : ℝ) ≤ ((1529465561258308603/1530000000000000000 : ℝ)+2*(42941060569/22950000000000 : ℝ)*(3507/25000 : ℝ))^(4141/1024 : ℝ) := by
    rw [show (1529465561258308603/1530000000000000000 : ℝ)+2*(42941060569/22950000000000 : ℝ)*(3507/25000 : ℝ)=(10001756410818243/10000000000000000 : ℝ) by norm_num, show 1+2*(7104401323210749/20000000000000000000 : ℝ)=(10007104401323210749/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1529465561258308603/1530000000000000000 : ℝ)*(X 1 0+X 2 0)+(42941060569/22950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (1529465561258308603/1530000000000000000 : ℝ)) (alpha := (42941060569/22950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1529465561258308603/1530000000000000000 : ℝ)*(X 0 1+X 2 1)+(42941060569/22950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (1529465561258308603/1530000000000000000 : ℝ)) (alpha := (42941060569/22950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1529465561258308603/1530000000000000000 : ℝ)*(X 0 2+X 1 2)+(42941060569/22950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (5637/50000 : ℝ)) (hi := (3507/25000 : ℝ)) (c := (1529465561258308603/1530000000000000000 : ℝ)) (alpha := (42941060569/22950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1095999737/5000000000 : ℝ)*X 0 0+(337126023/625000000 : ℝ)*X 0 1+(1316202119/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068987603/2000000000 : ℝ)*X 1 0+(-2257550281/10000000000 : ℝ)*X 1 1+(2632404359/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344938523/10000000000 : ℝ)*X 2 0+(1316202087/2500000000 : ℝ)*X 2 1+(-141096881/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4372048031/10000000000 : ℝ)*X 0 0+(1061673601/2500000000 : ℝ)*X 0 1+(225056511/500000000 : ℝ)*X 0 2+(4372048031/10000000000 : ℝ)*X 1 0+(1061673601/2500000000 : ℝ)*X 1 1+(225056511/500000000 : ℝ)*X 1 2+(4372048031/10000000000 : ℝ)*X 2 0+(1061673601/2500000000 : ℝ)*X 2 1+(225056511/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-137000293/625000000 : ℝ)*X 0 0+(5265132861/10000000000 : ℝ)*X 0 1+(539369067/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((16601037/31250000 : ℝ)*X 1 0+(-106433409/500000000 : ℝ)*X 1 1+(5393690669/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656165921/5000000000 : ℝ)*X 2 0+(1348422667/2500000000 : ℝ)*X 2 1+(-2128668179/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174882311/400000000 : ℝ)*X 0 0+(2250245871/5000000000 : ℝ)*X 0 1+(849467067/2000000000 : ℝ)*X 0 2+(174882311/400000000 : ℝ)*X 1 0+(2250245871/5000000000 : ℝ)*X 1 1+(849467067/2000000000 : ℝ)*X 1 2+(174882311/400000000 : ℝ)*X 2 0+(2250245871/5000000000 : ℝ)*X 2 1+(849467067/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (245467946161738485006350821/76500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119999927/20000000000000 : ℝ)*(base19) + (920316607/100000000000000 : ℝ)*(base23) + (28892311/12500000000000 : ℝ)*(lower2) + (39909969/100000000000000 : ℝ)*(upper5) + (583490615432331/10000000000000 : ℝ)*(major0) + (583490615432331/10000000000000 : ℝ)*(major1) + (5834906154323311/100000000000000 : ℝ)*(major2) + (3869744099448311/50000000000000 : ℝ)*(sp0) + (967440521942541/12500000000000 : ℝ)*(sp1) + (1934881667504543/25000000000000 : ℝ)*(sp2) + (1965135838606069/50000000000000 : ℝ)*(sp3) + (39391438157/100000000000000 : ℝ)*(sp4) + (2814794817/100000000000000 : ℝ)*(sp5) + (6467070987/50000000000000 : ℝ)*(sp7) + (7676337131551/195312500000 : ℝ)*(f.failure) + (7739527590334779/100000000000000 : ℝ)*(f.sum) + (17674919690569/2295000000000000000000000000 : ℝ)*base65 + (261820321999410779/45900000000000000000000000000000 : ℝ)*base67 + (960154473521581511/51000000000000000000000000000000 : ℝ)*base69 + (695830076408910779/45900000000000000000000000000000 : ℝ)*base71 + (101480050091/2295000000000000000000000000 : ℝ)*base74 + (1155424353956581511/51000000000000000000000000000000 : ℝ)*base75 + (18195289376414329/900000000000000000000000000000 : ℝ)*base77 + (12155419767614329/900000000000000000000000000000 : ℝ)*base79 + (329405443169/76500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (106291/9765625000000000000 : ℝ)*base90 + (106291/9765625000000000000 : ℝ)*base92 + (815789/39062500000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (83351625359808300794072573/7650000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (62532211/3125000000000 : ℝ)*(base19) + (2184050807/100000000000000 : ℝ)*(base23) + (108612511/50000000000000 : ℝ)*(upper3) + (81601841/100000000000000 : ℝ)*(lower4) + (220560313/100000000000000 : ℝ)*(upper5) + (1172872662099997/20000000000000 : ℝ)*(major0) + (1172872662099997/20000000000000 : ℝ)*(major1) + (1172872662099997/20000000000000 : ℝ)*(major2) + (2730148691/5000000000000 : ℝ)*(sp1) + (58916814169/100000000000000 : ℝ)*(sp2) + (1555719970433591/20000000000000 : ℝ)*(sp4) + (3889271624081691/50000000000000 : ℝ)*(sp5) + (7778538751302979/100000000000000 : ℝ)*(sp6) + (61720725088189/1562500000000 : ℝ)*(sp7) + (61720725088189/1562500000000 : ℝ)*(f.failure) + (1555719970433591/20000000000000 : ℝ)*(f.sum) + (437893017827/229500000000000000000000000 : ℝ)*base66 + (1193675915654269/5400000000000000000000000000000 : ℝ)*base67 + (61766476708545731/5400000000000000000000000000000 : ℝ)*base70 + (78450773386545731/5400000000000000000000000000000 : ℝ)*base72 + (732009590141/229500000000000000000000000 : ℝ)*base74 + (77891770235745731/5400000000000000000000000000000 : ℝ)*base76 + (26411186821545731/5400000000000000000000000000000 : ℝ)*base78 + (124232737140945731/5400000000000000000000000000000 : ℝ)*base80 + (2470050626419/459000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (11473/156250000000000000000 : ℝ)*base90 + (11473/156250000000000000000 : ℝ)*base92 + (11473/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1090_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3507/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5637/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (701/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1090_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1090_s8_0 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-274000357/1250000000 : ℝ)*x 0 + (2696964629/5000000000 : ℝ)*x 1 + (1052978749/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (274000357/1250000000 : ℝ)^8283 ≤ (13314605453583/100000000000000 : ℝ)^6235 := by
    have hnat : (274000357 : ℕ)^8283*100000000000000^6235 ≤ 13314605453583^6235*1250000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274000357 1250000000 13314605453583 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696964629/5000000000 : ℝ)^8283 ≤ (44039726370177/100000000000000 : ℝ)^6235 := by
    have hnat : (2696964629 : ℕ)^8283*100000000000000^6235 ≤ 44039726370177^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696964629 5000000000 44039726370177 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052978749/2000000000 : ℝ)^8283 ≤ (21322834078761/50000000000000 : ℝ)^6235 := by
    have hnat : (1052978749 : ℕ)^8283*50000000000000^6235 ≤ 21322834078761^6235*2000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052978749 2000000000 21322834078761 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-274000357/1250000000 : ℝ), (2696964629/5000000000 : ℝ), (1052978749/2000000000 : ℝ)] ![(13314605453583/100000000000000 : ℝ), (44039726370177/100000000000000 : ℝ), (21322834078761/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-274000357/1250000000 : ℝ)|^8283 ≤ (13314605453583/100000000000000 : ℝ)^6235
        have hw : |(-274000357/1250000000 : ℝ)|=(274000357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696964629/5000000000 : ℝ)|^8283 ≤ (44039726370177/100000000000000 : ℝ)^6235
        have hw : |(2696964629/5000000000 : ℝ)|=(2696964629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052978749/2000000000 : ℝ)|^8283 ≤ (21322834078761/50000000000000 : ℝ)^6235
        have hw : |(1052978749/2000000000 : ℝ)|=(1052978749/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s8_1 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344917693/10000000000 : ℝ)*x 0 + (-141091529/625000000 : ℝ)*x 1 + (5264894121/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344917693/10000000000 : ℝ)^8283 ≤ (43508916204573/100000000000000 : ℝ)^6235 := by
    have hnat : (5344917693 : ℕ)^8283*100000000000000^6235 ≤ 43508916204573^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344917693 10000000000 43508916204573 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (141091529/625000000 : ℝ)^8283 ≤ (6922705788177/50000000000000 : ℝ)^6235 := by
    have hnat : (141091529 : ℕ)^8283*50000000000000^6235 ≤ 6922705788177^6235*625000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      141091529 625000000 6922705788177 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264894121/10000000000 : ℝ)^8283 ≤ (10661418050877/25000000000000 : ℝ)^6235 := by
    have hnat : (5264894121 : ℕ)^8283*25000000000000^6235 ≤ 10661418050877^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264894121 10000000000 10661418050877 25000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344917693/10000000000 : ℝ), (-141091529/625000000 : ℝ), (5264894121/10000000000 : ℝ)] ![(43508916204573/100000000000000 : ℝ), (6922705788177/50000000000000 : ℝ), (10661418050877/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344917693/10000000000 : ℝ)|^8283 ≤ (43508916204573/100000000000000 : ℝ)^6235
        have hw : |(5344917693/10000000000 : ℝ)|=(5344917693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-141091529/625000000 : ℝ)|^8283 ≤ (6922705788177/50000000000000 : ℝ)^6235
        have hw : |(-141091529/625000000 : ℝ)|=(141091529/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264894121/10000000000 : ℝ)|^8283 ≤ (10661418050877/25000000000000 : ℝ)^6235
        have hw : |(5264894121/10000000000 : ℝ)|=(5264894121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s8_2 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336229327/2500000000 : ℝ)*x 0 + (658111819/1250000000 : ℝ)*x 1 + (-451492881/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336229327/2500000000 : ℝ)^8283 ≤ (43508912041163/100000000000000 : ℝ)^6235 := by
    have hnat : (1336229327 : ℕ)^8283*100000000000000^6235 ≤ 43508912041163^6235*2500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336229327 2500000000 43508912041163 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658111819/1250000000 : ℝ)^8283 ≤ (42645676841327/100000000000000 : ℝ)^6235 := by
    have hnat : (658111819 : ℕ)^8283*100000000000000^6235 ≤ 42645676841327^6235*1250000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658111819 1250000000 42645676841327 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451492881/2000000000 : ℝ)^8283 ≤ (13845411095639/100000000000000 : ℝ)^6235 := by
    have hnat : (451492881 : ℕ)^8283*100000000000000^6235 ≤ 13845411095639^6235*2000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451492881 2000000000 13845411095639 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336229327/2500000000 : ℝ), (658111819/1250000000 : ℝ), (-451492881/2000000000 : ℝ)] ![(43508912041163/100000000000000 : ℝ), (42645676841327/100000000000000 : ℝ), (13845411095639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336229327/2500000000 : ℝ)|^8283 ≤ (43508912041163/100000000000000 : ℝ)^6235
        have hw : |(1336229327/2500000000 : ℝ)|=(1336229327/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658111819/1250000000 : ℝ)|^8283 ≤ (42645676841327/100000000000000 : ℝ)^6235
        have hw : |(658111819/1250000000 : ℝ)|=(658111819/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-451492881/2000000000 : ℝ)|^8283 ≤ (13845411095639/100000000000000 : ℝ)^6235
        have hw : |(-451492881/2000000000 : ℝ)|=(451492881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s8_3 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4372052277/10000000000 : ℝ)*x 0 + (2123431727/5000000000 : ℝ)*x 1 + (1125240041/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4372052277/10000000000 : ℝ)^8283 ≤ (33316691242727/100000000000000 : ℝ)^6235 := by
    have hnat : (4372052277 : ℕ)^8283*100000000000000^6235 ≤ 33316691242727^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4372052277 10000000000 33316691242727 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2123431727/5000000000 : ℝ)^8283 ≤ (32055349384557/100000000000000 : ℝ)^6235 := by
    have hnat : (2123431727 : ℕ)^8283*100000000000000^6235 ≤ 32055349384557^6235*5000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2123431727 5000000000 32055349384557 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125240041/2500000000 : ℝ)^8283 ≤ (34627959364481/100000000000000 : ℝ)^6235 := by
    have hnat : (1125240041 : ℕ)^8283*100000000000000^6235 ≤ 34627959364481^6235*2500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125240041 2500000000 34627959364481 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4372052277/10000000000 : ℝ), (2123431727/5000000000 : ℝ), (1125240041/2500000000 : ℝ)] ![(33316691242727/100000000000000 : ℝ), (32055349384557/100000000000000 : ℝ), (34627959364481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4372052277/10000000000 : ℝ)|^8283 ≤ (33316691242727/100000000000000 : ℝ)^6235
        have hw : |(4372052277/10000000000 : ℝ)|=(4372052277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2123431727/5000000000 : ℝ)|^8283 ≤ (32055349384557/100000000000000 : ℝ)^6235
        have hw : |(2123431727/5000000000 : ℝ)|=(2123431727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125240041/2500000000 : ℝ)|^8283 ≤ (34627959364481/100000000000000 : ℝ)^6235
        have hw : |(1125240041/2500000000 : ℝ)|=(1125240041/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s8_4 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-8768031/40000000 : ℝ)*x 0 + (5265217489/10000000000 : ℝ)*x 1 + (337100277/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8768031/40000000 : ℝ)^8283 ≤ (13314644944981/100000000000000 : ℝ)^6235 := by
    have hnat : (8768031 : ℕ)^8283*100000000000000^6235 ≤ 13314644944981^6235*40000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8768031 40000000 13314644944981 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265217489/10000000000 : ℝ)^8283 ≤ (8529830374523/20000000000000 : ℝ)^6235 := by
    have hnat : (5265217489 : ℕ)^8283*20000000000000^6235 ≤ 8529830374523^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265217489 10000000000 8529830374523 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337100277/625000000 : ℝ)^8283 ≤ (44036203172119/100000000000000 : ℝ)^6235 := by
    have hnat : (337100277 : ℕ)^8283*100000000000000^6235 ≤ 44036203172119^6235*625000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337100277 625000000 44036203172119 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-8768031/40000000 : ℝ), (5265217489/10000000000 : ℝ), (337100277/625000000 : ℝ)] ![(13314644944981/100000000000000 : ℝ), (8529830374523/20000000000000 : ℝ), (44036203172119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-8768031/40000000 : ℝ)|^8283 ≤ (13314644944981/100000000000000 : ℝ)^6235
        have hw : |(-8768031/40000000 : ℝ)|=(8768031/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265217489/10000000000 : ℝ)|^8283 ≤ (8529830374523/20000000000000 : ℝ)^6235
        have hw : |(5265217489/10000000000 : ℝ)|=(5265217489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337100277/625000000 : ℝ)|^8283 ≤ (44036203172119/100000000000000 : ℝ)^6235
        have hw : |(337100277/625000000 : ℝ)|=(337100277/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s8_5 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1328088703/2500000000 : ℝ)*x 0 + (-2128754197/10000000000 : ℝ)*x 1 + (5393604431/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1328088703/2500000000 : ℝ)^8283 ≤ (43157132338877/100000000000000 : ℝ)^6235 := by
    have hnat : (1328088703 : ℕ)^8283*100000000000000^6235 ≤ 43157132338877^6235*2500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1328088703 2500000000 43157132338877 100000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2128754197/10000000000 : ℝ)^8283 ≤ (2561332897651/20000000000000 : ℝ)^6235 := by
    have hnat : (2128754197 : ℕ)^8283*20000000000000^6235 ≤ 2561332897651^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128754197 10000000000 2561332897651 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393604431/10000000000 : ℝ)^8283 ≤ (5504525395159/12500000000000 : ℝ)^6235 := by
    have hnat : (5393604431 : ℕ)^8283*12500000000000^6235 ≤ 5504525395159^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393604431 10000000000 5504525395159 12500000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1328088703/2500000000 : ℝ), (-2128754197/10000000000 : ℝ), (5393604431/10000000000 : ℝ)] ![(43157132338877/100000000000000 : ℝ), (2561332897651/20000000000000 : ℝ), (5504525395159/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1328088703/2500000000 : ℝ)|^8283 ≤ (43157132338877/100000000000000 : ℝ)^6235
        have hw : |(1328088703/2500000000 : ℝ)|=(1328088703/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2128754197/10000000000 : ℝ)|^8283 ≤ (2561332897651/20000000000000 : ℝ)^6235
        have hw : |(-2128754197/10000000000 : ℝ)|=(2128754197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393604431/10000000000 : ℝ)|^8283 ≤ (5504525395159/12500000000000 : ℝ)^6235
        have hw : |(5393604431/10000000000 : ℝ)|=(5393604431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s8_6 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312354903/10000000000 : ℝ)*x 0 + (269680223/500000000 : ℝ)*x 1 + (-425750807/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312354903/10000000000 : ℝ)^8283 ≤ (21578566660491/50000000000000 : ℝ)^6235 := by
    have hnat : (5312354903 : ℕ)^8283*50000000000000^6235 ≤ 21578566660491^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312354903 10000000000 21578566660491 50000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269680223/500000000 : ℝ)^8283 ≤ (8807240695163/20000000000000 : ℝ)^6235 := by
    have hnat : (269680223 : ℕ)^8283*20000000000000^6235 ≤ 8807240695163^6235*500000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269680223 500000000 8807240695163 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (425750807/2000000000 : ℝ)^8283 ≤ (3201665798383/25000000000000 : ℝ)^6235 := by
    have hnat : (425750807 : ℕ)^8283*25000000000000^6235 ≤ 3201665798383^6235*2000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425750807 2000000000 3201665798383 25000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312354903/10000000000 : ℝ), (269680223/500000000 : ℝ), (-425750807/2000000000 : ℝ)] ![(21578566660491/50000000000000 : ℝ), (8807240695163/20000000000000 : ℝ), (3201665798383/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312354903/10000000000 : ℝ)|^8283 ≤ (21578566660491/50000000000000 : ℝ)^6235
        have hw : |(5312354903/10000000000 : ℝ)|=(5312354903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269680223/500000000 : ℝ)|^8283 ≤ (8807240695163/20000000000000 : ℝ)^6235
        have hw : |(269680223/500000000 : ℝ)|=(269680223/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-425750807/2000000000 : ℝ)|^8283 ≤ (3201665798383/25000000000000 : ℝ)^6235
        have hw : |(-425750807/2000000000 : ℝ)|=(425750807/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1090_s8_7 (p : ℝ) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174882489/400000000 : ℝ)*x 0 + (4500322971/10000000000 : ℝ)*x 1 + (4247502851/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174882489/400000000 : ℝ)^8283 ≤ (6663358390131/20000000000000 : ℝ)^6235 := by
    have hnat : (174882489 : ℕ)^8283*20000000000000^6235 ≤ 6663358390131^6235*400000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174882489 400000000 6663358390131 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4500322971/10000000000 : ℝ)^8283 ≤ (6924289414597/20000000000000 : ℝ)^6235 := by
    have hnat : (4500322971 : ℕ)^8283*20000000000000^6235 ≤ 6924289414597^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500322971 10000000000 6924289414597 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4247502851/10000000000 : ℝ)^8283 ≤ (6412352191989/20000000000000 : ℝ)^6235 := by
    have hnat : (4247502851 : ℕ)^8283*20000000000000^6235 ≤ 6412352191989^6235*10000000000^8283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247502851 10000000000 6412352191989 20000000000000 8283 6235 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8283/2048 : ℝ)) 8283 6235 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174882489/400000000 : ℝ), (4500322971/10000000000 : ℝ), (4247502851/10000000000 : ℝ)] ![(6663358390131/20000000000000 : ℝ), (6924289414597/20000000000000 : ℝ), (6412352191989/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174882489/400000000 : ℝ)|^8283 ≤ (6663358390131/20000000000000 : ℝ)^6235
        have hw : |(174882489/400000000 : ℝ)|=(174882489/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4500322971/10000000000 : ℝ)|^8283 ≤ (6924289414597/20000000000000 : ℝ)^6235
        have hw : |(4500322971/10000000000 : ℝ)|=(4500322971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4247502851/10000000000 : ℝ)|^8283 ≤ (6412352191989/20000000000000 : ℝ)^6235
        have hw : |(4247502851/10000000000 : ℝ)|=(4247502851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1090_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2821/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7009/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (701/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11283/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (701/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11283/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (701/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11283/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (701/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11283/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (701/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11283/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (701/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11283/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11283/100000 : ℝ) ^ (4141/1024 : ℝ) ≤ (1840631575647343/12500000000000000000 : ℝ) := by
    have hpowers : (11283/100000 : ℝ)^4141 ≤ (1840631575647343/12500000000000000000 : ℝ)^1024 := by
      have hnat : (11283 : ℕ)^4141*12500000000000000000^1024 ≤ 1840631575647343^1024*100000^4141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11283 100000 1840631575647343 12500000000000000000 4141 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11283/100000 : ℝ)) (X := (1840631575647343/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (701/5000 : ℝ) ^ (4141/1024 : ℝ) ≤ (4430019545387183/12500000000000000000 : ℝ) := by
    have hpowers : (701/5000 : ℝ)^4141 ≤ (4430019545387183/12500000000000000000 : ℝ)^1024 := by
      have hnat : (701 : ℕ)^4141*12500000000000000000^1024 ≤ 4430019545387183^1024*5000^4141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701 5000 4430019545387183 12500000000000000000 4141 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (701/5000 : ℝ)) (X := (4430019545387183/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251840631575647343/6250000000000000000 : ℝ) ≤ (12500910213891/12500000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (6251840631575647343/6250000000000000000 : ℝ)^1024 ≤ (12500910213891/12500000000000 : ℝ)^4141 := by
      have hnat : (6251840631575647343 : ℕ)^1024*12500000000000^4141 ≤ 12500910213891^4141*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251840631575647343 6250000000000000000 12500910213891 12500000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12500910213891/12500000000000 : ℝ)) (X := (6251840631575647343/6250000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6253135325560517263/6250000000000000000 : ℝ) ≤ (5000620133763289/5000000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (6253135325560517263/6250000000000000000 : ℝ)^1024 ≤ (5000620133763289/5000000000000000 : ℝ)^4141 := by
      have hnat : (6253135325560517263 : ℕ)^1024*5000000000000000^4141 ≤ 5000620133763289^4141*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6253135325560517263 6250000000000000000 5000620133763289 5000000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000620133763289/5000000000000000 : ℝ)) (X := (6253135325560517263/6250000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254430019545387183/6250000000000000000 : ℝ) ≤ (2500438090985089/2500000000000000 : ℝ) ^ (4141/1024 : ℝ) := by
    have hpowers : (6254430019545387183/6250000000000000000 : ℝ)^1024 ≤ (2500438090985089/2500000000000000 : ℝ)^4141 := by
      have hnat : (6254430019545387183 : ℕ)^1024*2500000000000000^4141 ≤ 2500438090985089^4141*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254430019545387183 6250000000000000000 2500438090985089 2500000000000000 1024 4141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500438090985089/2500000000000000 : ℝ)) (X := (6254430019545387183/6250000000000000000 : ℝ)) (by norm_num) 4141 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1840631575647343/12500000000000000000 : ℝ) ≤ ((6840109259165604813/6842500000000000000 : ℝ)+2*(256048206889/136850000000000 : ℝ)*(11283/100000 : ℝ))^(4141/1024 : ℝ) := by
    rw [show (6840109259165604813/6842500000000000000 : ℝ)+2*(256048206889/136850000000000 : ℝ)*(11283/100000 : ℝ)=(12500910213891/12500000000000 : ℝ) by norm_num, show 1+2*(1840631575647343/12500000000000000000 : ℝ)=(6251840631575647343/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4430019545387183/12500000000000000000 : ℝ)+(1840631575647343/12500000000000000000 : ℝ) ≤ ((6840109259165604813/6842500000000000000 : ℝ)+(256048206889/136850000000000 : ℝ)*((701/5000 : ℝ)+(11283/100000 : ℝ)))^(4141/1024 : ℝ) := by
    rw [show (6840109259165604813/6842500000000000000 : ℝ)+(256048206889/136850000000000 : ℝ)*((701/5000 : ℝ)+(11283/100000 : ℝ))=(5000620133763289/5000000000000000 : ℝ) by norm_num, show 1+(4430019545387183/12500000000000000000 : ℝ)+(1840631575647343/12500000000000000000 : ℝ)=(6253135325560517263/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4430019545387183/12500000000000000000 : ℝ) ≤ ((6840109259165604813/6842500000000000000 : ℝ)+2*(256048206889/136850000000000 : ℝ)*(701/5000 : ℝ))^(4141/1024 : ℝ) := by
    rw [show (6840109259165604813/6842500000000000000 : ℝ)+2*(256048206889/136850000000000 : ℝ)*(701/5000 : ℝ)=(2500438090985089/2500000000000000 : ℝ) by norm_num, show 1+2*(4430019545387183/12500000000000000000 : ℝ)=(6254430019545387183/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6840109259165604813/6842500000000000000 : ℝ)*(X 1 0+X 2 0)+(256048206889/136850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (6840109259165604813/6842500000000000000 : ℝ)) (alpha := (256048206889/136850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6840109259165604813/6842500000000000000 : ℝ)*(X 0 1+X 2 1)+(256048206889/136850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (6840109259165604813/6842500000000000000 : ℝ)) (alpha := (256048206889/136850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6840109259165604813/6842500000000000000 : ℝ)*(X 0 2+X 1 2)+(256048206889/136850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4141/1024 : ℝ)) (lo := (11283/100000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (6840109259165604813/6842500000000000000 : ℝ)) (alpha := (256048206889/136850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-274000357/1250000000 : ℝ)*X 0 0+(2696964629/5000000000 : ℝ)*X 0 1+(1052978749/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344917693/10000000000 : ℝ)*X 1 0+(-141091529/625000000 : ℝ)*X 1 1+(5264894121/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336229327/2500000000 : ℝ)*X 2 0+(658111819/1250000000 : ℝ)*X 2 1+(-451492881/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4372052277/10000000000 : ℝ)*X 0 0+(2123431727/5000000000 : ℝ)*X 0 1+(1125240041/2500000000 : ℝ)*X 0 2+(4372052277/10000000000 : ℝ)*X 1 0+(2123431727/5000000000 : ℝ)*X 1 1+(1125240041/2500000000 : ℝ)*X 1 2+(4372052277/10000000000 : ℝ)*X 2 0+(2123431727/5000000000 : ℝ)*X 2 1+(1125240041/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-8768031/40000000 : ℝ)*X 0 0+(5265217489/10000000000 : ℝ)*X 0 1+(337100277/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1328088703/2500000000 : ℝ)*X 1 0+(-2128754197/10000000000 : ℝ)*X 1 1+(5393604431/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312354903/10000000000 : ℝ)*X 2 0+(269680223/500000000 : ℝ)*X 2 1+(-425750807/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174882489/400000000 : ℝ)*X 0 0+(4500322971/10000000000 : ℝ)*X 0 1+(4247502851/10000000000 : ℝ)*X 0 2+(174882489/400000000 : ℝ)*X 1 0+(4500322971/10000000000 : ℝ)*X 1 1+(4247502851/10000000000 : ℝ)*X 1 2+(174882489/400000000 : ℝ)*X 2 0+(4500322971/10000000000 : ℝ)*X 2 1+(4247502851/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1090_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (71561961467202705799803261/6109375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1107303497/50000000000000 : ℝ)*(base19) + (1646865309/100000000000000 : ℝ)*(base23) + (1015863/20000000000000 : ℝ)*(lower2) + (287599811/100000000000000 : ℝ)*(upper3) + (53641011/20000000000000 : ℝ)*(upper5) + (730347769861157/12500000000000 : ℝ)*(major0) + (730347769861157/12500000000000 : ℝ)*(major1) + (730347769861157/12500000000000 : ℝ)*(major2) + (7749892417505947/100000000000000 : ℝ)*(sp0) + (3874985985353653/50000000000000 : ℝ)*(sp1) + (7749972538448991/100000000000000 : ℝ)*(sp2) + (3935550731878101/100000000000000 : ℝ)*(sp3) + (81767808353/100000000000000 : ℝ)*(sp4) + (19505068603/50000000000000 : ℝ)*(sp7) + (3935589742015307/100000000000000 : ℝ)*(f.failure) + (7749974185314299/100000000000000 : ℝ)*(f.sum) + (7326968120451/1955000000000000000000000000 : ℝ)*base66 + (89865540591411413/12218750000000000000000000000000 : ℝ)*base67 + (214932425179776087/12218750000000000000000000000000 : ℝ)*base70 + (46087817443223913/12218750000000000000000000000000 : ℝ)*base71 + (1568983605043/244375000000000000000000000 : ℝ)*base73 + (129928121175557337/12218750000000000000000000000000 : ℝ)*base76 + (47220847834786413/12218750000000000000000000000000 : ℝ)*base77 + (249715943441442663/12218750000000000000000000000000 : ℝ)*base79 + (5233297174801/1955000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (14591099/10000000000000000000000 : ℝ)*base90 + (14591099/10000000000000000000000 : ℝ)*base92 + (14591099/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1519221974465638829377562547/171062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1674428331/100000000000000 : ℝ)*(base19) + (212558523/10000000000000 : ℝ)*(base23) + (546103537/100000000000000 : ℝ)*(lower1) + (224425499/100000000000000 : ℝ)*(upper3) + (106882449/100000000000000 : ℝ)*(lower4) + (83805459/50000000000000 : ℝ)*(upper5) + (5872134829035927/100000000000000 : ℝ)*(major0) + (5872134829035927/100000000000000 : ℝ)*(major1) + (5872134829035927/100000000000000 : ℝ)*(major2) + (19012436197/100000000000000 : ℝ)*(sp2) + (3894454102791421/50000000000000 : ℝ)*(sp4) + (7788906531154511/100000000000000 : ℝ)*(sp5) + (3894443533780707/50000000000000 : ℝ)*(sp6) + (1977680578226281/50000000000000 : ℝ)*(sp7) + (1977680578226281/50000000000000 : ℝ)*(f.failure) + (3894454102791421/50000000000000 : ℝ)*(f.sum) + (956575708659/855312500000000000000000000 : ℝ)*base66 + (4082621469628038093/97750000000000000000000000000000 : ℝ)*base67 + (85899178301538093/97750000000000000000000000000000 : ℝ)*base69 + (6099301529797538093/97750000000000000000000000000000 : ℝ)*base71 + (79625040941769/13685000000000000000000000000 : ℝ)*base74 + (2400532914219788093/97750000000000000000000000000000 : ℝ)*base75 + (30868766766038093/97750000000000000000000000000000 : ℝ)*base77 + (860643091718461907/97750000000000000000000000000000 : ℝ)*base80 + (29315039004889/13685000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (13618183/5000000000000000000000 : ℝ)*base89 + (13618183/5000000000000000000000 : ℝ)*base91 + (13618183/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1090_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11283/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1090_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1090_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1090_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1090_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1090_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4141/1024 : ℝ) ≤ p) (hpb : p ≤ (8283/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148460143/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3517/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2809/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2821/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7009/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1090_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
