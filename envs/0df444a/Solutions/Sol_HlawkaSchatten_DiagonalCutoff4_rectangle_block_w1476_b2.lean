-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1476_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:12:25.025625+00:00
-- url     : https://prove2.me/submissions/a96a405c-ef74-40ac-89ae-44c4a4974ab1

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
theorem support_rectangle_w1476_s6_0 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1922542027/10000000000 : ℝ)*x 0 + (679744871/1250000000 : ℝ)*x 1 + (651949811/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1922542027/10000000000 : ℝ)^4449 ≤ (11742765837667/100000000000000 : ℝ)^3425 := by
    have hnat : (1922542027 : ℕ)^4449*100000000000000^3425 ≤ 11742765837667^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922542027 10000000000 11742765837667 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (679744871/1250000000 : ℝ)^4449 ≤ (45324921609229/100000000000000 : ℝ)^3425 := by
    have hnat : (679744871 : ℕ)^4449*100000000000000^3425 ≤ 45324921609229^3425*1250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      679744871 1250000000 45324921609229 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (651949811/1250000000 : ℝ)^4449 ≤ (10733078133967/25000000000000 : ℝ)^3425 := by
    have hnat : (651949811 : ℕ)^4449*25000000000000^3425 ≤ 10733078133967^3425*1250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      651949811 1250000000 10733078133967 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1922542027/10000000000 : ℝ), (679744871/1250000000 : ℝ), (651949811/1250000000 : ℝ)] ![(11742765837667/100000000000000 : ℝ), (45324921609229/100000000000000 : ℝ), (10733078133967/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1922542027/10000000000 : ℝ)|^4449 ≤ (11742765837667/100000000000000 : ℝ)^3425
        have hw : |(-1922542027/10000000000 : ℝ)|=(1922542027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(679744871/1250000000 : ℝ)|^4449 ≤ (45324921609229/100000000000000 : ℝ)^3425
        have hw : |(679744871/1250000000 : ℝ)|=(679744871/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(651949811/1250000000 : ℝ)|^4449 ≤ (10733078133967/25000000000000 : ℝ)^3425
        have hw : |(651949811/1250000000 : ℝ)|=(651949811/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s6_1 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353515897/10000000000 : ℝ)*x 0 + (-2036506829/10000000000 : ℝ)*x 1 + (32597499/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353515897/10000000000 : ℝ)^4449 ≤ (11103199351827/25000000000000 : ℝ)^3425 := by
    have hnat : (5353515897 : ℕ)^4449*25000000000000^3425 ≤ 11103199351827^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353515897 10000000000 11103199351827 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2036506829/10000000000 : ℝ)^4449 ≤ (12654875590251/100000000000000 : ℝ)^3425 := by
    have hnat : (2036506829 : ℕ)^4449*100000000000000^3425 ≤ 12654875590251^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036506829 10000000000 12654875590251 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32597499/62500000 : ℝ)^4449 ≤ (21466163496109/50000000000000 : ℝ)^3425 := by
    have hnat : (32597499 : ℕ)^4449*50000000000000^3425 ≤ 21466163496109^3425*62500000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32597499 62500000 21466163496109 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353515897/10000000000 : ℝ), (-2036506829/10000000000 : ℝ), (32597499/62500000 : ℝ)] ![(11103199351827/25000000000000 : ℝ), (12654875590251/100000000000000 : ℝ), (21466163496109/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353515897/10000000000 : ℝ)|^4449 ≤ (11103199351827/25000000000000 : ℝ)^3425
        have hw : |(5353515897/10000000000 : ℝ)|=(5353515897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2036506829/10000000000 : ℝ)|^4449 ≤ (12654875590251/100000000000000 : ℝ)^3425
        have hw : |(-2036506829/10000000000 : ℝ)|=(2036506829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32597499/62500000 : ℝ)|^4449 ≤ (21466163496109/50000000000000 : ℝ)^3425
        have hw : |(32597499/62500000 : ℝ)|=(32597499/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s6_2 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353509627/10000000000 : ℝ)*x 0 + (2607802509/5000000000 : ℝ)*x 1 + (-101825417/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353509627/10000000000 : ℝ)^4449 ≤ (22206364919867/50000000000000 : ℝ)^3425 := by
    have hnat : (5353509627 : ℕ)^4449*50000000000000^3425 ≤ 22206364919867^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353509627 10000000000 22206364919867 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2607802509/5000000000 : ℝ)^4449 ≤ (2146619117917/5000000000000 : ℝ)^3425 := by
    have hnat : (2607802509 : ℕ)^4449*5000000000000^3425 ≤ 2146619117917^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2607802509 5000000000 2146619117917 5000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (101825417/500000000 : ℝ)^4449 ≤ (12654887786839/100000000000000 : ℝ)^3425 := by
    have hnat : (101825417 : ℕ)^4449*100000000000000^3425 ≤ 12654887786839^3425*500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      101825417 500000000 12654887786839 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353509627/10000000000 : ℝ), (2607802509/5000000000 : ℝ), (-101825417/500000000 : ℝ)] ![(22206364919867/50000000000000 : ℝ), (2146619117917/5000000000000 : ℝ), (12654887786839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353509627/10000000000 : ℝ)|^4449 ≤ (22206364919867/50000000000000 : ℝ)^3425
        have hw : |(5353509627/10000000000 : ℝ)|=(5353509627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2607802509/5000000000 : ℝ)|^4449 ≤ (2146619117917/5000000000000 : ℝ)^3425
        have hw : |(2607802509/5000000000 : ℝ)|=(2607802509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-101825417/500000000 : ℝ)|^4449 ≤ (12654887786839/100000000000000 : ℝ)^3425
        have hw : |(-101825417/500000000 : ℝ)|=(101825417/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s6_3 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (857366753/2000000000 : ℝ)*x 0 + (161890887/400000000 : ℝ)*x 1 + (1134682511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (857366753/2000000000 : ℝ)^4449 ≤ (6655543863333/20000000000000 : ℝ)^3425 := by
    have hnat : (857366753 : ℕ)^4449*20000000000000^3425 ≤ 6655543863333^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      857366753 2000000000 6655543863333 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161890887/400000000 : ℝ)^4449 ≤ (15441254422851/50000000000000 : ℝ)^3425 := by
    have hnat : (161890887 : ℕ)^4449*50000000000000^3425 ≤ 15441254422851^3425*400000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161890887 400000000 15441254422851 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1134682511/2500000000 : ℝ)^4449 ≤ (35839771834509/100000000000000 : ℝ)^3425 := by
    have hnat : (1134682511 : ℕ)^4449*100000000000000^3425 ≤ 35839771834509^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134682511 2500000000 35839771834509 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(857366753/2000000000 : ℝ), (161890887/400000000 : ℝ), (1134682511/2500000000 : ℝ)] ![(6655543863333/20000000000000 : ℝ), (15441254422851/50000000000000 : ℝ), (35839771834509/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(857366753/2000000000 : ℝ)|^4449 ≤ (6655543863333/20000000000000 : ℝ)^3425
        have hw : |(857366753/2000000000 : ℝ)|=(857366753/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161890887/400000000 : ℝ)|^4449 ≤ (15441254422851/50000000000000 : ℝ)^3425
        have hw : |(161890887/400000000 : ℝ)|=(161890887/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1134682511/2500000000 : ℝ)|^4449 ≤ (35839771834509/100000000000000 : ℝ)^3425
        have hw : |(1134682511/2500000000 : ℝ)|=(1134682511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s6_4 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-7510049/39062500 : ℝ)*x 0 + (5216736469/10000000000 : ℝ)*x 1 + (1359203167/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (7510049/39062500 : ℝ)^4449 ≤ (1467875995307/12500000000000 : ℝ)^3425 := by
    have hnat : (7510049 : ℕ)^4449*12500000000000^3425 ≤ 1467875995307^3425*39062500^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7510049 39062500 1467875995307 12500000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216736469/10000000000 : ℝ)^4449 ≤ (8588896174057/20000000000000 : ℝ)^3425 := by
    have hnat : (5216736469 : ℕ)^4449*20000000000000^3425 ≤ 8588896174057^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216736469 10000000000 8588896174057 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359203167/2500000000 : ℝ)^4449 ≤ (45312511158023/100000000000000 : ℝ)^3425 := by
    have hnat : (1359203167 : ℕ)^4449*100000000000000^3425 ≤ 45312511158023^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359203167 2500000000 45312511158023 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-7510049/39062500 : ℝ), (5216736469/10000000000 : ℝ), (1359203167/2500000000 : ℝ)] ![(1467875995307/12500000000000 : ℝ), (8588896174057/20000000000000 : ℝ), (45312511158023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-7510049/39062500 : ℝ)|^4449 ≤ (1467875995307/12500000000000 : ℝ)^3425
        have hw : |(-7510049/39062500 : ℝ)|=(7510049/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216736469/10000000000 : ℝ)|^4449 ≤ (8588896174057/20000000000000 : ℝ)^3425
        have hw : |(5216736469/10000000000 : ℝ)|=(5216736469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359203167/2500000000 : ℝ)|^4449 ≤ (45312511158023/100000000000000 : ℝ)^3425
        have hw : |(1359203167/2500000000 : ℝ)|=(1359203167/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s6_5 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647741289/5000000000 : ℝ)*x 0 + (-363059299/2000000000 : ℝ)*x 1 + (5436812637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647741289/5000000000 : ℝ)^4449 ≤ (2736776703373/6250000000000 : ℝ)^3425 := by
    have hnat : (2647741289 : ℕ)^4449*6250000000000^3425 ≤ 2736776703373^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647741289 5000000000 2736776703373 6250000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (363059299/2000000000 : ℝ)^4449 ≤ (10899061914669/100000000000000 : ℝ)^3425 := by
    have hnat : (363059299 : ℕ)^4449*100000000000000^3425 ≤ 10899061914669^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      363059299 2000000000 10899061914669 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5436812637/10000000000 : ℝ)^4449 ≤ (45312510822411/100000000000000 : ℝ)^3425 := by
    have hnat : (5436812637 : ℕ)^4449*100000000000000^3425 ≤ 45312510822411^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436812637 10000000000 45312510822411 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647741289/5000000000 : ℝ), (-363059299/2000000000 : ℝ), (5436812637/10000000000 : ℝ)] ![(2736776703373/6250000000000 : ℝ), (10899061914669/100000000000000 : ℝ), (45312510822411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647741289/5000000000 : ℝ)|^4449 ≤ (2736776703373/6250000000000 : ℝ)^3425
        have hw : |(2647741289/5000000000 : ℝ)|=(2647741289/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-363059299/2000000000 : ℝ)|^4449 ≤ (10899061914669/100000000000000 : ℝ)^3425
        have hw : |(-363059299/2000000000 : ℝ)|=(363059299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5436812637/10000000000 : ℝ)|^4449 ≤ (45312510822411/100000000000000 : ℝ)^3425
        have hw : |(5436812637/10000000000 : ℝ)|=(5436812637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s6_6 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647741281/5000000000 : ℝ)*x 0 + (5436812647/10000000000 : ℝ)*x 1 + (-907648251/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647741281/5000000000 : ℝ)^4449 ≤ (43788427082107/100000000000000 : ℝ)^3425 := by
    have hnat : (2647741281 : ℕ)^4449*100000000000000^3425 ≤ 43788427082107^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647741281 5000000000 43788427082107 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5436812647/10000000000 : ℝ)^4449 ≤ (45312510930673/100000000000000 : ℝ)^3425 := by
    have hnat : (5436812647 : ℕ)^4449*100000000000000^3425 ≤ 45312510930673^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5436812647 10000000000 45312510930673 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (907648251/5000000000 : ℝ)^4449 ≤ (10899061969263/100000000000000 : ℝ)^3425 := by
    have hnat : (907648251 : ℕ)^4449*100000000000000^3425 ≤ 10899061969263^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907648251 5000000000 10899061969263 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647741281/5000000000 : ℝ), (5436812647/10000000000 : ℝ), (-907648251/5000000000 : ℝ)] ![(43788427082107/100000000000000 : ℝ), (45312510930673/100000000000000 : ℝ), (10899061969263/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647741281/5000000000 : ℝ)|^4449 ≤ (43788427082107/100000000000000 : ℝ)^3425
        have hw : |(2647741281/5000000000 : ℝ)|=(2647741281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5436812647/10000000000 : ℝ)|^4449 ≤ (45312510930673/100000000000000 : ℝ)^3425
        have hw : |(5436812647/10000000000 : ℝ)|=(5436812647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-907648251/5000000000 : ℝ)|^4449 ≤ (10899061969263/100000000000000 : ℝ)^3425
        have hw : |(-907648251/5000000000 : ℝ)|=(907648251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_s6_7 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2143452177/5000000000 : ℝ)*x 0 + (4536213169/10000000000 : ℝ)*x 1 + (1012451129/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143452177/5000000000 : ℝ)^4449 ≤ (33278431114791/100000000000000 : ℝ)^3425 := by
    have hnat : (2143452177 : ℕ)^4449*100000000000000^3425 ≤ 33278431114791^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143452177 5000000000 33278431114791 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4536213169/10000000000 : ℝ)^4449 ≤ (7162791530677/20000000000000 : ℝ)^3425 := by
    have hnat : (4536213169 : ℕ)^4449*20000000000000^3425 ≤ 7162791530677^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4536213169 10000000000 7162791530677 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1012451129/2500000000 : ℝ)^4449 ≤ (3863451402443/12500000000000 : ℝ)^3425 := by
    have hnat : (1012451129 : ℕ)^4449*12500000000000^3425 ≤ 3863451402443^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1012451129 2500000000 3863451402443 12500000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2143452177/5000000000 : ℝ), (4536213169/10000000000 : ℝ), (1012451129/2500000000 : ℝ)] ![(33278431114791/100000000000000 : ℝ), (7162791530677/20000000000000 : ℝ), (3863451402443/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2143452177/5000000000 : ℝ)|^4449 ≤ (33278431114791/100000000000000 : ℝ)^3425
        have hw : |(2143452177/5000000000 : ℝ)|=(2143452177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4536213169/10000000000 : ℝ)|^4449 ≤ (7162791530677/20000000000000 : ℝ)^3425
        have hw : |(4536213169/10000000000 : ℝ)|=(4536213169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1012451129/2500000000 : ℝ)|^4449 ≤ (3863451402443/12500000000000 : ℝ)^3425
        have hw : |(1012451129/2500000000 : ℝ)|=(1012451129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1476_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10769/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7737/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10767/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10767/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10767/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3869/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10767/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10767/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3869/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10767/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (10767/100000 : ℝ) ^ (4447/1024 : ℝ) ≤ (6260465546689381/100000000000000000000 : ℝ) := by
    have hpowers : (10767/100000 : ℝ)^4447 ≤ (6260465546689381/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10767 : ℕ)^4447*100000000000000000000^1024 ≤ 6260465546689381^1024*100000^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10767 100000 6260465546689381 100000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10767/100000 : ℝ)) (X := (6260465546689381/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3869/25000 : ℝ) ^ (4447/1024 : ℝ) ≤ (30260173827041729/100000000000000000000 : ℝ) := by
    have hpowers : (3869/25000 : ℝ)^4447 ≤ (30260173827041729/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3869 : ℕ)^4447*100000000000000000000^1024 ≤ 30260173827041729^1024*25000^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3869 25000 30260173827041729 100000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3869/25000 : ℝ)) (X := (30260173827041729/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006260465546689381/50000000000000000000 : ℝ) ≤ (5000144151288907/5000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (50006260465546689381/50000000000000000000 : ℝ)^1024 ≤ (5000144151288907/5000000000000000 : ℝ)^4447 := by
      have hnat : (50006260465546689381 : ℕ)^1024*5000000000000000^4447 ≤ 5000144151288907^4447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006260465546689381 50000000000000000000 5000144151288907 5000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000144151288907/5000000000000000 : ℝ)) (X := (50006260465546689381/50000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003652063937373111/10000000000000000000 : ℝ) ≤ (1000084083380873/1000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (10003652063937373111/10000000000000000000 : ℝ)^1024 ≤ (1000084083380873/1000000000000000 : ℝ)^4447 := by
      have hnat : (10003652063937373111 : ℕ)^1024*1000000000000000^4447 ≤ 1000084083380873^4447*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003652063937373111 10000000000000000000 1000084083380873 1000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000084083380873/1000000000000000 : ℝ)) (X := (10003652063937373111/10000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50030260173827041729/50000000000000000000 : ℝ) ≤ (5000696682519823/5000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (50030260173827041729/50000000000000000000 : ℝ)^1024 ≤ (5000696682519823/5000000000000000 : ℝ)^4447 := by
      have hnat : (50030260173827041729 : ℕ)^1024*5000000000000000^4447 ≤ 5000696682519823^4447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50030260173827041729 50000000000000000000 5000696682519823 5000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000696682519823/5000000000000000 : ℝ)) (X := (50030260173827041729/50000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6260465546689381/100000000000000000000 : ℝ) ≤ ((23539729704656190491/23545000000000000000 : ℝ)+2*(138132807729/117725000000000 : ℝ)*(10767/100000 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (23539729704656190491/23545000000000000000 : ℝ)+2*(138132807729/117725000000000 : ℝ)*(10767/100000 : ℝ)=(5000144151288907/5000000000000000 : ℝ) by norm_num, show 1+2*(6260465546689381/100000000000000000000 : ℝ)=(50006260465546689381/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30260173827041729/100000000000000000000 : ℝ)+(6260465546689381/100000000000000000000 : ℝ) ≤ ((23539729704656190491/23545000000000000000 : ℝ)+(138132807729/117725000000000 : ℝ)*((3869/25000 : ℝ)+(10767/100000 : ℝ)))^(4447/1024 : ℝ) := by
    rw [show (23539729704656190491/23545000000000000000 : ℝ)+(138132807729/117725000000000 : ℝ)*((3869/25000 : ℝ)+(10767/100000 : ℝ))=(1000084083380873/1000000000000000 : ℝ) by norm_num, show 1+(30260173827041729/100000000000000000000 : ℝ)+(6260465546689381/100000000000000000000 : ℝ)=(10003652063937373111/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30260173827041729/100000000000000000000 : ℝ) ≤ ((23539729704656190491/23545000000000000000 : ℝ)+2*(138132807729/117725000000000 : ℝ)*(3869/25000 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (23539729704656190491/23545000000000000000 : ℝ)+2*(138132807729/117725000000000 : ℝ)*(3869/25000 : ℝ)=(5000696682519823/5000000000000000 : ℝ) by norm_num, show 1+2*(30260173827041729/100000000000000000000 : ℝ)=(50030260173827041729/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (23539729704656190491/23545000000000000000 : ℝ)*(X 1 0+X 2 0)+(138132807729/117725000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (10767/100000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (23539729704656190491/23545000000000000000 : ℝ)) (alpha := (138132807729/117725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (23539729704656190491/23545000000000000000 : ℝ)*(X 0 1+X 2 1)+(138132807729/117725000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (10767/100000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (23539729704656190491/23545000000000000000 : ℝ)) (alpha := (138132807729/117725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (23539729704656190491/23545000000000000000 : ℝ)*(X 0 2+X 1 2)+(138132807729/117725000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (10767/100000 : ℝ)) (hi := (3869/25000 : ℝ)) (c := (23539729704656190491/23545000000000000000 : ℝ)) (alpha := (138132807729/117725000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1922542027/10000000000 : ℝ)*X 0 0+(679744871/1250000000 : ℝ)*X 0 1+(651949811/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5353515897/10000000000 : ℝ)*X 1 0+(-2036506829/10000000000 : ℝ)*X 1 1+(32597499/62500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353509627/10000000000 : ℝ)*X 2 0+(2607802509/5000000000 : ℝ)*X 2 1+(-101825417/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((857366753/2000000000 : ℝ)*X 0 0+(161890887/400000000 : ℝ)*X 0 1+(1134682511/2500000000 : ℝ)*X 0 2+(857366753/2000000000 : ℝ)*X 1 0+(161890887/400000000 : ℝ)*X 1 1+(1134682511/2500000000 : ℝ)*X 1 2+(857366753/2000000000 : ℝ)*X 2 0+(161890887/400000000 : ℝ)*X 2 1+(1134682511/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-7510049/39062500 : ℝ)*X 0 0+(5216736469/10000000000 : ℝ)*X 0 1+(1359203167/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2647741289/5000000000 : ℝ)*X 1 0+(-363059299/2000000000 : ℝ)*X 1 1+(5436812637/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647741281/5000000000 : ℝ)*X 2 0+(5436812647/10000000000 : ℝ)*X 2 1+(-907648251/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2143452177/5000000000 : ℝ)*X 0 0+(4536213169/10000000000 : ℝ)*X 0 1+(1012451129/2500000000 : ℝ)*X 0 2+(2143452177/5000000000 : ℝ)*X 1 0+(4536213169/10000000000 : ℝ)*X 1 1+(1012451129/2500000000 : ℝ)*X 1 2+(2143452177/5000000000 : ℝ)*X 2 0+(4536213169/10000000000 : ℝ)*X 2 1+(1012451129/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3033574163209044366583947183/588625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (501000713/50000000000000 : ℝ)*(base21) + (284436059/20000000000000 : ℝ)*(upper2) + (148801917/50000000000000 : ℝ)*(lower3) + (833018023/100000000000000 : ℝ)*(lower4) + (3266104079261271/100000000000000 : ℝ)*(major0) + (3266104079261271/100000000000000 : ℝ)*(major1) + (3266104079261271/100000000000000 : ℝ)*(major2) + (562163786790849/12500000000000 : ℝ)*(sp0) + (2248675617046219/50000000000000 : ℝ)*(sp1) + (2248683651884417/50000000000000 : ℝ)*(sp2) + (508703153991801/25000000000000 : ℝ)*(sp3) + (14502860867/25000000000000 : ℝ)*(sp4) + (8535838911/50000000000000 : ℝ)*(sp5) + (5412999269/20000000000000 : ℝ)*(sp7) + (508709920240887/25000000000000 : ℝ)*(f.failure) + (224868415288513/5000000000000 : ℝ)*(f.sum) + (182331233919697/11772500000000000000000000000 : ℝ)*base66 + (1923106818308074061/2354500000000000000000000000000000 : ℝ)*base67 + (30718487363075425939/2354500000000000000000000000000000 : ℝ)*base70 + (8448418683517425939/2354500000000000000000000000000000 : ℝ)*base72 + (105670382686849/23545000000000000000000000000 : ℝ)*base74 + (13057155451338425939/2354500000000000000000000000000000 : ℝ)*base76 + (25803656954239425939/2354500000000000000000000000000000 : ℝ)*base78 + (7485248829479925939/2354500000000000000000000000000000 : ℝ)*base80 + (6026622899149/1471562500000000000000000000 : ℝ)*base82 + (124377/62500000000000000000 : ℝ)*base90 + (124377/62500000000000000000 : ℝ)*base92 + (124377/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28599667577129716561767/11772500000000000000000000000 : ℝ) := by norm_num
    linear_combination (440830237/100000000000000 : ℝ)*(base19) + (493878791/100000000000000 : ℝ)*(base23) + (135495933/100000000000000 : ℝ)*(lower1) + (25788581/50000000000000 : ℝ)*(upper3) + (6530127/20000000000000 : ℝ)*(lower4) + (4037871/6250000000000 : ℝ)*(upper5) + (1649938938948571/50000000000000 : ℝ)*(major0) + (1649938938948571/50000000000000 : ℝ)*(major1) + (1649938938948571/50000000000000 : ℝ)*(major2) + (467252363/100000000000000 : ℝ)*(sp2) + (908774865908161/20000000000000 : ℝ)*(sp4) + (567984236088821/12500000000000 : ℝ)*(sp5) + (90877467368193/2000000000000 : ℝ)*(sp6) + (1027940672637357/50000000000000 : ℝ)*(sp7) + (1027940672637357/50000000000000 : ℝ)*(f.failure) + (908774865908161/20000000000000 : ℝ)*(f.sum) + (19173238922113/5886250000000000000000000000 : ℝ)*base65 + (35340413880019711639/1177250000000000000000000000000000 : ℝ)*base68 + (12137051774688961639/1177250000000000000000000000000000 : ℝ)*base70 + (52336210669004961639/1177250000000000000000000000000000 : ℝ)*base72 + (32959350411651/11772500000000000000000000000 : ℝ)*base73 + (90883000793340038361/1177250000000000000000000000000000 : ℝ)*base75 + (2902669569926788361/1177250000000000000000000000000000 : ℝ)*base77 + (19913951973692538361/1177250000000000000000000000000000 : ℝ)*base79 + (31568598019201/2943125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1417253/125000000000000000000 : ℝ)*base89 + (1417253/125000000000000000000 : ℝ)*base91 + (1417253/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1476_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1476_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1476_box_0 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1702244659/10000000000 : ℝ)*x 0 + (1351683737/2500000000 : ℝ)*x 1 + (2703367463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1702244659/10000000000 : ℝ)^4449 ≤ (10025692755463/100000000000000 : ℝ)^3425 := by
    have hnat : (1702244659 : ℕ)^4449*100000000000000^3425 ≤ 10025692755463^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1702244659 10000000000 10025692755463 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351683737/2500000000 : ℝ)^4449 ≤ (8997430746317/20000000000000 : ℝ)^3425 := by
    have hnat : (1351683737 : ℕ)^4449*20000000000000^3425 ≤ 8997430746317^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351683737 2500000000 8997430746317 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703367463/5000000000 : ℝ)^4449 ≤ (44987153493803/100000000000000 : ℝ)^3425 := by
    have hnat : (2703367463 : ℕ)^4449*100000000000000^3425 ≤ 44987153493803^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703367463 5000000000 44987153493803 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1702244659/10000000000 : ℝ), (1351683737/2500000000 : ℝ), (2703367463/5000000000 : ℝ)] ![(10025692755463/100000000000000 : ℝ), (8997430746317/20000000000000 : ℝ), (44987153493803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1702244659/10000000000 : ℝ)|^4449 ≤ (10025692755463/100000000000000 : ℝ)^3425
        have hw : |(-1702244659/10000000000 : ℝ)|=(1702244659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351683737/2500000000 : ℝ)|^4449 ≤ (8997430746317/20000000000000 : ℝ)^3425
        have hw : |(1351683737/2500000000 : ℝ)|=(1351683737/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703367463/5000000000 : ℝ)|^4449 ≤ (44987153493803/100000000000000 : ℝ)^3425
        have hw : |(2703367463/5000000000 : ℝ)|=(2703367463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_1 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2635072771/5000000000 : ℝ)*x 0 + (-945705883/5000000000 : ℝ)*x 1 + (2703367473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2635072771/5000000000 : ℝ)^4449 ≤ (21758235092469/50000000000000 : ℝ)^3425 := by
    have hnat : (2635072771 : ℕ)^4449*50000000000000^3425 ≤ 21758235092469^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2635072771 5000000000 21758235092469 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (945705883/5000000000 : ℝ)^4449 ≤ (2299275219/20000000000 : ℝ)^3425 := by
    have hnat : (945705883 : ℕ)^4449*20000000000^3425 ≤ 2299275219^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945705883 5000000000 2299275219 20000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703367473/5000000000 : ℝ)^4449 ≤ (2811697106873/6250000000000 : ℝ)^3425 := by
    have hnat : (2703367473 : ℕ)^4449*6250000000000^3425 ≤ 2811697106873^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703367473 5000000000 2811697106873 6250000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2635072771/5000000000 : ℝ), (-945705883/5000000000 : ℝ), (2703367473/5000000000 : ℝ)] ![(21758235092469/50000000000000 : ℝ), (2299275219/20000000000 : ℝ), (2811697106873/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2635072771/5000000000 : ℝ)|^4449 ≤ (21758235092469/50000000000000 : ℝ)^3425
        have hw : |(2635072771/5000000000 : ℝ)|=(2635072771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-945705883/5000000000 : ℝ)|^4449 ≤ (2299275219/20000000000 : ℝ)^3425
        have hw : |(-945705883/5000000000 : ℝ)|=(945705883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703367473/5000000000 : ℝ)|^4449 ≤ (2811697106873/6250000000000 : ℝ)^3425
        have hw : |(2703367473/5000000000 : ℝ)|=(2703367473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_2 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5270146003/10000000000 : ℝ)*x 0 + (5406734073/10000000000 : ℝ)*x 1 + (-945706167/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5270146003/10000000000 : ℝ)^4449 ≤ (1359889847799/3125000000000 : ℝ)^3425 := by
    have hnat : (5270146003 : ℕ)^4449*3125000000000^3425 ≤ 1359889847799^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5270146003 10000000000 1359889847799 3125000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406734073/10000000000 : ℝ)^4449 ≤ (44987144274369/100000000000000 : ℝ)^3425 := by
    have hnat : (5406734073 : ℕ)^4449*100000000000000^3425 ≤ 44987144274369^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406734073 10000000000 44987144274369 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (945706167/5000000000 : ℝ)^4449 ≤ (5748190289807/50000000000000 : ℝ)^3425 := by
    have hnat : (945706167 : ℕ)^4449*50000000000000^3425 ≤ 5748190289807^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      945706167 5000000000 5748190289807 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5270146003/10000000000 : ℝ), (5406734073/10000000000 : ℝ), (-945706167/5000000000 : ℝ)] ![(1359889847799/3125000000000 : ℝ), (44987144274369/100000000000000 : ℝ), (5748190289807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5270146003/10000000000 : ℝ)|^4449 ≤ (1359889847799/3125000000000 : ℝ)^3425
        have hw : |(5270146003/10000000000 : ℝ)|=(5270146003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406734073/10000000000 : ℝ)|^4449 ≤ (44987144274369/100000000000000 : ℝ)^3425
        have hw : |(5406734073/10000000000 : ℝ)|=(5406734073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-945706167/5000000000 : ℝ)|^4449 ≤ (5748190289807/50000000000000 : ℝ)^3425
        have hw : |(-945706167/5000000000 : ℝ)|=(945706167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_3 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (112291081/250000000 : ℝ)*x 0 + (2095830483/5000000000 : ℝ)*x 1 + (838332213/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (112291081/250000000 : ℝ)^4449 ≤ (35357539608367/100000000000000 : ℝ)^3425 := by
    have hnat : (112291081 : ℕ)^4449*100000000000000^3425 ≤ 35357539608367^3425*250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112291081 250000000 35357539608367 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2095830483/5000000000 : ℝ)^4449 ≤ (8080307424511/25000000000000 : ℝ)^3425 := by
    have hnat : (2095830483 : ℕ)^4449*25000000000000^3425 ≤ 8080307424511^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095830483 5000000000 8080307424511 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (838332213/2000000000 : ℝ)^4449 ≤ (32321230689649/100000000000000 : ℝ)^3425 := by
    have hnat : (838332213 : ℕ)^4449*100000000000000^3425 ≤ 32321230689649^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838332213 2000000000 32321230689649 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(112291081/250000000 : ℝ), (2095830483/5000000000 : ℝ), (838332213/2000000000 : ℝ)] ![(35357539608367/100000000000000 : ℝ), (8080307424511/25000000000000 : ℝ), (32321230689649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(112291081/250000000 : ℝ)|^4449 ≤ (35357539608367/100000000000000 : ℝ)^3425
        have hw : |(112291081/250000000 : ℝ)|=(112291081/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2095830483/5000000000 : ℝ)|^4449 ≤ (8080307424511/25000000000000 : ℝ)^3425
        have hw : |(2095830483/5000000000 : ℝ)|=(2095830483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(838332213/2000000000 : ℝ)|^4449 ≤ (32321230689649/100000000000000 : ℝ)^3425
        have hw : |(838332213/2000000000 : ℝ)|=(838332213/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_4 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-429662039/2000000000 : ℝ)*x 0 + (5242265707/10000000000 : ℝ)*x 1 + (655283293/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429662039/2000000000 : ℝ)^4449 ≤ (13564650701821/100000000000000 : ℝ)^3425 := by
    have hnat : (429662039 : ℕ)^4449*100000000000000^3425 ≤ 13564650701821^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429662039 2000000000 13564650701821 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242265707/10000000000 : ℝ)^4449 ≤ (10804417808101/25000000000000 : ℝ)^3425 := by
    have hnat : (5242265707 : ℕ)^4449*25000000000000^3425 ≤ 10804417808101^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242265707 10000000000 10804417808101 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655283293/1250000000 : ℝ)^4449 ≤ (21608839026981/50000000000000 : ℝ)^3425 := by
    have hnat : (655283293 : ℕ)^4449*50000000000000^3425 ≤ 21608839026981^3425*1250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655283293 1250000000 21608839026981 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429662039/2000000000 : ℝ), (5242265707/10000000000 : ℝ), (655283293/1250000000 : ℝ)] ![(13564650701821/100000000000000 : ℝ), (10804417808101/25000000000000 : ℝ), (21608839026981/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429662039/2000000000 : ℝ)|^4449 ≤ (13564650701821/100000000000000 : ℝ)^3425
        have hw : |(-429662039/2000000000 : ℝ)|=(429662039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242265707/10000000000 : ℝ)|^4449 ≤ (10804417808101/25000000000000 : ℝ)^3425
        have hw : |(5242265707/10000000000 : ℝ)|=(5242265707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655283293/1250000000 : ℝ)|^4449 ≤ (21608839026981/50000000000000 : ℝ)^3425
        have hw : |(655283293/1250000000 : ℝ)|=(655283293/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_5 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346243883/2500000000 : ℝ)*x 0 + (-1958669661/10000000000 : ℝ)*x 1 + (327641651/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346243883/2500000000 : ℝ)^4449 ≤ (11188028552103/25000000000000 : ℝ)^3425 := by
    have hnat : (1346243883 : ℕ)^4449*25000000000000^3425 ≤ 11188028552103^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346243883 2500000000 11188028552103 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1958669661/10000000000 : ℝ)^4449 ≤ (12030206954561/100000000000000 : ℝ)^3425 := by
    have hnat : (1958669661 : ℕ)^4449*100000000000000^3425 ≤ 12030206954561^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1958669661 10000000000 12030206954561 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (327641651/625000000 : ℝ)^4449 ≤ (21608839412501/50000000000000 : ℝ)^3425 := by
    have hnat : (327641651 : ℕ)^4449*50000000000000^3425 ≤ 21608839412501^3425*625000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327641651 625000000 21608839412501 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346243883/2500000000 : ℝ), (-1958669661/10000000000 : ℝ), (327641651/625000000 : ℝ)] ![(11188028552103/25000000000000 : ℝ), (12030206954561/100000000000000 : ℝ), (21608839412501/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346243883/2500000000 : ℝ)|^4449 ≤ (11188028552103/25000000000000 : ℝ)^3425
        have hw : |(1346243883/2500000000 : ℝ)|=(1346243883/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1958669661/10000000000 : ℝ)|^4449 ≤ (12030206954561/100000000000000 : ℝ)^3425
        have hw : |(-1958669661/10000000000 : ℝ)|=(1958669661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(327641651/625000000 : ℝ)|^4449 ≤ (21608839412501/50000000000000 : ℝ)^3425
        have hw : |(327641651/625000000 : ℝ)|=(327641651/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_6 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346244003/2500000000 : ℝ)*x 0 + (5242266011/10000000000 : ℝ)*x 1 + (-979334777/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346244003/2500000000 : ℝ)^4449 ≤ (44752119390119/100000000000000 : ℝ)^3425 := by
    have hnat : (1346244003 : ℕ)^4449*100000000000000^3425 ≤ 44752119390119^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346244003 2500000000 44752119390119 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242266011/10000000000 : ℝ)^4449 ≤ (1350552327747/3125000000000 : ℝ)^3425 := by
    have hnat : (5242266011 : ℕ)^4449*3125000000000^3425 ≤ 1350552327747^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242266011 10000000000 1350552327747 3125000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979334777/5000000000 : ℝ)^4449 ≤ (3007551525219/25000000000000 : ℝ)^3425 := by
    have hnat : (979334777 : ℕ)^4449*25000000000000^3425 ≤ 3007551525219^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979334777 5000000000 3007551525219 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346244003/2500000000 : ℝ), (5242266011/10000000000 : ℝ), (-979334777/5000000000 : ℝ)] ![(44752119390119/100000000000000 : ℝ), (1350552327747/3125000000000 : ℝ), (3007551525219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346244003/2500000000 : ℝ)|^4449 ≤ (44752119390119/100000000000000 : ℝ)^3425
        have hw : |(1346244003/2500000000 : ℝ)|=(1346244003/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242266011/10000000000 : ℝ)|^4449 ≤ (1350552327747/3125000000000 : ℝ)^3425
        have hw : |(5242266011/10000000000 : ℝ)|=(5242266011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-979334777/5000000000 : ℝ)|^4449 ≤ (3007551525219/25000000000000 : ℝ)^3425
        have hw : |(-979334777/5000000000 : ℝ)|=(979334777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_7 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1019948337/2500000000 : ℝ)*x 0 + (4397446617/10000000000 : ℝ)*x 1 + (439744683/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019948337/2500000000 : ℝ)^4449 ≤ (6241047656299/20000000000000 : ℝ)^3425 := by
    have hnat : (1019948337 : ℕ)^4449*20000000000000^3425 ≤ 6241047656299^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019948337 2500000000 6241047656299 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4397446617/10000000000 : ℝ)^4449 ≤ (2149836235889/6250000000000 : ℝ)^3425 := by
    have hnat : (4397446617 : ℕ)^4449*6250000000000^3425 ≤ 2149836235889^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4397446617 10000000000 2149836235889 6250000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (439744683/1000000000 : ℝ)^4449 ≤ (8599345484617/25000000000000 : ℝ)^3425 := by
    have hnat : (439744683 : ℕ)^4449*25000000000000^3425 ≤ 8599345484617^3425*1000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      439744683 1000000000 8599345484617 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1019948337/2500000000 : ℝ), (4397446617/10000000000 : ℝ), (439744683/1000000000 : ℝ)] ![(6241047656299/20000000000000 : ℝ), (2149836235889/6250000000000 : ℝ), (8599345484617/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1019948337/2500000000 : ℝ)|^4449 ≤ (6241047656299/20000000000000 : ℝ)^3425
        have hw : |(1019948337/2500000000 : ℝ)|=(1019948337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4397446617/10000000000 : ℝ)|^4449 ≤ (2149836235889/6250000000000 : ℝ)^3425
        have hw : |(4397446617/10000000000 : ℝ)|=(4397446617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(439744683/1000000000 : ℝ)|^4449 ≤ (8599345484617/25000000000000 : ℝ)^3425
        have hw : |(439744683/1000000000 : ℝ)|=(439744683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_8 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-410851019/2000000000 : ℝ)*x 0 + (1025490973/2000000000 : ℝ)*x 1 + (339205689/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (410851019/2000000000 : ℝ)^4449 ≤ (1599790430489/12500000000000 : ℝ)^3425 := by
    have hnat : (410851019 : ℕ)^4449*12500000000000^3425 ≤ 1599790430489^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410851019 2000000000 1599790430489 12500000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1025490973/2000000000 : ℝ)^4449 ≤ (1679688860239/4000000000000 : ℝ)^3425 := by
    have hnat : (1025490973 : ℕ)^4449*4000000000000^3425 ≤ 1679688860239^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1025490973 2000000000 1679688860239 4000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339205689/625000000 : ℝ)^4449 ≤ (45209455042223/100000000000000 : ℝ)^3425 := by
    have hnat : (339205689 : ℕ)^4449*100000000000000^3425 ≤ 45209455042223^3425*625000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339205689 625000000 45209455042223 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-410851019/2000000000 : ℝ), (1025490973/2000000000 : ℝ), (339205689/625000000 : ℝ)] ![(1599790430489/12500000000000 : ℝ), (1679688860239/4000000000000 : ℝ), (45209455042223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-410851019/2000000000 : ℝ)|^4449 ≤ (1599790430489/12500000000000 : ℝ)^3425
        have hw : |(-410851019/2000000000 : ℝ)|=(410851019/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1025490973/2000000000 : ℝ)|^4449 ≤ (1679688860239/4000000000000 : ℝ)^3425
        have hw : |(1025490973/2000000000 : ℝ)|=(1025490973/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339205689/625000000 : ℝ)|^4449 ≤ (45209455042223/100000000000000 : ℝ)^3425
        have hw : |(339205689/625000000 : ℝ)|=(339205689/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_9 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1313946409/2500000000 : ℝ)*x 0 + (-1882749879/10000000000 : ℝ)*x 1 + (43418329/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1313946409/2500000000 : ℝ)^4449 ≤ (2710156896987/6250000000000 : ℝ)^3425 := by
    have hnat : (1313946409 : ℕ)^4449*6250000000000^3425 ≤ 2710156896987^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1313946409 2500000000 2710156896987 6250000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1882749879/10000000000 : ℝ)^4449 ≤ (11428033497311/100000000000000 : ℝ)^3425 := by
    have hnat : (1882749879 : ℕ)^4449*100000000000000^3425 ≤ 11428033497311^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882749879 10000000000 11428033497311 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43418329/80000000 : ℝ)^4449 ≤ (9041891227019/20000000000000 : ℝ)^3425 := by
    have hnat : (43418329 : ℕ)^4449*20000000000000^3425 ≤ 9041891227019^3425*80000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43418329 80000000 9041891227019 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1313946409/2500000000 : ℝ), (-1882749879/10000000000 : ℝ), (43418329/80000000 : ℝ)] ![(2710156896987/6250000000000 : ℝ), (11428033497311/100000000000000 : ℝ), (9041891227019/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1313946409/2500000000 : ℝ)|^4449 ≤ (2710156896987/6250000000000 : ℝ)^3425
        have hw : |(1313946409/2500000000 : ℝ)|=(1313946409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1882749879/10000000000 : ℝ)|^4449 ≤ (11428033497311/100000000000000 : ℝ)^3425
        have hw : |(-1882749879/10000000000 : ℝ)|=(1882749879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43418329/80000000 : ℝ)|^4449 ≤ (9041891227019/20000000000000 : ℝ)^3425
        have hw : |(43418329/80000000 : ℝ)|=(43418329/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_10 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051157177/2000000000 : ℝ)*x 0 + (339205683/625000000 : ℝ)*x 1 + (-1882749811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051157177/2000000000 : ℝ)^4449 ≤ (21681256510179/50000000000000 : ℝ)^3425 := by
    have hnat : (1051157177 : ℕ)^4449*50000000000000^3425 ≤ 21681256510179^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051157177 2000000000 21681256510179 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339205683/625000000 : ℝ)^4449 ≤ (45209454003453/100000000000000 : ℝ)^3425 := by
    have hnat : (339205683 : ℕ)^4449*100000000000000^3425 ≤ 45209454003453^3425*625000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339205683 625000000 45209454003453 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1882749811/10000000000 : ℝ)^4449 ≤ (11428032961157/100000000000000 : ℝ)^3425 := by
    have hnat : (1882749811 : ℕ)^4449*100000000000000^3425 ≤ 11428032961157^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1882749811 10000000000 11428032961157 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051157177/2000000000 : ℝ), (339205683/625000000 : ℝ), (-1882749811/10000000000 : ℝ)] ![(21681256510179/50000000000000 : ℝ), (45209454003453/100000000000000 : ℝ), (11428032961157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051157177/2000000000 : ℝ)|^4449 ≤ (21681256510179/50000000000000 : ℝ)^3425
        have hw : |(1051157177/2000000000 : ℝ)|=(1051157177/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339205683/625000000 : ℝ)|^4449 ≤ (45209454003453/100000000000000 : ℝ)^3425
        have hw : |(339205683/625000000 : ℝ)|=(339205683/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1882749811/10000000000 : ℝ)|^4449 ≤ (11428032961157/100000000000000 : ℝ)^3425
        have hw : |(-1882749811/10000000000 : ℝ)|=(1882749811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_11 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4541963077/10000000000 : ℝ)*x 0 + (2082954551/5000000000 : ℝ)*x 1 + (2082954597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4541963077/10000000000 : ℝ)^4449 ≤ (35872937528289/100000000000000 : ℝ)^3425 := by
    have hnat : (4541963077 : ℕ)^4449*100000000000000^3425 ≤ 35872937528289^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4541963077 10000000000 35872937528289 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2082954551/5000000000 : ℝ)^4449 ≤ (32063530769221/100000000000000 : ℝ)^3425 := by
    have hnat : (2082954551 : ℕ)^4449*100000000000000^3425 ≤ 32063530769221^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082954551 5000000000 32063530769221 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2082954597/5000000000 : ℝ)^4449 ≤ (4007941461127/12500000000000 : ℝ)^3425 := by
    have hnat : (2082954597 : ℕ)^4449*12500000000000^3425 ≤ 4007941461127^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2082954597 5000000000 4007941461127 12500000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4541963077/10000000000 : ℝ), (2082954551/5000000000 : ℝ), (2082954597/5000000000 : ℝ)] ![(35872937528289/100000000000000 : ℝ), (32063530769221/100000000000000 : ℝ), (4007941461127/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4541963077/10000000000 : ℝ)|^4449 ≤ (35872937528289/100000000000000 : ℝ)^3425
        have hw : |(4541963077/10000000000 : ℝ)|=(4541963077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2082954551/5000000000 : ℝ)|^4449 ≤ (32063530769221/100000000000000 : ℝ)^3425
        have hw : |(2082954551/5000000000 : ℝ)|=(2082954551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2082954597/5000000000 : ℝ)|^4449 ≤ (4007941461127/12500000000000 : ℝ)^3425
        have hw : |(2082954597/5000000000 : ℝ)|=(2082954597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_12 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-898227561/5000000000 : ℝ)*x 0 + (1103544563/2000000000 : ℝ)*x 1 + (5227279399/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (898227561/5000000000 : ℝ)^4449 ≤ (10752345090571/100000000000000 : ℝ)^3425 := by
    have hnat : (898227561 : ℕ)^4449*100000000000000^3425 ≤ 10752345090571^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      898227561 5000000000 10752345090571 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103544563/2000000000 : ℝ)^4449 ≤ (5773800206059/12500000000000 : ℝ)^3425 := by
    have hnat : (1103544563 : ℕ)^4449*12500000000000^3425 ≤ 5773800206059^3425*2000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103544563 2000000000 5773800206059 12500000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227279399/10000000000 : ℝ)^4449 ≤ (430572532479/1000000000000 : ℝ)^3425 := by
    have hnat : (5227279399 : ℕ)^4449*1000000000000^3425 ≤ 430572532479^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227279399 10000000000 430572532479 1000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-898227561/5000000000 : ℝ), (1103544563/2000000000 : ℝ), (5227279399/10000000000 : ℝ)] ![(10752345090571/100000000000000 : ℝ), (5773800206059/12500000000000 : ℝ), (430572532479/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-898227561/5000000000 : ℝ)|^4449 ≤ (10752345090571/100000000000000 : ℝ)^3425
        have hw : |(-898227561/5000000000 : ℝ)|=(898227561/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1103544563/2000000000 : ℝ)|^4449 ≤ (5773800206059/12500000000000 : ℝ)^3425
        have hw : |(1103544563/2000000000 : ℝ)|=(1103544563/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227279399/10000000000 : ℝ)|^4449 ≤ (430572532479/1000000000000 : ℝ)^3425
        have hw : |(5227279399/10000000000 : ℝ)|=(5227279399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_13 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1348859423/2500000000 : ℝ)*x 0 + (-49115369/250000000 : ℝ)*x 1 + (5227279191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1348859423/2500000000 : ℝ)^4449 ≤ (11216272088709/25000000000000 : ℝ)^3425 := by
    have hnat : (1348859423 : ℕ)^4449*25000000000000^3425 ≤ 11216272088709^3425*2500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348859423 2500000000 11216272088709 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (49115369/250000000 : ℝ)^4449 ≤ (6038830306273/50000000000000 : ℝ)^3425 := by
    have hnat : (49115369 : ℕ)^4449*50000000000000^3425 ≤ 6038830306273^3425*250000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      49115369 250000000 6038830306273 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5227279191/10000000000 : ℝ)^4449 ≤ (21528625511179/50000000000000 : ℝ)^3425 := by
    have hnat : (5227279191 : ℕ)^4449*50000000000000^3425 ≤ 21528625511179^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5227279191 10000000000 21528625511179 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1348859423/2500000000 : ℝ), (-49115369/250000000 : ℝ), (5227279191/10000000000 : ℝ)] ![(11216272088709/25000000000000 : ℝ), (6038830306273/50000000000000 : ℝ), (21528625511179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1348859423/2500000000 : ℝ)|^4449 ≤ (11216272088709/25000000000000 : ℝ)^3425
        have hw : |(1348859423/2500000000 : ℝ)|=(1348859423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-49115369/250000000 : ℝ)|^4449 ≤ (6038830306273/50000000000000 : ℝ)^3425
        have hw : |(-49115369/250000000 : ℝ)|=(49115369/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5227279191/10000000000 : ℝ)|^4449 ≤ (21528625511179/50000000000000 : ℝ)^3425
        have hw : |(5227279191/10000000000 : ℝ)|=(5227279191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_14 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2697719541/5000000000 : ℝ)*x 0 + (261363919/500000000 : ℝ)*x 1 + (-1964613967/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2697719541/5000000000 : ℝ)^4449 ≤ (11216275842227/25000000000000 : ℝ)^3425 := by
    have hnat : (2697719541 : ℕ)^4449*25000000000000^3425 ≤ 11216275842227^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697719541 5000000000 11216275842227 25000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (261363919/500000000 : ℝ)^4449 ≤ (8611448468977/20000000000000 : ℝ)^3425 := by
    have hnat : (261363919 : ℕ)^4449*20000000000000^3425 ≤ 8611448468977^3425*500000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261363919 500000000 8611448468977 20000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1964613967/10000000000 : ℝ)^4449 ≤ (1207765427997/10000000000000 : ℝ)^3425 := by
    have hnat : (1964613967 : ℕ)^4449*10000000000000^3425 ≤ 1207765427997^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1964613967 10000000000 1207765427997 10000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2697719541/5000000000 : ℝ), (261363919/500000000 : ℝ), (-1964613967/10000000000 : ℝ)] ![(11216275842227/25000000000000 : ℝ), (8611448468977/20000000000000 : ℝ), (1207765427997/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2697719541/5000000000 : ℝ)|^4449 ≤ (11216275842227/25000000000000 : ℝ)^3425
        have hw : |(2697719541/5000000000 : ℝ)|=(2697719541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(261363919/500000000 : ℝ)|^4449 ≤ (8611448468977/20000000000000 : ℝ)^3425
        have hw : |(261363919/500000000 : ℝ)|=(261363919/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1964613967/10000000000 : ℝ)|^4449 ≤ (1207765427997/10000000000000 : ℝ)^3425
        have hw : |(-1964613967/10000000000 : ℝ)|=(1964613967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1476_box_15 (p : ℝ) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4041403593/10000000000 : ℝ)*x 0 + (2208089249/5000000000 : ℝ)*x 1 + (2208088477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4041403593/10000000000 : ℝ)^4449 ≤ (30824353319403/100000000000000 : ℝ)^3425 := by
    have hnat : (4041403593 : ℕ)^4449*100000000000000^3425 ≤ 30824353319403^3425*10000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4041403593 10000000000 30824353319403 100000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2208089249/5000000000 : ℝ)^4449 ≤ (864695779617/2500000000000 : ℝ)^3425 := by
    have hnat : (2208089249 : ℕ)^4449*2500000000000^3425 ≤ 864695779617^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208089249 5000000000 864695779617 2500000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208088477/5000000000 : ℝ)^4449 ≤ (17293907738251/50000000000000 : ℝ)^3425 := by
    have hnat : (2208088477 : ℕ)^4449*50000000000000^3425 ≤ 17293907738251^3425*5000000000^4449 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208088477 5000000000 17293907738251 50000000000000 4449 3425 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4449/1024 : ℝ)) 4449 3425 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4041403593/10000000000 : ℝ), (2208089249/5000000000 : ℝ), (2208088477/5000000000 : ℝ)] ![(30824353319403/100000000000000 : ℝ), (864695779617/2500000000000 : ℝ), (17293907738251/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4041403593/10000000000 : ℝ)|^4449 ≤ (30824353319403/100000000000000 : ℝ)^3425
        have hw : |(4041403593/10000000000 : ℝ)|=(4041403593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2208089249/5000000000 : ℝ)|^4449 ≤ (864695779617/2500000000000 : ℝ)^3425
        have hw : |(2208089249/5000000000 : ℝ)|=(2208089249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2208088477/5000000000 : ℝ)|^4449 ≤ (17293907738251/50000000000000 : ℝ)^3425
        have hw : |(2208088477/5000000000 : ℝ)|=(2208088477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1476_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31849/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58459/100000 : ℝ) ∧ (79923/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (85767/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10769/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10769/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10769/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7737/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10769/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10769/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7737/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10769/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10769/100000 : ℝ) ^ (4447/1024 : ℝ) ≤ (6265517320731197/100000000000000000000 : ℝ) := by
    have hpowers : (10769/100000 : ℝ)^4447 ≤ (6265517320731197/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10769 : ℕ)^4447*100000000000000000000^1024 ≤ 6265517320731197^1024*100000^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10769 100000 6265517320731197 100000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10769/100000 : ℝ)) (X := (6265517320731197/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7737/50000 : ℝ) ^ (4447/1024 : ℝ) ≤ (3024319467259471/10000000000000000000 : ℝ) := by
    have hpowers : (7737/50000 : ℝ)^4447 ≤ (3024319467259471/10000000000000000000 : ℝ)^1024 := by
      have hnat : (7737 : ℕ)^4447*10000000000000000000^1024 ≤ 3024319467259471^1024*50000^4447 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7737 50000 3024319467259471 10000000000000000000 4447 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7737/50000 : ℝ)) (X := (3024319467259471/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006265517320731197/50000000000000000000 : ℝ) ≤ (5000144267603679/5000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (50006265517320731197/50000000000000000000 : ℝ)^1024 ≤ (5000144267603679/5000000000000000 : ℝ)^4447 := by
      have hnat : (50006265517320731197 : ℕ)^1024*5000000000000000^4447 ≤ 5000144267603679^4447*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006265517320731197 50000000000000000000 5000144267603679 5000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000144267603679/5000000000000000 : ℝ)) (X := (50006265517320731197/50000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100036508711993325907/100000000000000000000 : ℝ) ≤ (5000420279618489/5000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (100036508711993325907/100000000000000000000 : ℝ)^1024 ≤ (5000420279618489/5000000000000000 : ℝ)^4447 := by
      have hnat : (100036508711993325907 : ℕ)^1024*5000000000000000^4447 ≤ 5000420279618489^4447*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100036508711993325907 100000000000000000000 5000420279618489 5000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000420279618489/5000000000000000 : ℝ)) (X := (100036508711993325907/100000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003024319467259471/5000000000000000000 : ℝ) ≤ (5000696291633299/5000000000000000 : ℝ) ^ (4447/1024 : ℝ) := by
    have hpowers : (5003024319467259471/5000000000000000000 : ℝ)^1024 ≤ (5000696291633299/5000000000000000 : ℝ)^4447 := by
      have hnat : (5003024319467259471 : ℕ)^1024*5000000000000000^4447 ≤ 5000696291633299^4447*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003024319467259471 5000000000000000000 5000696291633299 5000000000000000 1024 4447 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000696291633299/5000000000000000 : ℝ)) (X := (5003024319467259471/5000000000000000000 : ℝ)) (by norm_num) 4447 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6265517320731197/100000000000000000000 : ℝ) ≤ ((4703946806460066383/4705000000000000000 : ℝ)+2*(27601201481/23525000000000 : ℝ)*(10769/100000 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (4703946806460066383/4705000000000000000 : ℝ)+2*(27601201481/23525000000000 : ℝ)*(10769/100000 : ℝ)=(5000144267603679/5000000000000000 : ℝ) by norm_num, show 1+2*(6265517320731197/100000000000000000000 : ℝ)=(50006265517320731197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3024319467259471/10000000000000000000 : ℝ)+(6265517320731197/100000000000000000000 : ℝ) ≤ ((4703946806460066383/4705000000000000000 : ℝ)+(27601201481/23525000000000 : ℝ)*((7737/50000 : ℝ)+(10769/100000 : ℝ)))^(4447/1024 : ℝ) := by
    rw [show (4703946806460066383/4705000000000000000 : ℝ)+(27601201481/23525000000000 : ℝ)*((7737/50000 : ℝ)+(10769/100000 : ℝ))=(5000420279618489/5000000000000000 : ℝ) by norm_num, show 1+(3024319467259471/10000000000000000000 : ℝ)+(6265517320731197/100000000000000000000 : ℝ)=(100036508711993325907/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3024319467259471/10000000000000000000 : ℝ) ≤ ((4703946806460066383/4705000000000000000 : ℝ)+2*(27601201481/23525000000000 : ℝ)*(7737/50000 : ℝ))^(4447/1024 : ℝ) := by
    rw [show (4703946806460066383/4705000000000000000 : ℝ)+2*(27601201481/23525000000000 : ℝ)*(7737/50000 : ℝ)=(5000696291633299/5000000000000000 : ℝ) by norm_num, show 1+2*(3024319467259471/10000000000000000000 : ℝ)=(5003024319467259471/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4703946806460066383/4705000000000000000 : ℝ)*(X 1 0+X 2 0)+(27601201481/23525000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (10769/100000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (4703946806460066383/4705000000000000000 : ℝ)) (alpha := (27601201481/23525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4703946806460066383/4705000000000000000 : ℝ)*(X 0 1+X 2 1)+(27601201481/23525000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (10769/100000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (4703946806460066383/4705000000000000000 : ℝ)) (alpha := (27601201481/23525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4703946806460066383/4705000000000000000 : ℝ)*(X 0 2+X 1 2)+(27601201481/23525000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4447/1024 : ℝ)) (lo := (10769/100000 : ℝ)) (hi := (7737/50000 : ℝ)) (c := (4703946806460066383/4705000000000000000 : ℝ)) (alpha := (27601201481/23525000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1702244659/10000000000 : ℝ)*X 0 0+(1351683737/2500000000 : ℝ)*X 0 1+(2703367463/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2635072771/5000000000 : ℝ)*X 1 0+(-945705883/5000000000 : ℝ)*X 1 1+(2703367473/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5270146003/10000000000 : ℝ)*X 2 0+(5406734073/10000000000 : ℝ)*X 2 1+(-945706167/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((112291081/250000000 : ℝ)*X 0 0+(2095830483/5000000000 : ℝ)*X 0 1+(838332213/2000000000 : ℝ)*X 0 2+(112291081/250000000 : ℝ)*X 1 0+(2095830483/5000000000 : ℝ)*X 1 1+(838332213/2000000000 : ℝ)*X 1 2+(112291081/250000000 : ℝ)*X 2 0+(2095830483/5000000000 : ℝ)*X 2 1+(838332213/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-429662039/2000000000 : ℝ)*X 0 0+(5242265707/10000000000 : ℝ)*X 0 1+(655283293/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1346243883/2500000000 : ℝ)*X 1 0+(-1958669661/10000000000 : ℝ)*X 1 1+(327641651/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1346244003/2500000000 : ℝ)*X 2 0+(5242266011/10000000000 : ℝ)*X 2 1+(-979334777/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1019948337/2500000000 : ℝ)*X 0 0+(4397446617/10000000000 : ℝ)*X 0 1+(439744683/1000000000 : ℝ)*X 0 2+(1019948337/2500000000 : ℝ)*X 1 0+(4397446617/10000000000 : ℝ)*X 1 1+(439744683/1000000000 : ℝ)*X 1 2+(1019948337/2500000000 : ℝ)*X 2 0+(4397446617/10000000000 : ℝ)*X 2 1+(439744683/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-410851019/2000000000 : ℝ)*X 0 0+(1025490973/2000000000 : ℝ)*X 0 1+(339205689/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1313946409/2500000000 : ℝ)*X 1 0+(-1882749879/10000000000 : ℝ)*X 1 1+(43418329/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1051157177/2000000000 : ℝ)*X 2 0+(339205683/625000000 : ℝ)*X 2 1+(-1882749811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4541963077/10000000000 : ℝ)*X 0 0+(2082954551/5000000000 : ℝ)*X 0 1+(2082954597/5000000000 : ℝ)*X 0 2+(4541963077/10000000000 : ℝ)*X 1 0+(2082954551/5000000000 : ℝ)*X 1 1+(2082954597/5000000000 : ℝ)*X 1 2+(4541963077/10000000000 : ℝ)*X 2 0+(2082954551/5000000000 : ℝ)*X 2 1+(2082954597/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-898227561/5000000000 : ℝ)*X 0 0+(1103544563/2000000000 : ℝ)*X 0 1+(5227279399/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((1348859423/2500000000 : ℝ)*X 1 0+(-49115369/250000000 : ℝ)*X 1 1+(5227279191/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2697719541/5000000000 : ℝ)*X 2 0+(261363919/500000000 : ℝ)*X 2 1+(-1964613967/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4041403593/10000000000 : ℝ)*X 0 0+(2208089249/5000000000 : ℝ)*X 0 1+(2208088477/5000000000 : ℝ)*X 0 2+(4041403593/10000000000 : ℝ)*X 1 0+(2208089249/5000000000 : ℝ)*X 1 1+(2208088477/5000000000 : ℝ)*X 1 2+(4041403593/10000000000 : ℝ)*X 2 0+(2208089249/5000000000 : ℝ)*X 2 1+(2208088477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1476_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31849/50000 : ℝ) ≤ (-149843803338429975592568661390009/235250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (26153243/50000000000000 : ℝ)*(lower2) + (95816657/100000000000000 : ℝ)*(lower3) + (8813357/50000000000000 : ℝ)*(upper5) + (2169703979559859/100000000000000 : ℝ)*(major0) + (2169703979559859/100000000000000 : ℝ)*(major1) + (2169703979559859/100000000000000 : ℝ)*(major2) + (193071/32000000000 : ℝ)*(sp2) + (601774686579853/20000000000000 : ℝ)*(sp4) + (752198761454467/25000000000000 : ℝ)*(sp5) + (3008875870543433/100000000000000 : ℝ)*(sp6) + (67584779262911/5000000000000 : ℝ)*(sp7) + (3040991043/100000000000000 : ℝ)*(sp12) + (81428072441/100000000000000 : ℝ)*(sp13) + (13550616651/20000000000000 : ℝ)*(sp15) + (54070533533659/4000000000000 : ℝ)*(f.failure) + (752219118472577/25000000000000 : ℝ)*(f.sum) + (5463491103323/2352500000000000000000000000 : ℝ)*base65 + (687355158667080003/470500000000000000000000000000000 : ℝ)*base68 + (292918097485580003/470500000000000000000000000000000 : ℝ)*base70 + (403751470826419997/470500000000000000000000000000000 : ℝ)*base71 + (10682079568603/2352500000000000000000000000 : ℝ)*base73 + (2118333886426580003/470500000000000000000000000000000 : ℝ)*base76 + (3872904236579919997/470500000000000000000000000000000 : ℝ)*base77 + (1227948478646080003/470500000000000000000000000000000 : ℝ)*base80 + (10757410163787/2352500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (45411/10000000000000000000 : ℝ)*base89 + (45411/10000000000000000000 : ℝ)*base91 + (45411/10000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58459/100000 : ℝ) ≤ (275061844923247325147888492871/470500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25991499/100000000000000 : ℝ)*(upper1) + (135189389/100000000000000 : ℝ)*(upper2) + (26392499/50000000000000 : ℝ)*(upper4) + (8974002698479/400000000000 : ℝ)*(major0) + (8974002698479/400000000000 : ℝ)*(major1) + (8974002698479/400000000000 : ℝ)*(major2) + (3069773501468263/100000000000000 : ℝ)*(sp0) + (306977148560779/10000000000000 : ℝ)*(sp1) + (3069639832633959/100000000000000 : ℝ)*(sp2) + (698866769580461/50000000000000 : ℝ)*(sp3) + (2698794693/100000000000000 : ℝ)*(sp5) + (5374070741/4000000000000 : ℝ)*(sp10) + (1284895427/20000000000000 : ℝ)*(sp11) + (682934221/100000000000000 : ℝ)*(sp12) + (1397739963638057/100000000000000 : ℝ)*(f.failure) + (767443546100621/25000000000000 : ℝ)*(f.sum) + (350850155791/235250000000000000000000000 : ℝ)*base65 + (7040356787470543/1882000000000000000000000000000 : ℝ)*base68 + (8883563076302543/1882000000000000000000000000000 : ℝ)*base70 + (7844675916410543/1882000000000000000000000000000 : ℝ)*base72 + (1601459683869/941000000000000000000000000 : ℝ)*base74 + (4501798865195457/1882000000000000000000000000000 : ℝ)*base75 + (2467353334182543/1882000000000000000000000000000 : ℝ)*base78 + (8394867508846543/1882000000000000000000000000000 : ℝ)*base80 + (446490531101/941000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1827553/250000000000000000000 : ℝ)*base89 + (1827553/250000000000000000000 : ℝ)*base91 + (1827553/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79923/100000 : ℝ) ≤ (376049486670773305153451391/470500000000000000000000000 : ℝ) := by norm_num
    linear_combination (6732049/100000000000000 : ℝ)*(upper0) + (11240399/100000000000000 : ℝ)*(lower1) + (39766851/100000000000000 : ℝ)*(lower3) + (9624031/20000000000000 : ℝ)*(upper4) + (97656945712513/4000000000000 : ℝ)*(major0) + (97656945712513/4000000000000 : ℝ)*(major1) + (97656945712513/4000000000000 : ℝ)*(major2) + (30264150011/100000000000000 : ℝ)*(sp1) + (1485678011/25000000000000 : ℝ)*(sp2) + (143672387/1562500000000 : ℝ)*(sp3) + (1667578017196311/50000000000000 : ℝ)*(sp8) + (333512577024261/10000000000000 : ℝ)*(sp9) + (1667575045840289/50000000000000 : ℝ)*(sp10) + (380260055554301/25000000000000 : ℝ)*(sp11) + (380262354312493/25000000000000 : ℝ)*(f.failure) + (1667578017196311/50000000000000 : ℝ)*(f.sum) + (2355882048701/470500000000000000000000000 : ℝ)*base65 + (61631090698969521/18820000000000000000000000000000 : ℝ)*base68 + (188510744735329521/18820000000000000000000000000000 : ℝ)*base70 + (30297359385350479/18820000000000000000000000000000 : ℝ)*base71 + (128568503439/47050000000000000000000000 : ℝ)*base73 + (15923467663710479/18820000000000000000000000000000 : ℝ)*base75 + (57847065541449521/18820000000000000000000000000000 : ℝ)*base78 + (2705727348910479/18820000000000000000000000000000 : ℝ)*base79 + (2701429432769/470500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (98397/62500000000000000000 : ℝ)*base89 + (98397/62500000000000000000 : ℝ)*base91 + (98397/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-85767/100000 : ℝ) ≤ (-10088074311155170050751200734031/11762500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122501117/25000000000000 : ℝ)*(lower2) + (985889/1562500000000 : ℝ)*(upper3) + (91103379/100000000000000 : ℝ)*(upper5) + (123981966005181/5000000000000 : ℝ)*(major0) + (123981966005181/5000000000000 : ℝ)*(major1) + (123981966005181/5000000000000 : ℝ)*(major2) + (2036079331/25000000000000 : ℝ)*(sp0) + (187403436361/100000000000000 : ℝ)*(sp5) + (35293308131/20000000000000 : ℝ)*(sp6) + (92531185219/100000000000000 : ℝ)*(sp7) + (344300028413479/10000000000000 : ℝ)*(sp12) + (430352628126969/12500000000000 : ℝ)*(sp13) + (3442831961911459/100000000000000 : ℝ)*(sp14) + (386191479519843/25000000000000 : ℝ)*(sp15) + (154485844926459/10000000000000 : ℝ)*(f.failure) + (1721504214226057/50000000000000 : ℝ)*(f.sum) + (1297712698527/117625000000000000000000000 : ℝ)*base66 + (35395045018894677/23525000000000000000000000000000 : ℝ)*base68 + (36747203465169677/23525000000000000000000000000000 : ℝ)*base70 + (83514893704030323/23525000000000000000000000000000 : ℝ)*base71 + (3050553034491/470500000000000000000000000 : ℝ)*base74 + (181176173556480323/23525000000000000000000000000000 : ℝ)*base75 + (132241469379519677/23525000000000000000000000000000 : ℝ)*base78 + (58220426174969677/23525000000000000000000000000000 : ℝ)*base80 + (5775594122859/941000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (103389/25000000000000000000 : ℝ)*base90 + (103389/25000000000000000000 : ℝ)*base92 + (103389/25000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1476_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7737/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10769/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31849/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58459/100000 : ℝ) else (79923/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85767/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1476_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1476_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31849/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58459/100000 : ℝ) else (79923/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85767/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1476_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1476_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4447/1024 : ℝ) ≤ p) (hpb : p ≤ (4449/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4012729/2500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3869/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10767/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31849/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58459/100000 : ℝ) else (79923/100000 : ℝ) ≤ X j i ∧ X j i ≤ (85767/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1476_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
