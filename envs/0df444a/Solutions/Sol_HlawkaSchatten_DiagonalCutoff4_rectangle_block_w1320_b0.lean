-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1320_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:42:59.123995+00:00
-- url     : https://prove2.me/submissions/f208b495-3693-497f-8a7d-0396e2508b1c

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
theorem support_rectangle_w1320_s0_0 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-36444473/200000000 : ℝ)*x 0 + (4692557/7812500 : ℝ)*x 1 + (240281647/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (36444473/200000000 : ℝ)^535 ≤ (2666881020539/25000000000000 : ℝ)^407 := by
    have hnat : (36444473 : ℕ)^535*25000000000000^407 ≤ 2666881020539^407*200000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      36444473 200000000 2666881020539 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4692557/7812500 : ℝ)^535 ≤ (12791933466723/25000000000000 : ℝ)^407 := by
    have hnat : (4692557 : ℕ)^535*25000000000000^407 ≤ 12791933466723^407*7812500^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4692557 7812500 12791933466723 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (240281647/500000000 : ℝ)^535 ≤ (38164742023409/100000000000000 : ℝ)^407 := by
    have hnat : (240281647 : ℕ)^535*100000000000000^407 ≤ 38164742023409^407*500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      240281647 500000000 38164742023409 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-36444473/200000000 : ℝ), (4692557/7812500 : ℝ), (240281647/500000000 : ℝ)] ![(2666881020539/25000000000000 : ℝ), (12791933466723/25000000000000 : ℝ), (38164742023409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-36444473/200000000 : ℝ)|^535 ≤ (2666881020539/25000000000000 : ℝ)^407
        have hw : |(-36444473/200000000 : ℝ)|=(36444473/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4692557/7812500 : ℝ)|^535 ≤ (12791933466723/25000000000000 : ℝ)^407
        have hw : |(4692557/7812500 : ℝ)|=(4692557/7812500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(240281647/500000000 : ℝ)|^535 ≤ (38164742023409/100000000000000 : ℝ)^407
        have hw : |(240281647/500000000 : ℝ)|=(240281647/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s0_1 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2752139043/5000000000 : ℝ)*x 0 + (-1252937213/5000000000 : ℝ)*x 1 + (96112661/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2752139043/5000000000 : ℝ)^535 ≤ (11404903026099/25000000000000 : ℝ)^407 := by
    have hnat : (2752139043 : ℕ)^535*25000000000000^407 ≤ 11404903026099^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2752139043 5000000000 11404903026099 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1252937213/5000000000 : ℝ)^535 ≤ (16215644704863/100000000000000 : ℝ)^407 := by
    have hnat : (1252937213 : ℕ)^535*100000000000000^407 ≤ 16215644704863^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1252937213 5000000000 16215644704863 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96112661/200000000 : ℝ)^535 ≤ (9541185792933/25000000000000 : ℝ)^407 := by
    have hnat : (96112661 : ℕ)^535*25000000000000^407 ≤ 9541185792933^407*200000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96112661 200000000 9541185792933 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2752139043/5000000000 : ℝ), (-1252937213/5000000000 : ℝ), (96112661/200000000 : ℝ)] ![(11404903026099/25000000000000 : ℝ), (16215644704863/100000000000000 : ℝ), (9541185792933/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2752139043/5000000000 : ℝ)|^535 ≤ (11404903026099/25000000000000 : ℝ)^407
        have hw : |(2752139043/5000000000 : ℝ)|=(2752139043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1252937213/5000000000 : ℝ)|^535 ≤ (16215644704863/100000000000000 : ℝ)^407
        have hw : |(-1252937213/5000000000 : ℝ)|=(1252937213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(96112661/200000000 : ℝ)|^535 ≤ (9541185792933/25000000000000 : ℝ)^407
        have hw : |(96112661/200000000 : ℝ)|=(96112661/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s0_2 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5504277331/10000000000 : ℝ)*x 0 + (1201408369/2500000000 : ℝ)*x 1 + (-250587487/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5504277331/10000000000 : ℝ)^535 ≤ (22809801939493/50000000000000 : ℝ)^407 := by
    have hnat : (5504277331 : ℕ)^535*50000000000000^407 ≤ 22809801939493^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5504277331 10000000000 22809801939493 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1201408369/2500000000 : ℝ)^535 ≤ (38164747618871/100000000000000 : ℝ)^407 := by
    have hnat : (1201408369 : ℕ)^535*100000000000000^407 ≤ 38164747618871^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1201408369 2500000000 38164747618871 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (250587487/1000000000 : ℝ)^535 ≤ (3243129696321/20000000000000 : ℝ)^407 := by
    have hnat : (250587487 : ℕ)^535*20000000000000^407 ≤ 3243129696321^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      250587487 1000000000 3243129696321 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5504277331/10000000000 : ℝ), (1201408369/2500000000 : ℝ), (-250587487/1000000000 : ℝ)] ![(22809801939493/50000000000000 : ℝ), (38164747618871/100000000000000 : ℝ), (3243129696321/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5504277331/10000000000 : ℝ)|^535 ≤ (22809801939493/50000000000000 : ℝ)^407
        have hw : |(5504277331/10000000000 : ℝ)|=(5504277331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1201408369/2500000000 : ℝ)|^535 ≤ (38164747618871/100000000000000 : ℝ)^407
        have hw : |(1201408369/2500000000 : ℝ)|=(1201408369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-250587487/1000000000 : ℝ)|^535 ≤ (3243129696321/20000000000000 : ℝ)^407
        have hw : |(-250587487/1000000000 : ℝ)|=(250587487/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s0_3 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4182059109/10000000000 : ℝ)*x 0 + (3107730971/10000000000 : ℝ)*x 1 + (5602172209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4182059109/10000000000 : ℝ)^535 ≤ (7948016834823/25000000000000 : ℝ)^407 := by
    have hnat : (4182059109 : ℕ)^535*25000000000000^407 ≤ 7948016834823^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4182059109 10000000000 7948016834823 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3107730971/10000000000 : ℝ)^535 ≤ (10759417135149/50000000000000 : ℝ)^407 := by
    have hnat : (3107730971 : ℕ)^535*50000000000000^407 ≤ 10759417135149^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3107730971 10000000000 10759417135149 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5602172209/10000000000 : ℝ)^535 ≤ (46689098373297/100000000000000 : ℝ)^407 := by
    have hnat : (5602172209 : ℕ)^535*100000000000000^407 ≤ 46689098373297^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5602172209 10000000000 46689098373297 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4182059109/10000000000 : ℝ), (3107730971/10000000000 : ℝ), (5602172209/10000000000 : ℝ)] ![(7948016834823/25000000000000 : ℝ), (10759417135149/50000000000000 : ℝ), (46689098373297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4182059109/10000000000 : ℝ)|^535 ≤ (7948016834823/25000000000000 : ℝ)^407
        have hw : |(4182059109/10000000000 : ℝ)|=(4182059109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3107730971/10000000000 : ℝ)|^535 ≤ (10759417135149/50000000000000 : ℝ)^407
        have hw : |(3107730971/10000000000 : ℝ)|=(3107730971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5602172209/10000000000 : ℝ)|^535 ≤ (46689098373297/100000000000000 : ℝ)^407
        have hw : |(5602172209/10000000000 : ℝ)|=(5602172209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s0_4 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-456699189/2500000000 : ℝ)*x 0 + (4836578657/10000000000 : ℝ)*x 1 + (5974423651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (456699189/2500000000 : ℝ)^535 ≤ (10702729041697/100000000000000 : ℝ)^407 := by
    have hnat : (456699189 : ℕ)^535*100000000000000^407 ≤ 10702729041697^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      456699189 2500000000 10702729041697 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4836578657/10000000000 : ℝ)^535 ≤ (19244060042947/50000000000000 : ℝ)^407 := by
    have hnat : (4836578657 : ℕ)^535*50000000000000^407 ≤ 19244060042947^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4836578657 10000000000 19244060042947 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5974423651/10000000000 : ℝ)^535 ≤ (12702287714047/25000000000000 : ℝ)^407 := by
    have hnat : (5974423651 : ℕ)^535*25000000000000^407 ≤ 12702287714047^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5974423651 10000000000 12702287714047 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-456699189/2500000000 : ℝ), (4836578657/10000000000 : ℝ), (5974423651/10000000000 : ℝ)] ![(10702729041697/100000000000000 : ℝ), (19244060042947/50000000000000 : ℝ), (12702287714047/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-456699189/2500000000 : ℝ)|^535 ≤ (10702729041697/100000000000000 : ℝ)^407
        have hw : |(-456699189/2500000000 : ℝ)|=(456699189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4836578657/10000000000 : ℝ)|^535 ≤ (19244060042947/50000000000000 : ℝ)^407
        have hw : |(4836578657/10000000000 : ℝ)|=(4836578657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5974423651/10000000000 : ℝ)|^535 ≤ (12702287714047/25000000000000 : ℝ)^407
        have hw : |(5974423651/10000000000 : ℝ)|=(5974423651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s0_5 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2588578297/5000000000 : ℝ)*x 0 + (-167135571/1250000000 : ℝ)*x 1 + (5974423661/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2588578297/5000000000 : ℝ)^535 ≤ (42089529337769/100000000000000 : ℝ)^407 := by
    have hnat : (2588578297 : ℕ)^535*100000000000000^407 ≤ 42089529337769^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588578297 5000000000 42089529337769 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (167135571/1250000000 : ℝ)^535 ≤ (1775329919477/25000000000000 : ℝ)^407 := by
    have hnat : (167135571 : ℕ)^535*25000000000000^407 ≤ 1775329919477^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167135571 1250000000 1775329919477 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5974423661/10000000000 : ℝ)^535 ≤ (25404575483989/50000000000000 : ℝ)^407 := by
    have hnat : (5974423661 : ℕ)^535*50000000000000^407 ≤ 25404575483989^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5974423661 10000000000 25404575483989 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2588578297/5000000000 : ℝ), (-167135571/1250000000 : ℝ), (5974423661/10000000000 : ℝ)] ![(42089529337769/100000000000000 : ℝ), (1775329919477/25000000000000 : ℝ), (25404575483989/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2588578297/5000000000 : ℝ)|^535 ≤ (42089529337769/100000000000000 : ℝ)^407
        have hw : |(2588578297/5000000000 : ℝ)|=(2588578297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-167135571/1250000000 : ℝ)|^535 ≤ (1775329919477/25000000000000 : ℝ)^407
        have hw : |(-167135571/1250000000 : ℝ)|=(167135571/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5974423661/10000000000 : ℝ)|^535 ≤ (25404575483989/50000000000000 : ℝ)^407
        have hw : |(5974423661/10000000000 : ℝ)|=(5974423661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s0_6 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5177156583/10000000000 : ℝ)*x 0 + (2987211829/5000000000 : ℝ)*x 1 + (-133708459/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5177156583/10000000000 : ℝ)^535 ≤ (8417905844043/20000000000000 : ℝ)^407 := by
    have hnat : (5177156583 : ℕ)^535*20000000000000^407 ≤ 8417905844043^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177156583 10000000000 8417905844043 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2987211829/5000000000 : ℝ)^535 ≤ (50809150934441/100000000000000 : ℝ)^407 := by
    have hnat : (2987211829 : ℕ)^535*100000000000000^407 ≤ 50809150934441^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2987211829 5000000000 50809150934441 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (133708459/1000000000 : ℝ)^535 ≤ (3550659915749/50000000000000 : ℝ)^407 := by
    have hnat : (133708459 : ℕ)^535*50000000000000^407 ≤ 3550659915749^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133708459 1000000000 3550659915749 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5177156583/10000000000 : ℝ), (2987211829/5000000000 : ℝ), (-133708459/1000000000 : ℝ)] ![(8417905844043/20000000000000 : ℝ), (50809150934441/100000000000000 : ℝ), (3550659915749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5177156583/10000000000 : ℝ)|^535 ≤ (8417905844043/20000000000000 : ℝ)^407
        have hw : |(5177156583/10000000000 : ℝ)|=(5177156583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2987211829/5000000000 : ℝ)|^535 ≤ (50809150934441/100000000000000 : ℝ)^407
        have hw : |(2987211829/5000000000 : ℝ)|=(2987211829/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-133708459/1000000000 : ℝ)|^535 ≤ (3550659915749/50000000000000 : ℝ)^407
        have hw : |(-133708459/1000000000 : ℝ)|=(133708459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s0_7 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (32746549/78125000 : ℝ)*x 0 + (2768945391/5000000000 : ℝ)*x 1 + (1587152303/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (32746549/78125000 : ℝ)^535 ≤ (15943512316263/50000000000000 : ℝ)^407 := by
    have hnat : (32746549 : ℕ)^535*50000000000000^407 ≤ 15943512316263^407*78125000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32746549 78125000 15943512316263 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2768945391/5000000000 : ℝ)^535 ≤ (9197231909931/20000000000000 : ℝ)^407 := by
    have hnat : (2768945391 : ℕ)^535*20000000000000^407 ≤ 9197231909931^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768945391 5000000000 9197231909931 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1587152303/5000000000 : ℝ)^535 ≤ (2212681579743/10000000000000 : ℝ)^407 := by
    have hnat : (1587152303 : ℕ)^535*10000000000000^407 ≤ 2212681579743^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1587152303 5000000000 2212681579743 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(32746549/78125000 : ℝ), (2768945391/5000000000 : ℝ), (1587152303/5000000000 : ℝ)] ![(15943512316263/50000000000000 : ℝ), (9197231909931/20000000000000 : ℝ), (2212681579743/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(32746549/78125000 : ℝ)|^535 ≤ (15943512316263/50000000000000 : ℝ)^407
        have hw : |(32746549/78125000 : ℝ)|=(32746549/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2768945391/5000000000 : ℝ)|^535 ≤ (9197231909931/20000000000000 : ℝ)^407
        have hw : |(2768945391/5000000000 : ℝ)|=(2768945391/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1587152303/5000000000 : ℝ)|^535 ≤ (2212681579743/10000000000000 : ℝ)^407
        have hw : |(1587152303/5000000000 : ℝ)|=(1587152303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1320_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (39/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2703/10000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4279/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4279 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4279*1^1024 ≤ 0^1024*1^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4279/1024 : ℝ) ≤ (2173320283603873707/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4279 ≤ (2173320283603873707/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4279*100000000000000000000^1024 ≤ 2173320283603873707^1024*5^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2173320283603873707 100000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2173320283603873707/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4279 := by
      have hnat : (1 : ℕ)^1024*1^4279 ≤ 1^4279*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (102173320283603873707/100000000000000000000 : ℝ) ≤ (10051584833768203/10000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (102173320283603873707/100000000000000000000 : ℝ)^1024 ≤ (10051584833768203/10000000000000000 : ℝ)^4279 := by
      have hnat : (102173320283603873707 : ℕ)^1024*10000000000000000^4279 ≤ 10051584833768203^4279*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102173320283603873707 100000000000000000000 10051584833768203 10000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10051584833768203/10000000000000000 : ℝ)) (X := (102173320283603873707/100000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (52173320283603873707/50000000000000000000 : ℝ) ≤ (5051584833768203/5000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (52173320283603873707/50000000000000000000 : ℝ)^1024 ≤ (5051584833768203/5000000000000000 : ℝ)^4279 := by
      have hnat : (52173320283603873707 : ℕ)^1024*5000000000000000^4279 ≤ 5051584833768203^4279*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52173320283603873707 50000000000000000000 5051584833768203 5000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5051584833768203/5000000000000000 : ℝ)) (X := (52173320283603873707/50000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(51584833768203/4000000000000000 : ℝ)*(0 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(51584833768203/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2173320283603873707/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(51584833768203/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4279/1024 : ℝ) := by
    rw [show (1 : ℝ)+(51584833768203/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10051584833768203/10000000000000000 : ℝ) by norm_num, show 1+(2173320283603873707/100000000000000000000 : ℝ)+(0 : ℝ)=(102173320283603873707/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2173320283603873707/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(51584833768203/4000000000000000 : ℝ)*(2/5 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(51584833768203/4000000000000000 : ℝ)*(2/5 : ℝ)=(5051584833768203/5000000000000000 : ℝ) by norm_num, show 1+2*(2173320283603873707/100000000000000000000 : ℝ)=(52173320283603873707/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(51584833768203/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51584833768203/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(51584833768203/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51584833768203/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(51584833768203/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (51584833768203/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-36444473/200000000 : ℝ)*X 0 0+(4692557/7812500 : ℝ)*X 0 1+(240281647/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2752139043/5000000000 : ℝ)*X 1 0+(-1252937213/5000000000 : ℝ)*X 1 1+(96112661/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5504277331/10000000000 : ℝ)*X 2 0+(1201408369/2500000000 : ℝ)*X 2 1+(-250587487/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4182059109/10000000000 : ℝ)*X 0 0+(3107730971/10000000000 : ℝ)*X 0 1+(5602172209/10000000000 : ℝ)*X 0 2+(4182059109/10000000000 : ℝ)*X 1 0+(3107730971/10000000000 : ℝ)*X 1 1+(5602172209/10000000000 : ℝ)*X 1 2+(4182059109/10000000000 : ℝ)*X 2 0+(3107730971/10000000000 : ℝ)*X 2 1+(5602172209/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-456699189/2500000000 : ℝ)*X 0 0+(4836578657/10000000000 : ℝ)*X 0 1+(5974423651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2588578297/5000000000 : ℝ)*X 1 0+(-167135571/1250000000 : ℝ)*X 1 1+(5974423661/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5177156583/10000000000 : ℝ)*X 2 0+(2987211829/5000000000 : ℝ)*X 2 1+(-133708459/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((32746549/78125000 : ℝ)*X 0 0+(2768945391/5000000000 : ℝ)*X 0 1+(1587152303/5000000000 : ℝ)*X 0 2+(32746549/78125000 : ℝ)*X 1 0+(2768945391/5000000000 : ℝ)*X 1 1+(1587152303/5000000000 : ℝ)*X 1 2+(32746549/78125000 : ℝ)*X 2 0+(2768945391/5000000000 : ℝ)*X 2 1+(1587152303/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22107402394392129621171/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12583603/20000000000000 : ℝ)*(base1) + (942347297/100000000000000 : ℝ)*(base19) + (207030377/25000000000000 : ℝ)*(base23) + (81400001/50000000000000 : ℝ)*(upper3) + (13707377/100000000000000 : ℝ)*(upper5) + (38551585770831/6250000000000 : ℝ)*(major0) + (38551585770831/6250000000000 : ℝ)*(major1) + (38551585770831/6250000000000 : ℝ)*(major2) + (416376957345641/50000000000000 : ℝ)*(sp0) + (832755524214001/100000000000000 : ℝ)*(sp1) + (83275563843979/10000000000000 : ℝ)*(sp2) + (400892532185781/100000000000000 : ℝ)*(sp3) + (2614788031/100000000000000 : ℝ)*(sp4) + (782547671/50000000000000 : ℝ)*(sp7) + (400894160199137/100000000000000 : ℝ)*(f.failure) + (832756466561299/100000000000000 : ℝ)*(f.sum) + (52405510025807/12500000000000000000000000000 : ℝ)*base66 + (168578885636693/25000000000000000000000000000 : ℝ)*base67 + (68473739136693/25000000000000000000000000000 : ℝ)*base69 + (26780626711693/25000000000000000000000000000 : ℝ)*base71 + (6057353074193/12500000000000000000000000000 : ℝ)*base73 + (93219169411693/25000000000000000000000000000 : ℝ)*base75 + (21112666611693/25000000000000000000000000000 : ℝ)*base77 + (122578361811693/25000000000000000000000000000 : ℝ)*base79 + (31672719575807/12500000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (63450337/10000000000000000000000 : ℝ)*base90 + (63450337/10000000000000000000000 : ℝ)*base92 + (63450337/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126028179627105731076453/40000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37657433/5000000000000 : ℝ)*(base19) + (757307061/100000000000000 : ℝ)*(base23) + (27274271/50000000000000 : ℝ)*(base32) + (5400441/5000000000000 : ℝ)*(upper3) + (17726997/25000000000000 : ℝ)*(upper5) + (130194002896361/20000000000000 : ℝ)*(major0) + (130194002896361/20000000000000 : ℝ)*(major1) + (130194002896361/20000000000000 : ℝ)*(major2) + (1677424293/100000000000000 : ℝ)*(sp1) + (354558749/20000000000000 : ℝ)*(sp2) + (439427044820497/50000000000000 : ℝ)*(sp4) + (878851659068041/100000000000000 : ℝ)*(sp5) + (219712889885047/25000000000000 : ℝ)*(sp6) + (423085779750587/100000000000000 : ℝ)*(sp7) + (423085834299129/100000000000000 : ℝ)*(f.failure) + (439427044820497/50000000000000 : ℝ)*(f.sum) + (42384098209283/40000000000000000000000000000 : ℝ)*base65 + (228224621150717/80000000000000000000000000000 : ℝ)*base68 + (402255480929283/80000000000000000000000000000 : ℝ)*base69 + (259822808929283/80000000000000000000000000000 : ℝ)*base71 + (107638970910717/40000000000000000000000000000 : ℝ)*base74 + (240635268369283/80000000000000000000000000000 : ℝ)*base75 + (367215077169283/80000000000000000000000000000 : ℝ)*base77 + (137238557569283/80000000000000000000000000000 : ℝ)*base79 + (54255200129283/40000000000000000000000000000 : ℝ)*base81 + (28449529/10000000000000000000000 : ℝ)*base90 + (28449529/10000000000000000000000 : ℝ)*base92 + (28449529/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1320_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (39/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2703/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1320_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1320_s1_0 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2010218937/10000000000 : ℝ)*x 0 + (282607033/500000000 : ℝ)*x 1 + (5039591191/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2010218937/10000000000 : ℝ)^535 ≤ (12137128904553/100000000000000 : ℝ)^407 := by
    have hnat : (2010218937 : ℕ)^535*100000000000000^407 ≤ 12137128904553^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2010218937 10000000000 12137128904553 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282607033/500000000 : ℝ)^535 ≤ (23618638285799/50000000000000 : ℝ)^407 := by
    have hnat : (282607033 : ℕ)^535*50000000000000^407 ≤ 23618638285799^407*500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282607033 500000000 23618638285799 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5039591191/10000000000 : ℝ)^535 ≤ (1269549828199/3125000000000 : ℝ)^407 := by
    have hnat : (5039591191 : ℕ)^535*3125000000000^407 ≤ 1269549828199^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5039591191 10000000000 1269549828199 3125000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2010218937/10000000000 : ℝ), (282607033/500000000 : ℝ), (5039591191/10000000000 : ℝ)] ![(12137128904553/100000000000000 : ℝ), (23618638285799/50000000000000 : ℝ), (1269549828199/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2010218937/10000000000 : ℝ)|^535 ≤ (12137128904553/100000000000000 : ℝ)^407
        have hw : |(-2010218937/10000000000 : ℝ)|=(2010218937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(282607033/500000000 : ℝ)|^535 ≤ (23618638285799/50000000000000 : ℝ)^407
        have hw : |(282607033/500000000 : ℝ)|=(282607033/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5039591191/10000000000 : ℝ)|^535 ≤ (1269549828199/3125000000000 : ℝ)^407
        have hw : |(5039591191/10000000000 : ℝ)|=(5039591191/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s1_1 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1352005477/2500000000 : ℝ)*x 0 + (-1168856723/5000000000 : ℝ)*x 1 + (5039591039/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1352005477/2500000000 : ℝ)^535 ≤ (11143459138923/25000000000000 : ℝ)^407 := by
    have hnat : (1352005477 : ℕ)^535*25000000000000^407 ≤ 11143459138923^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352005477 2500000000 11143459138923 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1168856723/5000000000 : ℝ)^535 ≤ (1480057053789/10000000000000 : ℝ)^407 := by
    have hnat : (1168856723 : ℕ)^535*10000000000000^407 ≤ 1480057053789^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1168856723 5000000000 1480057053789 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5039591039/10000000000 : ℝ)^535 ≤ (8125118578339/20000000000000 : ℝ)^407 := by
    have hnat : (5039591039 : ℕ)^535*20000000000000^407 ≤ 8125118578339^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5039591039 10000000000 8125118578339 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1352005477/2500000000 : ℝ), (-1168856723/5000000000 : ℝ), (5039591039/10000000000 : ℝ)] ![(11143459138923/25000000000000 : ℝ), (1480057053789/10000000000000 : ℝ), (8125118578339/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1352005477/2500000000 : ℝ)|^535 ≤ (11143459138923/25000000000000 : ℝ)^407
        have hw : |(1352005477/2500000000 : ℝ)|=(1352005477/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1168856723/5000000000 : ℝ)|^535 ≤ (1480057053789/10000000000000 : ℝ)^407
        have hw : |(-1168856723/5000000000 : ℝ)|=(1168856723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5039591039/10000000000 : ℝ)|^535 ≤ (8125118578339/20000000000000 : ℝ)^407
        have hw : |(5039591039/10000000000 : ℝ)|=(5039591039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s1_2 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (5408021519/10000000000 : ℝ)*x 0 + (2519795493/5000000000 : ℝ)*x 1 + (-2337714019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5408021519/10000000000 : ℝ)^535 ≤ (11143458085287/25000000000000 : ℝ)^407 := by
    have hnat : (5408021519 : ℕ)^535*25000000000000^407 ≤ 11143458085287^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408021519 10000000000 11143458085287 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2519795493/5000000000 : ℝ)^535 ≤ (40625592330079/100000000000000 : ℝ)^407 := by
    have hnat : (2519795493 : ℕ)^535*100000000000000^407 ≤ 40625592330079^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2519795493 5000000000 40625592330079 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2337714019/10000000000 : ℝ)^535 ≤ (14800575306603/100000000000000 : ℝ)^407 := by
    have hnat : (2337714019 : ℕ)^535*100000000000000^407 ≤ 14800575306603^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337714019 10000000000 14800575306603 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5408021519/10000000000 : ℝ), (2519795493/5000000000 : ℝ), (-2337714019/10000000000 : ℝ)] ![(11143458085287/25000000000000 : ℝ), (40625592330079/100000000000000 : ℝ), (14800575306603/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5408021519/10000000000 : ℝ)|^535 ≤ (11143458085287/25000000000000 : ℝ)^407
        have hw : |(5408021519/10000000000 : ℝ)|=(5408021519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2519795493/5000000000 : ℝ)|^535 ≤ (40625592330079/100000000000000 : ℝ)^407
        have hw : |(2519795493/5000000000 : ℝ)|=(2519795493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2337714019/10000000000 : ℝ)|^535 ≤ (14800575306603/100000000000000 : ℝ)^407
        have hw : |(-2337714019/10000000000 : ℝ)|=(2337714019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s1_3 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2148107231/5000000000 : ℝ)*x 0 + (740816941/2000000000 : ℝ)*x 1 + (4976501201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148107231/5000000000 : ℝ)^535 ≤ (32937667195613/100000000000000 : ℝ)^407 := by
    have hnat : (2148107231 : ℕ)^535*100000000000000^407 ≤ 32937667195613^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148107231 5000000000 32937667195613 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (740816941/2000000000 : ℝ)^535 ≤ (2710395360533/10000000000000 : ℝ)^407 := by
    have hnat : (740816941 : ℕ)^535*10000000000000^407 ≤ 2710395360533^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740816941 2000000000 2710395360533 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4976501201/10000000000 : ℝ)^535 ≤ (39958379185287/100000000000000 : ℝ)^407 := by
    have hnat : (4976501201 : ℕ)^535*100000000000000^407 ≤ 39958379185287^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4976501201 10000000000 39958379185287 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148107231/5000000000 : ℝ), (740816941/2000000000 : ℝ), (4976501201/10000000000 : ℝ)] ![(32937667195613/100000000000000 : ℝ), (2710395360533/10000000000000 : ℝ), (39958379185287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148107231/5000000000 : ℝ)|^535 ≤ (32937667195613/100000000000000 : ℝ)^407
        have hw : |(2148107231/5000000000 : ℝ)|=(2148107231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(740816941/2000000000 : ℝ)|^535 ≤ (2710395360533/10000000000000 : ℝ)^407
        have hw : |(740816941/2000000000 : ℝ)|=(740816941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4976501201/10000000000 : ℝ)|^535 ≤ (39958379185287/100000000000000 : ℝ)^407
        have hw : |(4976501201/10000000000 : ℝ)|=(4976501201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s1_4 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-502699451/2500000000 : ℝ)*x 0 + (100948153/200000000 : ℝ)*x 1 + (5644179343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (502699451/2500000000 : ℝ)^535 ≤ (3035430830449/25000000000000 : ℝ)^407 := by
    have hnat : (502699451 : ℕ)^535*25000000000000^407 ≤ 3035430830449^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      502699451 2500000000 3035430830449 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100948153/200000000 : ℝ)^535 ≤ (5088555257729/12500000000000 : ℝ)^407 := by
    have hnat : (100948153 : ℕ)^535*12500000000000^407 ≤ 5088555257729^407*200000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100948153 200000000 5088555257729 12500000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5644179343/10000000000 : ℝ)^535 ≤ (5893729324911/12500000000000 : ℝ)^407 := by
    have hnat : (5644179343 : ℕ)^535*12500000000000^407 ≤ 5893729324911^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5644179343 10000000000 5893729324911 12500000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-502699451/2500000000 : ℝ), (100948153/200000000 : ℝ), (5644179343/10000000000 : ℝ)] ![(3035430830449/25000000000000 : ℝ), (5088555257729/12500000000000 : ℝ), (5893729324911/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-502699451/2500000000 : ℝ)|^535 ≤ (3035430830449/25000000000000 : ℝ)^407
        have hw : |(-502699451/2500000000 : ℝ)|=(502699451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(100948153/200000000 : ℝ)|^535 ≤ (5088555257729/12500000000000 : ℝ)^407
        have hw : |(100948153/200000000 : ℝ)|=(100948153/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5644179343/10000000000 : ℝ)|^535 ≤ (5893729324911/12500000000000 : ℝ)^407
        have hw : |(5644179343/10000000000 : ℝ)|=(5644179343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s1_5 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (1049874109/2000000000 : ℝ)*x 0 + (-346625129/2000000000 : ℝ)*x 1 + (5644178969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049874109/2000000000 : ℝ)^535 ≤ (10715735718531/25000000000000 : ℝ)^407 := by
    have hnat : (1049874109 : ℕ)^535*25000000000000^407 ≤ 10715735718531^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049874109 2000000000 10715735718531 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (346625129/2000000000 : ℝ)^535 ≤ (9987226609767/100000000000000 : ℝ)^407 := by
    have hnat : (346625129 : ℕ)^535*100000000000000^407 ≤ 9987226609767^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346625129 2000000000 9987226609767 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5644178969/10000000000 : ℝ)^535 ≤ (5893728811553/12500000000000 : ℝ)^407 := by
    have hnat : (5644178969 : ℕ)^535*12500000000000^407 ≤ 5893728811553^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5644178969 10000000000 5893728811553 12500000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049874109/2000000000 : ℝ), (-346625129/2000000000 : ℝ), (5644178969/10000000000 : ℝ)] ![(10715735718531/25000000000000 : ℝ), (9987226609767/100000000000000 : ℝ), (5893728811553/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049874109/2000000000 : ℝ)|^535 ≤ (10715735718531/25000000000000 : ℝ)^407
        have hw : |(1049874109/2000000000 : ℝ)|=(1049874109/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-346625129/2000000000 : ℝ)|^535 ≤ (9987226609767/100000000000000 : ℝ)^407
        have hw : |(-346625129/2000000000 : ℝ)|=(346625129/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5644178969/10000000000 : ℝ)|^535 ≤ (5893728811553/12500000000000 : ℝ)^407
        have hw : |(5644178969/10000000000 : ℝ)|=(5644178969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s1_6 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (20505353/39062500 : ℝ)*x 0 + (5644178809/10000000000 : ℝ)*x 1 + (-1733126129/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (20505353/39062500 : ℝ)^535 ≤ (21431470487163/50000000000000 : ℝ)^407 := by
    have hnat : (20505353 : ℕ)^535*50000000000000^407 ≤ 21431470487163^407*39062500^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20505353 39062500 21431470487163 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5644178809/10000000000 : ℝ)^535 ≤ (11787457183869/25000000000000 : ℝ)^407 := by
    have hnat : (5644178809 : ℕ)^535*25000000000000^407 ≤ 11787457183869^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5644178809 10000000000 11787457183869 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1733126129/10000000000 : ℝ)^535 ≤ (2496807568999/25000000000000 : ℝ)^407 := by
    have hnat : (1733126129 : ℕ)^535*25000000000000^407 ≤ 2496807568999^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1733126129 10000000000 2496807568999 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(20505353/39062500 : ℝ), (5644178809/10000000000 : ℝ), (-1733126129/10000000000 : ℝ)] ![(21431470487163/50000000000000 : ℝ), (11787457183869/25000000000000 : ℝ), (2496807568999/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(20505353/39062500 : ℝ)|^535 ≤ (21431470487163/50000000000000 : ℝ)^407
        have hw : |(20505353/39062500 : ℝ)|=(20505353/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5644178809/10000000000 : ℝ)|^535 ≤ (11787457183869/25000000000000 : ℝ)^407
        have hw : |(5644178809/10000000000 : ℝ)|=(5644178809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1733126129/10000000000 : ℝ)|^535 ≤ (2496807568999/25000000000000 : ℝ)^407
        have hw : |(-1733126129/10000000000 : ℝ)|=(1733126129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s1_7 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (429741603/1000000000 : ℝ)*x 0 + (2480131919/5000000000 : ℝ)*x 1 + (3720622497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429741603/1000000000 : ℝ)^535 ≤ (16474888452337/50000000000000 : ℝ)^407 := by
    have hnat : (429741603 : ℕ)^535*50000000000000^407 ≤ 16474888452337^407*1000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429741603 1000000000 16474888452337 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2480131919/5000000000 : ℝ)^535 ≤ (3978708777859/10000000000000 : ℝ)^407 := by
    have hnat : (2480131919 : ℕ)^535*10000000000000^407 ≤ 3978708777859^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2480131919 5000000000 3978708777859 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3720622497/10000000000 : ℝ)^535 ≤ (6815783824913/25000000000000 : ℝ)^407 := by
    have hnat : (3720622497 : ℕ)^535*25000000000000^407 ≤ 6815783824913^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3720622497 10000000000 6815783824913 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(429741603/1000000000 : ℝ), (2480131919/5000000000 : ℝ), (3720622497/10000000000 : ℝ)] ![(16474888452337/50000000000000 : ℝ), (3978708777859/10000000000000 : ℝ), (6815783824913/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(429741603/1000000000 : ℝ)|^535 ≤ (16474888452337/50000000000000 : ℝ)^407
        have hw : |(429741603/1000000000 : ℝ)|=(429741603/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2480131919/5000000000 : ℝ)|^535 ≤ (3978708777859/10000000000000 : ℝ)^407
        have hw : |(2480131919/5000000000 : ℝ)|=(2480131919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3720622497/10000000000 : ℝ)|^535 ≤ (6815783824913/25000000000000 : ℝ)^407
        have hw : |(3720622497/10000000000 : ℝ)|=(3720622497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1320_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2703/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (39/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (3341/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19629/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2703/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (39/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2703/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (39/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2703/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (39/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2703/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (39/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2703/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (39/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2703/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (39/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (39/3125 : ℝ) ^ (4279/1024 : ℝ) ≤ (221646593403/20000000000000000000 : ℝ) := by
    have hpowers : (39/3125 : ℝ)^4279 ≤ (221646593403/20000000000000000000 : ℝ)^1024 := by
      have hnat : (39 : ℕ)^4279*20000000000000000000^1024 ≤ 221646593403^1024*3125^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        39 3125 221646593403 20000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (39/3125 : ℝ)) (X := (221646593403/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2703/10000 : ℝ) ^ (4279/1024 : ℝ) ≤ (422521542866973677/100000000000000000000 : ℝ) := by
    have hpowers : (2703/10000 : ℝ)^4279 ≤ (422521542866973677/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2703 : ℕ)^4279*100000000000000000000^1024 ≤ 422521542866973677^1024*10000^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2703 10000 422521542866973677 100000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2703/10000 : ℝ)) (X := (422521542866973677/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000000221646593403/10000000000000000000 : ℝ) ≤ (5000000026520929/5000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (10000000221646593403/10000000000000000000 : ℝ)^1024 ≤ (5000000026520929/5000000000000000 : ℝ)^4279 := by
      have hnat : (10000000221646593403 : ℕ)^1024*5000000000000000^4279 ≤ 5000000026520929^4279*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000000221646593403 10000000000000000000 5000000026520929 5000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000026520929/5000000000000000 : ℝ)) (X := (10000000221646593403/10000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25105630662774985173/25000000000000000000 : ℝ) ≤ (1001009510641813/1000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (25105630662774985173/25000000000000000000 : ℝ)^1024 ≤ (1001009510641813/1000000000000000 : ℝ)^4279 := by
      have hnat : (25105630662774985173 : ℕ)^1024*1000000000000000^4279 ≤ 1001009510641813^4279*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25105630662774985173 25000000000000000000 1001009510641813 1000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1001009510641813/1000000000000000 : ℝ)) (X := (25105630662774985173/25000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50422521542866973677/50000000000000000000 : ℝ) ≤ (5010095079897201/5000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (50422521542866973677/50000000000000000000 : ℝ)^1024 ≤ (5010095079897201/5000000000000000 : ℝ)^4279 := by
      have hnat : (50422521542866973677 : ℕ)^1024*5000000000000000^4279 ≤ 5010095079897201^4279*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50422521542866973677 50000000000000000000 5010095079897201 5000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5010095079897201/5000000000000000 : ℝ)) (X := (50422521542866973677/50000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(221646593403/20000000000000000000 : ℝ) ≤ ((21482900342858167337/21485000000000000000 : ℝ)+2*(630940836017/161137500000000 : ℝ)*(39/3125 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (21482900342858167337/21485000000000000000 : ℝ)+2*(630940836017/161137500000000 : ℝ)*(39/3125 : ℝ)=(5000000026520929/5000000000000000 : ℝ) by norm_num, show 1+2*(221646593403/20000000000000000000 : ℝ)=(10000000221646593403/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(422521542866973677/100000000000000000000 : ℝ)+(221646593403/20000000000000000000 : ℝ) ≤ ((21482900342858167337/21485000000000000000 : ℝ)+(630940836017/161137500000000 : ℝ)*((2703/10000 : ℝ)+(39/3125 : ℝ)))^(4279/1024 : ℝ) := by
    rw [show (21482900342858167337/21485000000000000000 : ℝ)+(630940836017/161137500000000 : ℝ)*((2703/10000 : ℝ)+(39/3125 : ℝ))=(1001009510641813/1000000000000000 : ℝ) by norm_num, show 1+(422521542866973677/100000000000000000000 : ℝ)+(221646593403/20000000000000000000 : ℝ)=(25105630662774985173/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(422521542866973677/100000000000000000000 : ℝ) ≤ ((21482900342858167337/21485000000000000000 : ℝ)+2*(630940836017/161137500000000 : ℝ)*(2703/10000 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (21482900342858167337/21485000000000000000 : ℝ)+2*(630940836017/161137500000000 : ℝ)*(2703/10000 : ℝ)=(5010095079897201/5000000000000000 : ℝ) by norm_num, show 1+2*(422521542866973677/100000000000000000000 : ℝ)=(50422521542866973677/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21482900342858167337/21485000000000000000 : ℝ)*(X 1 0+X 2 0)+(630940836017/161137500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (39/3125 : ℝ)) (hi := (2703/10000 : ℝ)) (c := (21482900342858167337/21485000000000000000 : ℝ)) (alpha := (630940836017/161137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21482900342858167337/21485000000000000000 : ℝ)*(X 0 1+X 2 1)+(630940836017/161137500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (39/3125 : ℝ)) (hi := (2703/10000 : ℝ)) (c := (21482900342858167337/21485000000000000000 : ℝ)) (alpha := (630940836017/161137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21482900342858167337/21485000000000000000 : ℝ)*(X 0 2+X 1 2)+(630940836017/161137500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (39/3125 : ℝ)) (hi := (2703/10000 : ℝ)) (c := (21482900342858167337/21485000000000000000 : ℝ)) (alpha := (630940836017/161137500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2010218937/10000000000 : ℝ)*X 0 0+(282607033/500000000 : ℝ)*X 0 1+(5039591191/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1352005477/2500000000 : ℝ)*X 1 0+(-1168856723/5000000000 : ℝ)*X 1 1+(5039591039/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5408021519/10000000000 : ℝ)*X 2 0+(2519795493/5000000000 : ℝ)*X 2 1+(-2337714019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2148107231/5000000000 : ℝ)*X 0 0+(740816941/2000000000 : ℝ)*X 0 1+(4976501201/10000000000 : ℝ)*X 0 2+(2148107231/5000000000 : ℝ)*X 1 0+(740816941/2000000000 : ℝ)*X 1 1+(4976501201/10000000000 : ℝ)*X 1 2+(2148107231/5000000000 : ℝ)*X 2 0+(740816941/2000000000 : ℝ)*X 2 1+(4976501201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-502699451/2500000000 : ℝ)*X 0 0+(100948153/200000000 : ℝ)*X 0 1+(5644179343/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1049874109/2000000000 : ℝ)*X 1 0+(-346625129/2000000000 : ℝ)*X 1 1+(5644178969/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((20505353/39062500 : ℝ)*X 2 0+(5644178809/10000000000 : ℝ)*X 2 1+(-1733126129/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((429741603/1000000000 : ℝ)*X 0 0+(2480131919/5000000000 : ℝ)*X 0 1+(3720622497/10000000000 : ℝ)*X 0 2+(429741603/1000000000 : ℝ)*X 1 0+(2480131919/5000000000 : ℝ)*X 1 1+(3720622497/10000000000 : ℝ)*X 1 2+(429741603/1000000000 : ℝ)*X 2 0+(2480131919/5000000000 : ℝ)*X 2 1+(3720622497/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (98002190732093064586569/10742500000000000000000000000 : ℝ) := by norm_num
    linear_combination (129905583/100000000000000 : ℝ)*(base1) + (755272189/50000000000000 : ℝ)*(base19) + (1393115847/100000000000000 : ℝ)*(base23) + (57945769/20000000000000 : ℝ)*(upper3) + (32229241/100000000000000 : ℝ)*(upper5) + (604612432049773/50000000000000 : ℝ)*(major0) + (604612432049773/50000000000000 : ℝ)*(major1) + (604612432049773/50000000000000 : ℝ)*(major2) + (65301210867477/4000000000000 : ℝ)*(sp0) + (1632534739217857/100000000000000 : ℝ)*(sp1) + (408133714161597/25000000000000 : ℝ)*(sp2) + (785909028923031/100000000000000 : ℝ)*(sp3) + (1526995223/25000000000000 : ℝ)*(sp4) + (4015513317/100000000000000 : ℝ)*(sp7) + (78591317434193/10000000000000 : ℝ)*(f.failure) + (326507249952447/20000000000000 : ℝ)*(f.sum) + (242608185011989/64455000000000000000000000000 : ℝ)*base66 + (22408302483924243503/3222750000000000000000000000000000 : ℝ)*base67 + (4562823331453256497/3222750000000000000000000000000000 : ℝ)*base70 + (23350018436019993503/3222750000000000000000000000000000 : ℝ)*base71 + (119897488826689/64455000000000000000000000000 : ℝ)*base74 + (11011519629121256497/3222750000000000000000000000000000 : ℝ)*base76 + (5773368133094006497/3222750000000000000000000000000000 : ℝ)*base78 + (11977020439227243503/3222750000000000000000000000000000 : ℝ)*base79 + (5849841857131/1007109375000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (390993/1000000000000000000000 : ℝ)*base90 + (390993/1000000000000000000000 : ℝ)*base92 + (390993/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (719229454402128775810426953/107425000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (590556629/50000000000000 : ℝ)*(base19) + (1075855387/100000000000000 : ℝ)*(base23) + (2543591/50000000000000 : ℝ)*(upper2) + (26083983/25000000000000 : ℝ)*(upper3) + (187192191/100000000000000 : ℝ)*(upper5) + (124118398981277/10000000000000 : ℝ)*(major0) + (124118398981277/10000000000000 : ℝ)*(major1) + (124118398981277/10000000000000 : ℝ)*(major2) + (5747142659/100000000000000 : ℝ)*(sp1) + (3813261933/100000000000000 : ℝ)*(sp2) + (1675683343705187/100000000000000 : ℝ)*(sp4) + (167567641544927/10000000000000 : ℝ)*(sp5) + (1675678454587867/100000000000000 : ℝ)*(sp6) + (806684412747763/100000000000000 : ℝ)*(sp7) + (806684412747763/100000000000000 : ℝ)*(f.failure) + (1675683343705187/100000000000000 : ℝ)*(f.sum) + (6650357825711/6445500000000000000000000000 : ℝ)*base65 + (198164711316248047/644550000000000000000000000000000 : ℝ)*base67 + (3532362686210151953/644550000000000000000000000000000 : ℝ)*base70 + (3984772550616848047/644550000000000000000000000000000 : ℝ)*base71 + (26521026273343/6445500000000000000000000000 : ℝ)*base74 + (325135506324651953/644550000000000000000000000000000 : ℝ)*base76 + (906056425864298047/644550000000000000000000000000000 : ℝ)*base77 + (5132088100727198047/644550000000000000000000000000000 : ℝ)*base79 + (33972864331787/12891000000000000000000000000 : ℝ)*base82 + (2936563/10000000000000000000000 : ℝ)*base90 + (2936563/10000000000000000000000 : ℝ)*base92 + (2936563/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1320_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2703/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (39/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3341/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19629/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1320_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1320_s2_0 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-2052324263/10000000000 : ℝ)*x 0 + (2742961567/5000000000 : ℝ)*x 1 + (323679469/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2052324263/10000000000 : ℝ)^535 ≤ (1247239552513/10000000000000 : ℝ)^407 := by
    have hnat : (2052324263 : ℕ)^535*10000000000000^407 ≤ 1247239552513^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2052324263 10000000000 1247239552513 10000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2742961567/5000000000 : ℝ)^535 ≤ (22709873751419/50000000000000 : ℝ)^407 := by
    have hnat : (2742961567 : ℕ)^535*50000000000000^407 ≤ 22709873751419^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2742961567 5000000000 22709873751419 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323679469/625000000 : ℝ)^535 ≤ (8421571391731/20000000000000 : ℝ)^407 := by
    have hnat : (323679469 : ℕ)^535*20000000000000^407 ≤ 8421571391731^407*625000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323679469 625000000 8421571391731 20000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2052324263/10000000000 : ℝ), (2742961567/5000000000 : ℝ), (323679469/625000000 : ℝ)] ![(1247239552513/10000000000000 : ℝ), (22709873751419/50000000000000 : ℝ), (8421571391731/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2052324263/10000000000 : ℝ)|^535 ≤ (1247239552513/10000000000000 : ℝ)^407
        have hw : |(-2052324263/10000000000 : ℝ)|=(2052324263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2742961567/5000000000 : ℝ)|^535 ≤ (22709873751419/50000000000000 : ℝ)^407
        have hw : |(2742961567/5000000000 : ℝ)|=(2742961567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323679469/625000000 : ℝ)|^535 ≤ (8421571391731/20000000000000 : ℝ)^407
        have hw : |(323679469/625000000 : ℝ)|=(323679469/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s2_1 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (167735089/312500000 : ℝ)*x 0 + (-2211177921/10000000000 : ℝ)*x 1 + (2589435519/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167735089/312500000 : ℝ)^535 ≤ (2758473442847/6250000000000 : ℝ)^407 := by
    have hnat : (167735089 : ℕ)^535*6250000000000^407 ≤ 2758473442847^407*312500000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167735089 312500000 2758473442847 6250000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211177921/10000000000 : ℝ)^535 ≤ (1719571616061/12500000000000 : ℝ)^407 := by
    have hnat : (2211177921 : ℕ)^535*12500000000000^407 ≤ 1719571616061^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211177921 10000000000 1719571616061 12500000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589435519/5000000000 : ℝ)^535 ≤ (42107851978151/100000000000000 : ℝ)^407 := by
    have hnat : (2589435519 : ℕ)^535*100000000000000^407 ≤ 42107851978151^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589435519 5000000000 42107851978151 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167735089/312500000 : ℝ), (-2211177921/10000000000 : ℝ), (2589435519/5000000000 : ℝ)] ![(2758473442847/6250000000000 : ℝ), (1719571616061/12500000000000 : ℝ), (42107851978151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167735089/312500000 : ℝ)|^535 ≤ (2758473442847/6250000000000 : ℝ)^407
        have hw : |(167735089/312500000 : ℝ)|=(167735089/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2211177921/10000000000 : ℝ)|^535 ≤ (1719571616061/12500000000000 : ℝ)^407
        have hw : |(-2211177921/10000000000 : ℝ)|=(2211177921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589435519/5000000000 : ℝ)|^535 ≤ (42107851978151/100000000000000 : ℝ)^407
        have hw : |(2589435519/5000000000 : ℝ)|=(2589435519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s2_2 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (268376109/500000000 : ℝ)*x 0 + (1035774339/2000000000 : ℝ)*x 1 + (-276397243/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268376109/500000000 : ℝ)^535 ≤ (2758472991583/6250000000000 : ℝ)^407 := by
    have hnat : (268376109 : ℕ)^535*6250000000000^407 ≤ 2758472991583^407*500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268376109 500000000 2758472991583 6250000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1035774339/2000000000 : ℝ)^535 ≤ (2105392950001/5000000000000 : ℝ)^407 := by
    have hnat : (1035774339 : ℕ)^535*5000000000000^407 ≤ 2105392950001^407*2000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1035774339 2000000000 2105392950001 5000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276397243/1250000000 : ℝ)^535 ≤ (6878286558291/50000000000000 : ℝ)^407 := by
    have hnat : (276397243 : ℕ)^535*50000000000000^407 ≤ 6878286558291^407*1250000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276397243 1250000000 6878286558291 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268376109/500000000 : ℝ), (1035774339/2000000000 : ℝ), (-276397243/1250000000 : ℝ)] ![(2758472991583/6250000000000 : ℝ), (2105392950001/5000000000000 : ℝ), (6878286558291/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268376109/500000000 : ℝ)|^535 ≤ (2758472991583/6250000000000 : ℝ)^407
        have hw : |(268376109/500000000 : ℝ)|=(268376109/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1035774339/2000000000 : ℝ)|^535 ≤ (2105392950001/5000000000000 : ℝ)^407
        have hw : |(1035774339/2000000000 : ℝ)|=(1035774339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276397243/1250000000 : ℝ)|^535 ≤ (6878286558291/50000000000000 : ℝ)^407
        have hw : |(-276397243/1250000000 : ℝ)|=(276397243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s2_3 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (4325583253/10000000000 : ℝ)*x 0 + (2008865063/5000000000 : ℝ)*x 1 + (290972559/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325583253/10000000000 : ℝ)^535 ≤ (33233958012153/100000000000000 : ℝ)^407 := by
    have hnat : (4325583253 : ℕ)^535*100000000000000^407 ≤ 33233958012153^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325583253 10000000000 33233958012153 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2008865063/5000000000 : ℝ)^535 ≤ (30160196763593/100000000000000 : ℝ)^407 := by
    have hnat : (2008865063 : ℕ)^535*100000000000000^407 ≤ 30160196763593^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2008865063 5000000000 30160196763593 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (290972559/625000000 : ℝ)^535 ≤ (18302922606299/50000000000000 : ℝ)^407 := by
    have hnat : (290972559 : ℕ)^535*50000000000000^407 ≤ 18302922606299^407*625000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      290972559 625000000 18302922606299 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325583253/10000000000 : ℝ), (2008865063/5000000000 : ℝ), (290972559/625000000 : ℝ)] ![(33233958012153/100000000000000 : ℝ), (30160196763593/100000000000000 : ℝ), (18302922606299/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325583253/10000000000 : ℝ)|^535 ≤ (33233958012153/100000000000000 : ℝ)^407
        have hw : |(4325583253/10000000000 : ℝ)|=(4325583253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2008865063/5000000000 : ℝ)|^535 ≤ (30160196763593/100000000000000 : ℝ)^407
        have hw : |(2008865063/5000000000 : ℝ)|=(2008865063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(290972559/625000000 : ℝ)|^535 ≤ (18302922606299/50000000000000 : ℝ)^407
        have hw : |(290972559/625000000 : ℝ)|=(290972559/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s2_4 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (-1026198373/5000000000 : ℝ)*x 0 + (207233791/400000000 : ℝ)*x 1 + (1370982963/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1026198373/5000000000 : ℝ)^535 ≤ (12472974556163/100000000000000 : ℝ)^407 := by
    have hnat : (1026198373 : ℕ)^535*100000000000000^407 ≤ 12472974556163^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1026198373 5000000000 12472974556163 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207233791/400000000 : ℝ)^535 ≤ (42128948102191/100000000000000 : ℝ)^407 := by
    have hnat : (207233791 : ℕ)^535*100000000000000^407 ≤ 42128948102191^407*400000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207233791 400000000 42128948102191 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370982963/2500000000 : ℝ)^535 ≤ (2269903866571/5000000000000 : ℝ)^407 := by
    have hnat : (1370982963 : ℕ)^535*5000000000000^407 ≤ 2269903866571^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370982963 2500000000 2269903866571 5000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1026198373/5000000000 : ℝ), (207233791/400000000 : ℝ), (1370982963/2500000000 : ℝ)] ![(12472974556163/100000000000000 : ℝ), (42128948102191/100000000000000 : ℝ), (2269903866571/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1026198373/5000000000 : ℝ)|^535 ≤ (12472974556163/100000000000000 : ℝ)^407
        have hw : |(-1026198373/5000000000 : ℝ)|=(1026198373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207233791/400000000 : ℝ)|^535 ≤ (42128948102191/100000000000000 : ℝ)^407
        have hw : |(207233791/400000000 : ℝ)|=(207233791/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1370982963/2500000000 : ℝ)|^535 ≤ (2269903866571/5000000000000 : ℝ)^407
        have hw : |(1370982963/2500000000 : ℝ)|=(1370982963/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s2_5 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (211542877/400000000 : ℝ)*x 0 + (-119132289/625000000 : ℝ)*x 1 + (1370982979/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211542877/400000000 : ℝ)^535 ≤ (43284197139103/100000000000000 : ℝ)^407 := by
    have hnat : (211542877 : ℕ)^535*100000000000000^407 ≤ 43284197139103^407*400000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211542877 400000000 43284197139103 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (119132289/625000000 : ℝ)^535 ≤ (2829431203607/25000000000000 : ℝ)^407 := by
    have hnat : (119132289 : ℕ)^535*25000000000000^407 ≤ 2829431203607^407*625000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119132289 625000000 2829431203607 25000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1370982979/2500000000 : ℝ)^535 ≤ (22699039013931/50000000000000 : ℝ)^407 := by
    have hnat : (1370982979 : ℕ)^535*50000000000000^407 ≤ 22699039013931^407*2500000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1370982979 2500000000 22699039013931 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211542877/400000000 : ℝ), (-119132289/625000000 : ℝ), (1370982979/2500000000 : ℝ)] ![(43284197139103/100000000000000 : ℝ), (2829431203607/25000000000000 : ℝ), (22699039013931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211542877/400000000 : ℝ)|^535 ≤ (43284197139103/100000000000000 : ℝ)^407
        have hw : |(211542877/400000000 : ℝ)|=(211542877/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-119132289/625000000 : ℝ)|^535 ≤ (2829431203607/25000000000000 : ℝ)^407
        have hw : |(-119132289/625000000 : ℝ)|=(119132289/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1370982979/2500000000 : ℝ)|^535 ≤ (22699039013931/50000000000000 : ℝ)^407
        have hw : |(1370982979/2500000000 : ℝ)|=(1370982979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s2_6 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2644286007/5000000000 : ℝ)*x 0 + (5483931859/10000000000 : ℝ)*x 1 + (-1906116581/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644286007/5000000000 : ℝ)^535 ≤ (21642099048303/50000000000000 : ℝ)^407 := by
    have hnat : (2644286007 : ℕ)^535*50000000000000^407 ≤ 21642099048303^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644286007 5000000000 21642099048303 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5483931859/10000000000 : ℝ)^535 ≤ (22699038703797/50000000000000 : ℝ)^407 := by
    have hnat : (5483931859 : ℕ)^535*50000000000000^407 ≤ 22699038703797^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5483931859 10000000000 22699038703797 50000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1906116581/10000000000 : ℝ)^535 ≤ (353678889963/3125000000000 : ℝ)^407 := by
    have hnat : (1906116581 : ℕ)^535*3125000000000^407 ≤ 353678889963^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1906116581 10000000000 353678889963 3125000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644286007/5000000000 : ℝ), (5483931859/10000000000 : ℝ), (-1906116581/10000000000 : ℝ)] ![(21642099048303/50000000000000 : ℝ), (22699038703797/50000000000000 : ℝ), (353678889963/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644286007/5000000000 : ℝ)|^535 ≤ (21642099048303/50000000000000 : ℝ)^407
        have hw : |(2644286007/5000000000 : ℝ)|=(2644286007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5483931859/10000000000 : ℝ)|^535 ≤ (22699038703797/50000000000000 : ℝ)^407
        have hw : |(5483931859/10000000000 : ℝ)|=(5483931859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1906116581/10000000000 : ℝ)|^535 ≤ (353678889963/3125000000000 : ℝ)^407
        have hw : |(-1906116581/10000000000 : ℝ)|=(1906116581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1320_s2_7 (p : ℝ) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ)) (x : Fin 3 → ℝ) :
    (2162866139/5000000000 : ℝ)*x 0 + (4651459777/10000000000 : ℝ)*x 1 + (4021872017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2162866139/5000000000 : ℝ)^535 ≤ (33235463087519/100000000000000 : ℝ)^407 := by
    have hnat : (2162866139 : ℕ)^535*100000000000000^407 ≤ 33235463087519^407*5000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2162866139 5000000000 33235463087519 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4651459777/10000000000 : ℝ)^535 ≤ (36563462858677/100000000000000 : ℝ)^407 := by
    have hnat : (4651459777 : ℕ)^535*100000000000000^407 ≤ 36563462858677^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4651459777 10000000000 36563462858677 100000000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4021872017/10000000000 : ℝ)^535 ≤ (188756712677/625000000000 : ℝ)^407 := by
    have hnat : (4021872017 : ℕ)^535*625000000000^407 ≤ 188756712677^407*10000000000^535 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4021872017 10000000000 188756712677 625000000000 535 407 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (535/128 : ℝ)) 535 407 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2162866139/5000000000 : ℝ), (4651459777/10000000000 : ℝ), (4021872017/10000000000 : ℝ)] ![(33235463087519/100000000000000 : ℝ), (36563462858677/100000000000000 : ℝ), (188756712677/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2162866139/5000000000 : ℝ)|^535 ≤ (33235463087519/100000000000000 : ℝ)^407
        have hw : |(2162866139/5000000000 : ℝ)|=(2162866139/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4651459777/10000000000 : ℝ)|^535 ≤ (36563462858677/100000000000000 : ℝ)^407
        have hw : |(4651459777/10000000000 : ℝ)|=(4651459777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4021872017/10000000000 : ℝ)|^535 ≤ (188756712677/625000000000 : ℝ)^407
        have hw : |(4021872017/10000000000 : ℝ)|=(4021872017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1320_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19629/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3341/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1213/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8097/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19629/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3341/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19629/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3341/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19629/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3341/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19629/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3341/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19629/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3341/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19629/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3341/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3341/50000 : ℝ) ^ (4279/1024 : ℝ) ≤ (24584071746917/2000000000000000000 : ℝ) := by
    have hpowers : (3341/50000 : ℝ)^4279 ≤ (24584071746917/2000000000000000000 : ℝ)^1024 := by
      have hnat : (3341 : ℕ)^4279*2000000000000000000^1024 ≤ 24584071746917^1024*50000^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3341 50000 24584071746917 2000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3341/50000 : ℝ)) (X := (24584071746917/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19629/100000 : ℝ) ^ (4279/1024 : ℝ) ≤ (110975183042031869/100000000000000000000 : ℝ) := by
    have hpowers : (19629/100000 : ℝ)^4279 ≤ (110975183042031869/100000000000000000000 : ℝ)^1024 := by
      have hnat : (19629 : ℕ)^4279*100000000000000000000^1024 ≤ 110975183042031869^1024*100000^4279 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19629 100000 110975183042031869 100000000000000000000 4279 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19629/100000 : ℝ)) (X := (110975183042031869/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1000024584071746917/1000000000000000000 : ℝ) ≤ (10000058831161681/10000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (1000024584071746917/1000000000000000000 : ℝ)^1024 ≤ (10000058831161681/10000000000000000 : ℝ)^4279 := by
      have hnat : (1000024584071746917 : ℕ)^1024*10000000000000000^4279 ≤ 10000058831161681^4279*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000024584071746917 1000000000000000000 10000058831161681 10000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000058831161681/10000000000000000 : ℝ)) (X := (1000024584071746917/1000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100112204386629377719/100000000000000000000 : ℝ) ≤ (250067099959137/250000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (100112204386629377719/100000000000000000000 : ℝ)^1024 ≤ (250067099959137/250000000000000 : ℝ)^4279 := by
      have hnat : (100112204386629377719 : ℕ)^1024*250000000000000^4279 ≤ 250067099959137^4279*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100112204386629377719 100000000000000000000 250067099959137 250000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250067099959137/250000000000000 : ℝ)) (X := (100112204386629377719/100000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50110975183042031869/50000000000000000000 : ℝ) ≤ (10005309165569279/10000000000000000 : ℝ) ^ (4279/1024 : ℝ) := by
    have hpowers : (50110975183042031869/50000000000000000000 : ℝ)^1024 ≤ (10005309165569279/10000000000000000 : ℝ)^4279 := by
      have hnat : (50110975183042031869 : ℕ)^1024*10000000000000000^4279 ≤ 10005309165569279^4279*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50110975183042031869 50000000000000000000 10005309165569279 10000000000000000 1024 4279 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005309165569279/10000000000000000 : ℝ)) (X := (50110975183042031869/50000000000000000000 : ℝ)) (by norm_num) 4279 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(24584071746917/2000000000000000000 : ℝ) ≤ ((129435678952538714071/129470000000000000000 : ℝ)+2*(2625167203799/1294700000000000 : ℝ)*(3341/50000 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (129435678952538714071/129470000000000000000 : ℝ)+2*(2625167203799/1294700000000000 : ℝ)*(3341/50000 : ℝ)=(10000058831161681/10000000000000000 : ℝ) by norm_num, show 1+2*(24584071746917/2000000000000000000 : ℝ)=(1000024584071746917/1000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(110975183042031869/100000000000000000000 : ℝ)+(24584071746917/2000000000000000000 : ℝ) ≤ ((129435678952538714071/129470000000000000000 : ℝ)+(2625167203799/1294700000000000 : ℝ)*((19629/100000 : ℝ)+(3341/50000 : ℝ)))^(4279/1024 : ℝ) := by
    rw [show (129435678952538714071/129470000000000000000 : ℝ)+(2625167203799/1294700000000000 : ℝ)*((19629/100000 : ℝ)+(3341/50000 : ℝ))=(250067099959137/250000000000000 : ℝ) by norm_num, show 1+(110975183042031869/100000000000000000000 : ℝ)+(24584071746917/2000000000000000000 : ℝ)=(100112204386629377719/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(110975183042031869/100000000000000000000 : ℝ) ≤ ((129435678952538714071/129470000000000000000 : ℝ)+2*(2625167203799/1294700000000000 : ℝ)*(19629/100000 : ℝ))^(4279/1024 : ℝ) := by
    rw [show (129435678952538714071/129470000000000000000 : ℝ)+2*(2625167203799/1294700000000000 : ℝ)*(19629/100000 : ℝ)=(10005309165569279/10000000000000000 : ℝ) by norm_num, show 1+2*(110975183042031869/100000000000000000000 : ℝ)=(50110975183042031869/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (129435678952538714071/129470000000000000000 : ℝ)*(X 1 0+X 2 0)+(2625167203799/1294700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (3341/50000 : ℝ)) (hi := (19629/100000 : ℝ)) (c := (129435678952538714071/129470000000000000000 : ℝ)) (alpha := (2625167203799/1294700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (129435678952538714071/129470000000000000000 : ℝ)*(X 0 1+X 2 1)+(2625167203799/1294700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (3341/50000 : ℝ)) (hi := (19629/100000 : ℝ)) (c := (129435678952538714071/129470000000000000000 : ℝ)) (alpha := (2625167203799/1294700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (129435678952538714071/129470000000000000000 : ℝ)*(X 0 2+X 1 2)+(2625167203799/1294700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4279/1024 : ℝ)) (lo := (3341/50000 : ℝ)) (hi := (19629/100000 : ℝ)) (c := (129435678952538714071/129470000000000000000 : ℝ)) (alpha := (2625167203799/1294700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2052324263/10000000000 : ℝ)*X 0 0+(2742961567/5000000000 : ℝ)*X 0 1+(323679469/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((167735089/312500000 : ℝ)*X 1 0+(-2211177921/10000000000 : ℝ)*X 1 1+(2589435519/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268376109/500000000 : ℝ)*X 2 0+(1035774339/2000000000 : ℝ)*X 2 1+(-276397243/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325583253/10000000000 : ℝ)*X 0 0+(2008865063/5000000000 : ℝ)*X 0 1+(290972559/625000000 : ℝ)*X 0 2+(4325583253/10000000000 : ℝ)*X 1 0+(2008865063/5000000000 : ℝ)*X 1 1+(290972559/625000000 : ℝ)*X 1 2+(4325583253/10000000000 : ℝ)*X 2 0+(2008865063/5000000000 : ℝ)*X 2 1+(290972559/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1026198373/5000000000 : ℝ)*X 0 0+(207233791/400000000 : ℝ)*X 0 1+(1370982963/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((211542877/400000000 : ℝ)*X 1 0+(-119132289/625000000 : ℝ)*X 1 1+(1370982979/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2644286007/5000000000 : ℝ)*X 2 0+(5483931859/10000000000 : ℝ)*X 2 1+(-1906116581/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2162866139/5000000000 : ℝ)*X 0 0+(4651459777/10000000000 : ℝ)*X 0 1+(4021872017/10000000000 : ℝ)*X 0 2+(2162866139/5000000000 : ℝ)*X 1 0+(4651459777/10000000000 : ℝ)*X 1 1+(4021872017/10000000000 : ℝ)*X 1 2+(2162866139/5000000000 : ℝ)*X 2 0+(4651459777/10000000000 : ℝ)*X 2 1+(4021872017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1320_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12125810000767616280589946883/3236750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (884278469/50000000000000 : ℝ)*(base19) + (804622793/100000000000000 : ℝ)*(base23) + (299840099/100000000000000 : ℝ)*(lower2) + (667857519/100000000000000 : ℝ)*(upper3) + (106271751/100000000000000 : ℝ)*(upper5) + (1206158564141197/50000000000000 : ℝ)*(major0) + (1206158564141197/50000000000000 : ℝ)*(major1) + (1206158564141197/50000000000000 : ℝ)*(major2) + (3256792469669967/100000000000000 : ℝ)*(sp0) + (407098972940267/12500000000000 : ℝ)*(sp1) + (3256792747456281/100000000000000 : ℝ)*(sp2) + (783912222656319/50000000000000 : ℝ)*(sp3) + (541204553/50000000000000 : ℝ)*(sp4) + (645371867/4000000000000 : ℝ)*(sp7) + (783920289804657/50000000000000 : ℝ)*(f.failure) + (1628396776039537/50000000000000 : ℝ)*(f.sum) + (114410734656561/64735000000000000000000000000 : ℝ)*base65 + (58122160254078653/53500000000000000000000000000000 : ℝ)*base68 + (398077575980078653/53500000000000000000000000000000 : ℝ)*base70 + (72747926107578653/53500000000000000000000000000000 : ℝ)*base72 + (42906658530661/64735000000000000000000000000 : ℝ)*base73 + (189060164088078653/53500000000000000000000000000000 : ℝ)*base76 + (177289561089578653/53500000000000000000000000000000 : ℝ)*base78 + (613346688588578653/53500000000000000000000000000000 : ℝ)*base80 + (51546424097199/64735000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (67392143/5000000000000000000000 : ℝ)*base89 + (67392143/5000000000000000000000 : ℝ)*base91 + (67392143/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (18444694309462576775287650129/3236750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1149428143/100000000000000 : ℝ)*(base19) + (1397058657/100000000000000 : ℝ)*(base23) + (33276333/20000000000000 : ℝ)*(upper3) + (898949/1250000000000 : ℝ)*(lower4) + (16782609/25000000000000 : ℝ)*(upper5) + (1221930281016733/50000000000000 : ℝ)*(major0) + (1221930281016733/50000000000000 : ℝ)*(major1) + (1221930281016733/50000000000000 : ℝ)*(major2) + (12254076619/100000000000000 : ℝ)*(sp1) + (3202725653/20000000000000 : ℝ)*(sp2) + (3299379287348089/100000000000000 : ℝ)*(sp4) + (3299365883843327/100000000000000 : ℝ)*(sp5) + (3299361876661167/100000000000000 : ℝ)*(sp6) + (63533665870723/4000000000000 : ℝ)*(sp7) + (63533665870723/4000000000000 : ℝ)*(f.failure) + (3299379287348089/100000000000000 : ℝ)*(f.sum) + (32932502454087/32367500000000000000000000000 : ℝ)*base65 + (161313715547559917/53500000000000000000000000000000 : ℝ)*base68 + (2081498316940083/53500000000000000000000000000000 : ℝ)*base69 + (7217985852059917/53500000000000000000000000000000 : ℝ)*base72 + (49747546809373/32367500000000000000000000000 : ℝ)*base74 + (178350152774059917/53500000000000000000000000000000 : ℝ)*base76 + (82484787319440083/53500000000000000000000000000000 : ℝ)*base77 + (33876375983059917/53500000000000000000000000000000 : ℝ)*base80 + (51173089520327/32367500000000000000000000000 : ℝ)*base81 + (644477/400000000000000000000 : ℝ)*base89 + (644477/400000000000000000000 : ℝ)*base91 + (644477/400000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1320_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19629/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3341/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1213/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1320_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1320_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1213/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1320_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1320_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1320_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4279/1024 : ℝ) ≤ p) (hpb : p ≤ (535/128 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153862399/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1213/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8097/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1320_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
