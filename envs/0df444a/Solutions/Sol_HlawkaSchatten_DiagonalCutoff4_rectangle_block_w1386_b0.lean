-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1386_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:24:19.509106+00:00
-- url     : https://prove2.me/submissions/5bb81a33-b3c8-493d-888a-ff346d539098

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
theorem support_rectangle_w1386_s0_0 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-891708971/5000000000 : ℝ)*x 0 + (373633077/625000000 : ℝ)*x 1 + (4821297889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (891708971/5000000000 : ℝ)^2173 ≤ (10482222509199/100000000000000 : ℝ)^1661 := by
    have hnat : (891708971 : ℕ)^2173*100000000000000^1661 ≤ 10482222509199^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      891708971 5000000000 10482222509199 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (373633077/625000000 : ℝ)^2173 ≤ (2550715340661/5000000000000 : ℝ)^1661 := by
    have hnat : (373633077 : ℕ)^2173*5000000000000^1661 ≤ 2550715340661^1661*625000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373633077 625000000 2550715340661 5000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4821297889/10000000000 : ℝ)^2173 ≤ (3850347065241/10000000000000 : ℝ)^1661 := by
    have hnat : (4821297889 : ℕ)^2173*10000000000000^1661 ≤ 3850347065241^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4821297889 10000000000 3850347065241 10000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-891708971/5000000000 : ℝ), (373633077/625000000 : ℝ), (4821297889/10000000000 : ℝ)] ![(10482222509199/100000000000000 : ℝ), (2550715340661/5000000000000 : ℝ), (3850347065241/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-891708971/5000000000 : ℝ)|^2173 ≤ (10482222509199/100000000000000 : ℝ)^1661
        have hw : |(-891708971/5000000000 : ℝ)|=(891708971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(373633077/625000000 : ℝ)|^2173 ≤ (2550715340661/5000000000000 : ℝ)^1661
        have hw : |(373633077/625000000 : ℝ)|=(373633077/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4821297889/10000000000 : ℝ)|^2173 ≤ (3850347065241/10000000000000 : ℝ)^1661
        have hw : |(4821297889/10000000000 : ℝ)|=(4821297889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s0_1 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2748446157/5000000000 : ℝ)*x 0 + (-2438880723/10000000000 : ℝ)*x 1 + (2410649307/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2748446157/5000000000 : ℝ)^2173 ≤ (5713719110761/12500000000000 : ℝ)^1661 := by
    have hnat : (2748446157 : ℕ)^2173*12500000000000^1661 ≤ 5713719110761^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2748446157 5000000000 5713719110761 12500000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2438880723/10000000000 : ℝ)^2173 ≤ (3946692216623/25000000000000 : ℝ)^1661 := by
    have hnat : (2438880723 : ℕ)^2173*25000000000000^1661 ≤ 3946692216623^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2438880723 10000000000 3946692216623 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2410649307/5000000000 : ℝ)^2173 ≤ (7700695645417/20000000000000 : ℝ)^1661 := by
    have hnat : (2410649307 : ℕ)^2173*20000000000000^1661 ≤ 7700695645417^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2410649307 5000000000 7700695645417 20000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2748446157/5000000000 : ℝ), (-2438880723/10000000000 : ℝ), (2410649307/5000000000 : ℝ)] ![(5713719110761/12500000000000 : ℝ), (3946692216623/25000000000000 : ℝ), (7700695645417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2748446157/5000000000 : ℝ)|^2173 ≤ (5713719110761/12500000000000 : ℝ)^1661
        have hw : |(2748446157/5000000000 : ℝ)|=(2748446157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2438880723/10000000000 : ℝ)|^2173 ≤ (3946692216623/25000000000000 : ℝ)^1661
        have hw : |(-2438880723/10000000000 : ℝ)|=(2438880723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2410649307/5000000000 : ℝ)|^2173 ≤ (7700695645417/20000000000000 : ℝ)^1661
        have hw : |(2410649307/5000000000 : ℝ)|=(2410649307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s0_2 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (274844607/500000000 : ℝ)*x 0 + (37666389/78125000 : ℝ)*x 1 + (-2438881961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (274844607/500000000 : ℝ)^2173 ≤ (22854875496587/50000000000000 : ℝ)^1661 := by
    have hnat : (274844607 : ℕ)^2173*50000000000000^1661 ≤ 22854875496587^1661*500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274844607 500000000 22854875496587 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37666389/78125000 : ℝ)^2173 ≤ (38503469638971/100000000000000 : ℝ)^1661 := by
    have hnat : (37666389 : ℕ)^2173*100000000000000^1661 ≤ 38503469638971^1661*78125000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37666389 78125000 38503469638971 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2438881961/10000000000 : ℝ)^2173 ≤ (3157355870033/20000000000000 : ℝ)^1661 := by
    have hnat : (2438881961 : ℕ)^2173*20000000000000^1661 ≤ 3157355870033^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2438881961 10000000000 3157355870033 20000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(274844607/500000000 : ℝ), (37666389/78125000 : ℝ), (-2438881961/10000000000 : ℝ)] ![(22854875496587/50000000000000 : ℝ), (38503469638971/100000000000000 : ℝ), (3157355870033/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(274844607/500000000 : ℝ)|^2173 ≤ (22854875496587/50000000000000 : ℝ)^1661
        have hw : |(274844607/500000000 : ℝ)|=(274844607/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(37666389/78125000 : ℝ)|^2173 ≤ (38503469638971/100000000000000 : ℝ)^1661
        have hw : |(37666389/78125000 : ℝ)|=(37666389/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2438881961/10000000000 : ℝ)|^2173 ≤ (3157355870033/20000000000000 : ℝ)^1661
        have hw : |(-2438881961/10000000000 : ℝ)|=(2438881961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s0_3 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4172233673/10000000000 : ℝ)*x 0 + (388083817/1250000000 : ℝ)*x 1 + (2783955031/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4172233673/10000000000 : ℝ)^2173 ≤ (31867500033321/100000000000000 : ℝ)^1661 := by
    have hnat : (4172233673 : ℕ)^2173*100000000000000^1661 ≤ 31867500033321^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172233673 10000000000 31867500033321 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (388083817/1250000000 : ℝ)^2173 ≤ (21648624031301/100000000000000 : ℝ)^1661 := by
    have hnat : (388083817 : ℕ)^2173*100000000000000^1661 ≤ 21648624031301^1661*1250000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      388083817 1250000000 21648624031301 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2783955031/5000000000 : ℝ)^2173 ≤ (11620968982281/25000000000000 : ℝ)^1661 := by
    have hnat : (2783955031 : ℕ)^2173*25000000000000^1661 ≤ 11620968982281^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2783955031 5000000000 11620968982281 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4172233673/10000000000 : ℝ), (388083817/1250000000 : ℝ), (2783955031/5000000000 : ℝ)] ![(31867500033321/100000000000000 : ℝ), (21648624031301/100000000000000 : ℝ), (11620968982281/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4172233673/10000000000 : ℝ)|^2173 ≤ (31867500033321/100000000000000 : ℝ)^1661
        have hw : |(4172233673/10000000000 : ℝ)|=(4172233673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(388083817/1250000000 : ℝ)|^2173 ≤ (21648624031301/100000000000000 : ℝ)^1661
        have hw : |(388083817/1250000000 : ℝ)|=(388083817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2783955031/5000000000 : ℝ)|^2173 ≤ (11620968982281/25000000000000 : ℝ)^1661
        have hw : |(2783955031/5000000000 : ℝ)|=(2783955031/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s0_4 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1787648599/10000000000 : ℝ)*x 0 + (75796697/156250000 : ℝ)*x 1 + (1486844307/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1787648599/10000000000 : ℝ)^2173 ≤ (2628691362989/25000000000000 : ℝ)^1661 := by
    have hnat : (1787648599 : ℕ)^2173*25000000000000^1661 ≤ 2628691362989^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1787648599 10000000000 2628691362989 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (75796697/156250000 : ℝ)^2173 ≤ (776279363587/2000000000000 : ℝ)^1661 := by
    have hnat : (75796697 : ℕ)^2173*2000000000000^1661 ≤ 776279363587^1661*156250000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      75796697 156250000 776279363587 2000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1486844307/2500000000 : ℝ)^2173 ≤ (25335633178843/50000000000000 : ℝ)^1661 := by
    have hnat : (1486844307 : ℕ)^2173*50000000000000^1661 ≤ 25335633178843^1661*2500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1486844307 2500000000 25335633178843 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1787648599/10000000000 : ℝ), (75796697/156250000 : ℝ), (1486844307/2500000000 : ℝ)] ![(2628691362989/25000000000000 : ℝ), (776279363587/2000000000000 : ℝ), (25335633178843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1787648599/10000000000 : ℝ)|^2173 ≤ (2628691362989/25000000000000 : ℝ)^1661
        have hw : |(-1787648599/10000000000 : ℝ)|=(1787648599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(75796697/156250000 : ℝ)|^2173 ≤ (776279363587/2000000000000 : ℝ)^1661
        have hw : |(75796697/156250000 : ℝ)|=(75796697/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1486844307/2500000000 : ℝ)|^2173 ≤ (25335633178843/50000000000000 : ℝ)^1661
        have hw : |(1486844307/2500000000 : ℝ)|=(1486844307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s0_5 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1036272511/2000000000 : ℝ)*x 0 + (-65640141/500000000 : ℝ)*x 1 + (5947377043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1036272511/2000000000 : ℝ)^2173 ≤ (42307941818533/100000000000000 : ℝ)^1661 := by
    have hnat : (1036272511 : ℕ)^2173*100000000000000^1661 ≤ 42307941818533^1661*2000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036272511 2000000000 42307941818533 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (65640141/500000000 : ℝ)^2173 ≤ (7020793871929/100000000000000 : ℝ)^1661 := by
    have hnat : (65640141 : ℕ)^2173*100000000000000^1661 ≤ 7020793871929^1661*500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65640141 500000000 7020793871929 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5947377043/10000000000 : ℝ)^2173 ≤ (25335632147821/50000000000000 : ℝ)^1661 := by
    have hnat : (5947377043 : ℕ)^2173*50000000000000^1661 ≤ 25335632147821^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5947377043 10000000000 25335632147821 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1036272511/2000000000 : ℝ), (-65640141/500000000 : ℝ), (5947377043/10000000000 : ℝ)] ![(42307941818533/100000000000000 : ℝ), (7020793871929/100000000000000 : ℝ), (25335632147821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1036272511/2000000000 : ℝ)|^2173 ≤ (42307941818533/100000000000000 : ℝ)^1661
        have hw : |(1036272511/2000000000 : ℝ)|=(1036272511/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-65640141/500000000 : ℝ)|^2173 ≤ (7020793871929/100000000000000 : ℝ)^1661
        have hw : |(-65640141/500000000 : ℝ)|=(65640141/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5947377043/10000000000 : ℝ)|^2173 ≤ (25335632147821/50000000000000 : ℝ)^1661
        have hw : |(5947377043/10000000000 : ℝ)|=(5947377043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s0_6 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5181362223/10000000000 : ℝ)*x 0 + (5947377151/10000000000 : ℝ)*x 1 + (-262560631/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5181362223/10000000000 : ℝ)^2173 ≤ (42307938271983/100000000000000 : ℝ)^1661 := by
    have hnat : (5181362223 : ℕ)^2173*100000000000000^1661 ≤ 42307938271983^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5181362223 10000000000 42307938271983 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5947377151/10000000000 : ℝ)^2173 ≤ (5067126549943/10000000000000 : ℝ)^1661 := by
    have hnat : (5947377151 : ℕ)^2173*10000000000000^1661 ≤ 5067126549943^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5947377151 10000000000 5067126549943 10000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (262560631/2000000000 : ℝ)^2173 ≤ (1404159243147/20000000000000 : ℝ)^1661 := by
    have hnat : (262560631 : ℕ)^2173*20000000000000^1661 ≤ 1404159243147^1661*2000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262560631 2000000000 1404159243147 20000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5181362223/10000000000 : ℝ), (5947377151/10000000000 : ℝ), (-262560631/2000000000 : ℝ)] ![(42307938271983/100000000000000 : ℝ), (5067126549943/10000000000000 : ℝ), (1404159243147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5181362223/10000000000 : ℝ)|^2173 ≤ (42307938271983/100000000000000 : ℝ)^1661
        have hw : |(5181362223/10000000000 : ℝ)|=(5181362223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5947377151/10000000000 : ℝ)|^2173 ≤ (5067126549943/10000000000000 : ℝ)^1661
        have hw : |(5947377151/10000000000 : ℝ)|=(5947377151/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-262560631/2000000000 : ℝ)|^2173 ≤ (1404159243147/20000000000000 : ℝ)^1661
        have hw : |(-262560631/2000000000 : ℝ)|=(262560631/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s0_7 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4181239487/10000000000 : ℝ)*x 0 + (1376172307/2500000000 : ℝ)*x 1 + (396268851/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4181239487/10000000000 : ℝ)^2173 ≤ (31957519580219/100000000000000 : ℝ)^1661 := by
    have hnat : (4181239487 : ℕ)^2173*100000000000000^1661 ≤ 31957519580219^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4181239487 10000000000 31957519580219 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1376172307/2500000000 : ℝ)^2173 ≤ (45794592636693/100000000000000 : ℝ)^1661 := by
    have hnat : (1376172307 : ℕ)^2173*100000000000000^1661 ≤ 45794592636693^1661*2500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1376172307 2500000000 45794592636693 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (396268851/1250000000 : ℝ)^2173 ≤ (22247887767359/100000000000000 : ℝ)^1661 := by
    have hnat : (396268851 : ℕ)^2173*100000000000000^1661 ≤ 22247887767359^1661*1250000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      396268851 1250000000 22247887767359 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4181239487/10000000000 : ℝ), (1376172307/2500000000 : ℝ), (396268851/1250000000 : ℝ)] ![(31957519580219/100000000000000 : ℝ), (45794592636693/100000000000000 : ℝ), (22247887767359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4181239487/10000000000 : ℝ)|^2173 ≤ (31957519580219/100000000000000 : ℝ)^1661
        have hw : |(4181239487/10000000000 : ℝ)|=(4181239487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1376172307/2500000000 : ℝ)|^2173 ≤ (45794592636693/100000000000000 : ℝ)^1661
        have hw : |(1376172307/2500000000 : ℝ)|=(1376172307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(396268851/1250000000 : ℝ)|^2173 ≤ (22247887767359/100000000000000 : ℝ)^1661
        have hw : |(396268851/1250000000 : ℝ)|=(396268851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1386_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1739/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13279/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4345/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4345 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4345*1^1024 ≤ 0^1024*1^4345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4345 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4345/1024 : ℝ) ≤ (1024342661628814807/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4345 ≤ (1024342661628814807/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4345*50000000000000000000^1024 ≤ 1024342661628814807^1024*5^4345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1024342661628814807 50000000000000000000 4345 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1024342661628814807/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4345 := by
      have hnat : (1 : ℕ)^1024*1^4345 ≤ 1^4345*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51024342661628814807/50000000000000000000 : ℝ) ≤ (2511977123851921/2500000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (51024342661628814807/50000000000000000000 : ℝ)^1024 ≤ (2511977123851921/2500000000000000 : ℝ)^4345 := by
      have hnat : (51024342661628814807 : ℕ)^1024*2500000000000000^4345 ≤ 2511977123851921^4345*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51024342661628814807 50000000000000000000 2511977123851921 2500000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2511977123851921/2500000000000000 : ℝ)) (X := (51024342661628814807/50000000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26024342661628814807/25000000000000000000 : ℝ) ≤ (1261977123851921/1250000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (26024342661628814807/25000000000000000000 : ℝ)^1024 ≤ (1261977123851921/1250000000000000 : ℝ)^4345 := by
      have hnat : (26024342661628814807 : ℕ)^1024*1250000000000000^4345 ≤ 1261977123851921^4345*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26024342661628814807 25000000000000000000 1261977123851921 1250000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1261977123851921/1250000000000000 : ℝ)) (X := (26024342661628814807/25000000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(11977123851921/1000000000000000 : ℝ)*(0 : ℝ))^(4345/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11977123851921/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1024342661628814807/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(11977123851921/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4345/1024 : ℝ) := by
    rw [show (1 : ℝ)+(11977123851921/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2511977123851921/2500000000000000 : ℝ) by norm_num, show 1+(1024342661628814807/50000000000000000000 : ℝ)+(0 : ℝ)=(51024342661628814807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1024342661628814807/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(11977123851921/1000000000000000 : ℝ)*(2/5 : ℝ))^(4345/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(11977123851921/1000000000000000 : ℝ)*(2/5 : ℝ)=(1261977123851921/1250000000000000 : ℝ) by norm_num, show 1+2*(1024342661628814807/50000000000000000000 : ℝ)=(26024342661628814807/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(11977123851921/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11977123851921/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(11977123851921/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11977123851921/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(11977123851921/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (11977123851921/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-891708971/5000000000 : ℝ)*X 0 0+(373633077/625000000 : ℝ)*X 0 1+(4821297889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2748446157/5000000000 : ℝ)*X 1 0+(-2438880723/10000000000 : ℝ)*X 1 1+(2410649307/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((274844607/500000000 : ℝ)*X 2 0+(37666389/78125000 : ℝ)*X 2 1+(-2438881961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4172233673/10000000000 : ℝ)*X 0 0+(388083817/1250000000 : ℝ)*X 0 1+(2783955031/5000000000 : ℝ)*X 0 2+(4172233673/10000000000 : ℝ)*X 1 0+(388083817/1250000000 : ℝ)*X 1 1+(2783955031/5000000000 : ℝ)*X 1 2+(4172233673/10000000000 : ℝ)*X 2 0+(388083817/1250000000 : ℝ)*X 2 1+(2783955031/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1787648599/10000000000 : ℝ)*X 0 0+(75796697/156250000 : ℝ)*X 0 1+(1486844307/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1036272511/2000000000 : ℝ)*X 1 0+(-65640141/500000000 : ℝ)*X 1 1+(5947377043/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5181362223/10000000000 : ℝ)*X 2 0+(5947377151/10000000000 : ℝ)*X 2 1+(-262560631/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4181239487/10000000000 : ℝ)*X 0 0+(1376172307/2500000000 : ℝ)*X 0 1+(396268851/1250000000 : ℝ)*X 0 2+(4181239487/10000000000 : ℝ)*X 1 0+(1376172307/2500000000 : ℝ)*X 1 1+(396268851/1250000000 : ℝ)*X 1 2+(4181239487/10000000000 : ℝ)*X 2 0+(1376172307/2500000000 : ℝ)*X 2 1+(396268851/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (192697922844492247514103/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18500327/6250000000000 : ℝ)*(base1) + (1802755111/100000000000000 : ℝ)*(base19) + (887695969/50000000000000 : ℝ)*(base23) + (341004399/100000000000000 : ℝ)*(upper3) + (1184177/12500000000000 : ℝ)*(upper5) + (635207852782819/100000000000000 : ℝ)*(major0) + (635207852782819/100000000000000 : ℝ)*(major1) + (635207852782819/100000000000000 : ℝ)*(major2) + (172887337367237/20000000000000 : ℝ)*(sp0) + (864439139688239/100000000000000 : ℝ)*(sp1) + (216109791762853/25000000000000 : ℝ)*(sp2) + (50746414140393/12500000000000 : ℝ)*(sp3) + (4551612397/100000000000000 : ℝ)*(sp4) + (579412669/20000000000000 : ℝ)*(sp7) + (405974506191721/100000000000000 : ℝ)*(f.failure) + (17288818848867/2000000000000 : ℝ)*(f.sum) + (103859386245299/50000000000000000000000000000 : ℝ)*base65 + (414806285054701/100000000000000000000000000000 : ℝ)*base68 + (671478662045299/100000000000000000000000000000 : ℝ)*base69 + (28397631645299/100000000000000000000000000000 : ℝ)*base71 + (27635473404701/50000000000000000000000000000 : ℝ)*base74 + (106159485545299/100000000000000000000000000000 : ℝ)*base75 + (56968245299/100000000000000000000000000000 : ℝ)*base77 + (295171185854701/100000000000000000000000000000 : ℝ)*base80 + (333838891145299/50000000000000000000000000000 : ℝ)*base81 + (15212119/10000000000000000000000 : ℝ)*base90 + (15212119/10000000000000000000000 : ℝ)*base92 + (15212119/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34119308208917243887983/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (838126451/50000000000000 : ℝ)*(base19) + (808071891/50000000000000 : ℝ)*(base23) + (83263459/50000000000000 : ℝ)*(base32) + (46881099/20000000000000 : ℝ)*(upper3) + (78209529/50000000000000 : ℝ)*(upper5) + (335108702045941/50000000000000 : ℝ)*(major0) + (335108702045941/50000000000000 : ℝ)*(major1) + (335108702045941/50000000000000 : ℝ)*(major2) + (3801183163/100000000000000 : ℝ)*(sp1) + (943453217/25000000000000 : ℝ)*(sp2) + (45604237228067/5000000000000 : ℝ)*(sp4) + (36483170685011/4000000000000 : ℝ)*(sp5) + (91207935460469/10000000000000 : ℝ)*(sp6) + (428349669633449/100000000000000 : ℝ)*(sp7) + (428349836160367/100000000000000 : ℝ)*(f.failure) + (45604237228067/5000000000000 : ℝ)*(f.sum) + (8792526972339/25000000000000000000000000000 : ℝ)*base66 + (58236681497339/50000000000000000000000000000 : ℝ)*base68 + (261253692497339/50000000000000000000000000000 : ℝ)*base70 + (120175950397339/50000000000000000000000000000 : ℝ)*base72 + (29252702472339/25000000000000000000000000000 : ℝ)*base74 + (266600311847339/50000000000000000000000000000 : ℝ)*base76 + (51410779547339/50000000000000000000000000000 : ℝ)*base78 + (63972772202661/50000000000000000000000000000 : ℝ)*base79 + (88599219247339/25000000000000000000000000000 : ℝ)*base82 + (12400687/10000000000000000000000 : ℝ)*base89 + (12400687/10000000000000000000000 : ℝ)*base91 + (12400687/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1386_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1739/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13279/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1386_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1386_s1_0 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-980952329/5000000000 : ℝ)*x 0 + (1124590317/2000000000 : ℝ)*x 1 + (5062118767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (980952329/5000000000 : ℝ)^2173 ≤ (2968843146993/25000000000000 : ℝ)^1661 := by
    have hnat : (980952329 : ℕ)^2173*25000000000000^1661 ≤ 2968843146993^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      980952329 5000000000 2968843146993 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1124590317/2000000000 : ℝ)^2173 ≤ (1177148764487/2500000000000 : ℝ)^1661 := by
    have hnat : (1124590317 : ℕ)^2173*2500000000000^1661 ≤ 1177148764487^1661*2000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1124590317 2000000000 1177148764487 2500000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5062118767/10000000000 : ℝ)^2173 ≤ (41038676817359/100000000000000 : ℝ)^1661 := by
    have hnat : (5062118767 : ℕ)^2173*100000000000000^1661 ≤ 41038676817359^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5062118767 10000000000 41038676817359 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-980952329/5000000000 : ℝ), (1124590317/2000000000 : ℝ), (5062118767/10000000000 : ℝ)] ![(2968843146993/25000000000000 : ℝ), (1177148764487/2500000000000 : ℝ), (41038676817359/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-980952329/5000000000 : ℝ)|^2173 ≤ (2968843146993/25000000000000 : ℝ)^1661
        have hw : |(-980952329/5000000000 : ℝ)|=(980952329/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1124590317/2000000000 : ℝ)|^2173 ≤ (1177148764487/2500000000000 : ℝ)^1661
        have hw : |(1124590317/2000000000 : ℝ)|=(1124590317/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5062118767/10000000000 : ℝ)|^2173 ≤ (41038676817359/100000000000000 : ℝ)^1661
        have hw : |(5062118767/10000000000 : ℝ)|=(5062118767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s1_1 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5401169807/10000000000 : ℝ)*x 0 + (-2260085663/10000000000 : ℝ)*x 1 + (5062120209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5401169807/10000000000 : ℝ)^2173 ≤ (1116780281843/2500000000000 : ℝ)^1661 := by
    have hnat : (5401169807 : ℕ)^2173*2500000000000^1661 ≤ 1116780281843^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5401169807 10000000000 1116780281843 2500000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2260085663/10000000000 : ℝ)^2173 ≤ (14290096600159/100000000000000 : ℝ)^1661 := by
    have hnat : (2260085663 : ℕ)^2173*100000000000000^1661 ≤ 14290096600159^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260085663 10000000000 14290096600159 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5062120209/10000000000 : ℝ)^2173 ≤ (20519346055597/50000000000000 : ℝ)^1661 := by
    have hnat : (5062120209 : ℕ)^2173*50000000000000^1661 ≤ 20519346055597^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5062120209 10000000000 20519346055597 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5401169807/10000000000 : ℝ), (-2260085663/10000000000 : ℝ), (5062120209/10000000000 : ℝ)] ![(1116780281843/2500000000000 : ℝ), (14290096600159/100000000000000 : ℝ), (20519346055597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5401169807/10000000000 : ℝ)|^2173 ≤ (1116780281843/2500000000000 : ℝ)^1661
        have hw : |(5401169807/10000000000 : ℝ)|=(5401169807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2260085663/10000000000 : ℝ)|^2173 ≤ (14290096600159/100000000000000 : ℝ)^1661
        have hw : |(-2260085663/10000000000 : ℝ)|=(2260085663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5062120209/10000000000 : ℝ)|^2173 ≤ (20519346055597/50000000000000 : ℝ)^1661
        have hw : |(5062120209/10000000000 : ℝ)|=(5062120209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s1_2 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2700585301/5000000000 : ℝ)*x 0 + (5062118949/10000000000 : ℝ)*x 1 + (-2260086239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2700585301/5000000000 : ℝ)^2173 ≤ (22335609937837/50000000000000 : ℝ)^1661 := by
    have hnat : (2700585301 : ℕ)^2173*50000000000000^1661 ≤ 22335609937837^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700585301 5000000000 22335609937837 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5062118949/10000000000 : ℝ)^2173 ≤ (41038678747649/100000000000000 : ℝ)^1661 := by
    have hnat : (5062118949 : ℕ)^2173*100000000000000^1661 ≤ 41038678747649^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5062118949 10000000000 41038678747649 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2260086239/10000000000 : ℝ)^2173 ≤ (178626267059/1250000000000 : ℝ)^1661 := by
    have hnat : (2260086239 : ℕ)^2173*1250000000000^1661 ≤ 178626267059^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2260086239 10000000000 178626267059 1250000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2700585301/5000000000 : ℝ), (5062118949/10000000000 : ℝ), (-2260086239/10000000000 : ℝ)] ![(22335609937837/50000000000000 : ℝ), (41038678747649/100000000000000 : ℝ), (178626267059/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2700585301/5000000000 : ℝ)|^2173 ≤ (22335609937837/50000000000000 : ℝ)^1661
        have hw : |(2700585301/5000000000 : ℝ)|=(2700585301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5062118949/10000000000 : ℝ)|^2173 ≤ (41038678747649/100000000000000 : ℝ)^1661
        have hw : |(5062118949/10000000000 : ℝ)|=(5062118949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2260086239/10000000000 : ℝ)|^2173 ≤ (178626267059/1250000000000 : ℝ)^1661
        have hw : |(-2260086239/10000000000 : ℝ)|=(2260086239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s1_3 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1071105211/2500000000 : ℝ)*x 0 + (931290683/2500000000 : ℝ)*x 1 + (1229834791/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1071105211/2500000000 : ℝ)^2173 ≤ (16496567757637/50000000000000 : ℝ)^1661 := by
    have hnat : (1071105211 : ℕ)^2173*50000000000000^1661 ≤ 16496567757637^1661*2500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1071105211 2500000000 16496567757637 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (931290683/2500000000 : ℝ)^2173 ≤ (27475880048863/100000000000000 : ℝ)^1661 := by
    have hnat : (931290683 : ℕ)^2173*100000000000000^1661 ≤ 27475880048863^1661*2500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931290683 2500000000 27475880048863 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1229834791/2500000000 : ℝ)^2173 ≤ (39530984420869/100000000000000 : ℝ)^1661 := by
    have hnat : (1229834791 : ℕ)^2173*100000000000000^1661 ≤ 39530984420869^1661*2500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1229834791 2500000000 39530984420869 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1071105211/2500000000 : ℝ), (931290683/2500000000 : ℝ), (1229834791/2500000000 : ℝ)] ![(16496567757637/50000000000000 : ℝ), (27475880048863/100000000000000 : ℝ), (39530984420869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1071105211/2500000000 : ℝ)|^2173 ≤ (16496567757637/50000000000000 : ℝ)^1661
        have hw : |(1071105211/2500000000 : ℝ)|=(1071105211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(931290683/2500000000 : ℝ)|^2173 ≤ (27475880048863/100000000000000 : ℝ)^1661
        have hw : |(931290683/2500000000 : ℝ)|=(931290683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1229834791/2500000000 : ℝ)|^2173 ≤ (39530984420869/100000000000000 : ℝ)^1661
        have hw : |(1229834791/2500000000 : ℝ)|=(1229834791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s1_4 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-981183087/5000000000 : ℝ)*x 0 + (126723021/250000000 : ℝ)*x 1 + (2808014999/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981183087/5000000000 : ℝ)^2173 ≤ (11879027373921/100000000000000 : ℝ)^1661 := by
    have hnat : (981183087 : ℕ)^2173*100000000000000^1661 ≤ 11879027373921^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981183087 5000000000 11879027373921 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (126723021/250000000 : ℝ)^2173 ≤ (5138854306881/12500000000000 : ℝ)^1661 := by
    have hnat : (126723021 : ℕ)^2173*12500000000000^1661 ≤ 5138854306881^1661*250000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126723021 250000000 5138854306881 12500000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2808014999/5000000000 : ℝ)^2173 ≤ (23505069080697/50000000000000 : ℝ)^1661 := by
    have hnat : (2808014999 : ℕ)^2173*50000000000000^1661 ≤ 23505069080697^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808014999 5000000000 23505069080697 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-981183087/5000000000 : ℝ), (126723021/250000000 : ℝ), (2808014999/5000000000 : ℝ)] ![(11879027373921/100000000000000 : ℝ), (5138854306881/12500000000000 : ℝ), (23505069080697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-981183087/5000000000 : ℝ)|^2173 ≤ (11879027373921/100000000000000 : ℝ)^1661
        have hw : |(-981183087/5000000000 : ℝ)|=(981183087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(126723021/250000000 : ℝ)|^2173 ≤ (5138854306881/12500000000000 : ℝ)^1661
        have hw : |(126723021/250000000 : ℝ)|=(126723021/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2808014999/5000000000 : ℝ)|^2173 ≤ (23505069080697/50000000000000 : ℝ)^1661
        have hw : |(2808014999/5000000000 : ℝ)|=(2808014999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s1_5 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2627560349/5000000000 : ℝ)*x 0 + (-5331799/31250000 : ℝ)*x 1 + (2808015027/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2627560349/5000000000 : ℝ)^2173 ≤ (10774394336357/25000000000000 : ℝ)^1661 := by
    have hnat : (2627560349 : ℕ)^2173*25000000000000^1661 ≤ 10774394336357^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627560349 5000000000 10774394336357 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5331799/31250000 : ℝ)^2173 ≤ (1978456771689/20000000000000 : ℝ)^1661 := by
    have hnat : (5331799 : ℕ)^2173*20000000000000^1661 ≤ 1978456771689^1661*31250000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5331799 31250000 1978456771689 20000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2808015027/5000000000 : ℝ)^2173 ≤ (47010138774647/100000000000000 : ℝ)^1661 := by
    have hnat : (2808015027 : ℕ)^2173*100000000000000^1661 ≤ 47010138774647^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2808015027 5000000000 47010138774647 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2627560349/5000000000 : ℝ), (-5331799/31250000 : ℝ), (2808015027/5000000000 : ℝ)] ![(10774394336357/25000000000000 : ℝ), (1978456771689/20000000000000 : ℝ), (47010138774647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2627560349/5000000000 : ℝ)|^2173 ≤ (10774394336357/25000000000000 : ℝ)^1661
        have hw : |(2627560349/5000000000 : ℝ)|=(2627560349/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-5331799/31250000 : ℝ)|^2173 ≤ (1978456771689/20000000000000 : ℝ)^1661
        have hw : |(-5331799/31250000 : ℝ)|=(5331799/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2808015027/5000000000 : ℝ)|^2173 ≤ (47010138774647/100000000000000 : ℝ)^1661
        have hw : |(2808015027/5000000000 : ℝ)|=(2808015027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s1_6 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (328445067/625000000 : ℝ)*x 0 + (5616030391/10000000000 : ℝ)*x 1 + (-341234933/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328445067/625000000 : ℝ)^2173 ≤ (43097581358083/100000000000000 : ℝ)^1661 := by
    have hnat : (328445067 : ℕ)^2173*100000000000000^1661 ≤ 43097581358083^1661*625000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328445067 625000000 43097581358083 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5616030391/10000000000 : ℝ)^2173 ≤ (47010142465121/100000000000000 : ℝ)^1661 := by
    have hnat : (5616030391 : ℕ)^2173*100000000000000^1661 ≤ 47010142465121^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5616030391 10000000000 47010142465121 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (341234933/2000000000 : ℝ)^2173 ≤ (9892276159541/100000000000000 : ℝ)^1661 := by
    have hnat : (341234933 : ℕ)^2173*100000000000000^1661 ≤ 9892276159541^1661*2000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      341234933 2000000000 9892276159541 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328445067/625000000 : ℝ), (5616030391/10000000000 : ℝ), (-341234933/2000000000 : ℝ)] ![(43097581358083/100000000000000 : ℝ), (47010142465121/100000000000000 : ℝ), (9892276159541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328445067/625000000 : ℝ)|^2173 ≤ (43097581358083/100000000000000 : ℝ)^1661
        have hw : |(328445067/625000000 : ℝ)|=(328445067/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5616030391/10000000000 : ℝ)|^2173 ≤ (47010142465121/100000000000000 : ℝ)^1661
        have hw : |(5616030391/10000000000 : ℝ)|=(5616030391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-341234933/2000000000 : ℝ)|^2173 ≤ (9892276159541/100000000000000 : ℝ)^1661
        have hw : |(-341234933/2000000000 : ℝ)|=(341234933/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s1_7 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (267837817/625000000 : ℝ)*x 0 + (2452428163/5000000000 : ℝ)*x 1 + (3739897917/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267837817/625000000 : ℝ)^2173 ≤ (4125381428377/12500000000000 : ℝ)^1661 := by
    have hnat : (267837817 : ℕ)^2173*12500000000000^1661 ≤ 4125381428377^1661*625000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267837817 625000000 4125381428377 12500000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2452428163/5000000000 : ℝ)^2173 ≤ (39378797479039/100000000000000 : ℝ)^1661 := by
    have hnat : (2452428163 : ℕ)^2173*100000000000000^1661 ≤ 39378797479039^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2452428163 5000000000 39378797479039 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3739897917/10000000000 : ℝ)^2173 ≤ (13809075542593/50000000000000 : ℝ)^1661 := by
    have hnat : (3739897917 : ℕ)^2173*50000000000000^1661 ≤ 13809075542593^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3739897917 10000000000 13809075542593 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(267837817/625000000 : ℝ), (2452428163/5000000000 : ℝ), (3739897917/10000000000 : ℝ)] ![(4125381428377/12500000000000 : ℝ), (39378797479039/100000000000000 : ℝ), (13809075542593/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(267837817/625000000 : ℝ)|^2173 ≤ (4125381428377/12500000000000 : ℝ)^1661
        have hw : |(267837817/625000000 : ℝ)|=(267837817/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2452428163/5000000000 : ℝ)|^2173 ≤ (39378797479039/100000000000000 : ℝ)^1661
        have hw : |(2452428163/5000000000 : ℝ)|=(2452428163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3739897917/10000000000 : ℝ)|^2173 ≤ (13809075542593/50000000000000 : ℝ)^1661
        have hw : |(3739897917/10000000000 : ℝ)|=(3739897917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1386_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13279/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1739/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (7287/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (19141/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13279/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1739/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13279/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1739/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13279/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1739/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13279/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1739/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13279/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1739/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13279/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1739/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1739/100000 : ℝ) ^ (4345/1024 : ℝ) ≤ (1707152938421/50000000000000000000 : ℝ) := by
    have hpowers : (1739/100000 : ℝ)^4345 ≤ (1707152938421/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1739 : ℕ)^4345*50000000000000000000^1024 ≤ 1707152938421^1024*100000^4345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1739 100000 1707152938421 50000000000000000000 4345 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1739/100000 : ℝ)) (X := (1707152938421/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (13279/50000 : ℝ) ^ (4345/1024 : ℝ) ≤ (360384805809840207/100000000000000000000 : ℝ) := by
    have hpowers : (13279/50000 : ℝ)^4345 ≤ (360384805809840207/100000000000000000000 : ℝ)^1024 := by
      have hnat : (13279 : ℕ)^4345*100000000000000000000^1024 ≤ 360384805809840207^1024*50000^4345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13279 50000 360384805809840207 100000000000000000000 4345 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13279/50000 : ℝ)) (X := (360384805809840207/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000001707152938421/25000000000000000000 : ℝ) ≤ (5000000080466033/5000000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (25000001707152938421/25000000000000000000 : ℝ)^1024 ≤ (5000000080466033/5000000000000000 : ℝ)^4345 := by
      have hnat : (25000001707152938421 : ℕ)^1024*5000000000000000^4345 ≤ 5000000080466033^4345*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000001707152938421 25000000000000000000 5000000080466033 5000000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000080466033/5000000000000000 : ℝ)) (X := (25000001707152938421/25000000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100360388220115717049/100000000000000000000 : ℝ) ≤ (10008481711092027/10000000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (100360388220115717049/100000000000000000000 : ℝ)^1024 ≤ (10008481711092027/10000000000000000 : ℝ)^4345 := by
      have hnat : (100360388220115717049 : ℕ)^1024*10000000000000000^4345 ≤ 10008481711092027^4345*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100360388220115717049 100000000000000000000 10008481711092027 10000000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10008481711092027/10000000000000000 : ℝ)) (X := (100360388220115717049/100000000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50360384805809840207/50000000000000000000 : ℝ) ≤ (2504240815312997/2500000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (50360384805809840207/50000000000000000000 : ℝ)^1024 ≤ (2504240815312997/2500000000000000 : ℝ)^4345 := by
      have hnat : (50360384805809840207 : ℕ)^1024*2500000000000000^4345 ≤ 2504240815312997^4345*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50360384805809840207 50000000000000000000 2504240815312997 2500000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2504240815312997/2500000000000000 : ℝ)) (X := (50360384805809840207/50000000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1707152938421/50000000000000000000 : ℝ) ≤ ((7755015786334893803/7755937500000000000 : ℝ)+2*(8481550159961/2481900000000000 : ℝ)*(1739/100000 : ℝ))^(4345/1024 : ℝ) := by
    rw [show (7755015786334893803/7755937500000000000 : ℝ)+2*(8481550159961/2481900000000000 : ℝ)*(1739/100000 : ℝ)=(5000000080466033/5000000000000000 : ℝ) by norm_num, show 1+2*(1707152938421/50000000000000000000 : ℝ)=(25000001707152938421/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(360384805809840207/100000000000000000000 : ℝ)+(1707152938421/50000000000000000000 : ℝ) ≤ ((7755015786334893803/7755937500000000000 : ℝ)+(8481550159961/2481900000000000 : ℝ)*((13279/50000 : ℝ)+(1739/100000 : ℝ)))^(4345/1024 : ℝ) := by
    rw [show (7755015786334893803/7755937500000000000 : ℝ)+(8481550159961/2481900000000000 : ℝ)*((13279/50000 : ℝ)+(1739/100000 : ℝ))=(10008481711092027/10000000000000000 : ℝ) by norm_num, show 1+(360384805809840207/100000000000000000000 : ℝ)+(1707152938421/50000000000000000000 : ℝ)=(100360388220115717049/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(360384805809840207/100000000000000000000 : ℝ) ≤ ((7755015786334893803/7755937500000000000 : ℝ)+2*(8481550159961/2481900000000000 : ℝ)*(13279/50000 : ℝ))^(4345/1024 : ℝ) := by
    rw [show (7755015786334893803/7755937500000000000 : ℝ)+2*(8481550159961/2481900000000000 : ℝ)*(13279/50000 : ℝ)=(2504240815312997/2500000000000000 : ℝ) by norm_num, show 1+2*(360384805809840207/100000000000000000000 : ℝ)=(50360384805809840207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7755015786334893803/7755937500000000000 : ℝ)*(X 1 0+X 2 0)+(8481550159961/2481900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (1739/100000 : ℝ)) (hi := (13279/50000 : ℝ)) (c := (7755015786334893803/7755937500000000000 : ℝ)) (alpha := (8481550159961/2481900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7755015786334893803/7755937500000000000 : ℝ)*(X 0 1+X 2 1)+(8481550159961/2481900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (1739/100000 : ℝ)) (hi := (13279/50000 : ℝ)) (c := (7755015786334893803/7755937500000000000 : ℝ)) (alpha := (8481550159961/2481900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7755015786334893803/7755937500000000000 : ℝ)*(X 0 2+X 1 2)+(8481550159961/2481900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (1739/100000 : ℝ)) (hi := (13279/50000 : ℝ)) (c := (7755015786334893803/7755937500000000000 : ℝ)) (alpha := (8481550159961/2481900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-980952329/5000000000 : ℝ)*X 0 0+(1124590317/2000000000 : ℝ)*X 0 1+(5062118767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5401169807/10000000000 : ℝ)*X 1 0+(-2260085663/10000000000 : ℝ)*X 1 1+(5062120209/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2700585301/5000000000 : ℝ)*X 2 0+(5062118949/10000000000 : ℝ)*X 2 1+(-2260086239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1071105211/2500000000 : ℝ)*X 0 0+(931290683/2500000000 : ℝ)*X 0 1+(1229834791/2500000000 : ℝ)*X 0 2+(1071105211/2500000000 : ℝ)*X 1 0+(931290683/2500000000 : ℝ)*X 1 1+(1229834791/2500000000 : ℝ)*X 1 2+(1071105211/2500000000 : ℝ)*X 2 0+(931290683/2500000000 : ℝ)*X 2 1+(1229834791/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-981183087/5000000000 : ℝ)*X 0 0+(126723021/250000000 : ℝ)*X 0 1+(2808014999/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2627560349/5000000000 : ℝ)*X 1 0+(-5331799/31250000 : ℝ)*X 1 1+(2808015027/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((328445067/625000000 : ℝ)*X 2 0+(5616030391/10000000000 : ℝ)*X 2 1+(-341234933/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((267837817/625000000 : ℝ)*X 0 0+(2452428163/5000000000 : ℝ)*X 0 1+(3739897917/10000000000 : ℝ)*X 0 2+(267837817/625000000 : ℝ)*X 1 0+(2452428163/5000000000 : ℝ)*X 1 1+(3739897917/10000000000 : ℝ)*X 1 2+(267837817/625000000 : ℝ)*X 2 0+(2452428163/5000000000 : ℝ)*X 2 1+(3739897917/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (280628334070792260465188189/129265625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12299373/6250000000000 : ℝ)*(base19) + (513430007/100000000000000 : ℝ)*(base23) + (43646003/100000000000000 : ℝ)*(upper2) + (2707731/100000000000000 : ℝ)*(upper3) + (655118720782819/50000000000000 : ℝ)*(major0) + (655118720782819/50000000000000 : ℝ)*(major1) + (1310237441565639/100000000000000 : ℝ)*(major2) + (445767138530661/25000000000000 : ℝ)*(sp0) + (445768676158689/25000000000000 : ℝ)*(sp1) + (1783073403550967/100000000000000 : ℝ)*(sp2) + (167479685416479/20000000000000 : ℝ)*(sp3) + (19835319/312500000000 : ℝ)*(sp4) + (984443749/100000000000000 : ℝ)*(sp6) + (1482259377/100000000000000 : ℝ)*(sp7) + (209349977335443/25000000000000 : ℝ)*(f.failure) + (445768725356181/25000000000000 : ℝ)*(f.sum) + (901037499027683/248190000000000000000000000000 : ℝ)*base66 + (4640132741630124311/775593750000000000000000000000000 : ℝ)*base68 + (1907516873314014883/775593750000000000000000000000000 : ℝ)*base70 + (7304998125762811811/775593750000000000000000000000000 : ℝ)*base72 + (50089532746463/248190000000000000000000000000 : ℝ)*base74 + (1775368164407735117/775593750000000000000000000000000 : ℝ)*base75 + (473138090200093953/64632812500000000000000000000000 : ℝ)*base78 + (127370756316277293/16158203125000000000000000000000 : ℝ)*base79 + (631109618526527/124095000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (22912723/2500000000000000000000 : ℝ)*base89 + (22912723/2500000000000000000000 : ℝ)*base91 + (2087277/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (528009820716949299706983297/129265625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157261651/100000000000000 : ℝ)*(base1) + (578898973/50000000000000 : ℝ)*(base19) + (1370922427/100000000000000 : ℝ)*(base23) + (54992633/50000000000000 : ℝ)*(upper3) + (34494241/20000000000000 : ℝ)*(upper5) + (335773747136397/25000000000000 : ℝ)*(major0) + (335773747136397/25000000000000 : ℝ)*(major1) + (335773747136397/25000000000000 : ℝ)*(major2) + (1153642189/20000000000000 : ℝ)*(sp1) + (1094529363/12500000000000 : ℝ)*(sp2) + (114236884341413/6250000000000 : ℝ)*(sp4) + (913891533096033/50000000000000 : ℝ)*(sp5) + (913889932521813/50000000000000 : ℝ)*(sp6) + (85839969147227/10000000000000 : ℝ)*(sp7) + (5364999054587/625000000000 : ℝ)*(f.failure) + (913894996100479/50000000000000 : ℝ)*(f.sum) + (39874489588041/10341250000000000000000000000 : ℝ)*base66 + (230977428996199111/32316406250000000000000000000000 : ℝ)*base67 + (74002762555117403/64632812500000000000000000000000 : ℝ)*base70 + (43088268569812069/129265625000000000000000000000000 : ℝ)*base71 + (14135271046531/41365000000000000000000000000 : ℝ)*base73 + (65990577861562069/129265625000000000000000000000000 : ℝ)*base75 + (16446108468011217/4039550781250000000000000000000 : ℝ)*base77 + (261691190967663847/64632812500000000000000000000000 : ℝ)*base79 + (44058771928213/5170625000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (673893/62500000000000000000 : ℝ)*base90 + (673893/62500000000000000000 : ℝ)*base92 + (673893/62500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1386_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13279/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1739/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (7287/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (19141/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1386_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1386_s2_0 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-499592771/2500000000 : ℝ)*x 0 + (5468294927/10000000000 : ℝ)*x 1 + (1298339711/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499592771/2500000000 : ℝ)^2173 ≤ (3041241675177/25000000000000 : ℝ)^1661 := by
    have hnat : (499592771 : ℕ)^2173*25000000000000^1661 ≤ 3041241675177^1661*2500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499592771 2500000000 3041241675177 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468294927/10000000000 : ℝ)^2173 ≤ (22699448425241/50000000000000 : ℝ)^1661 := by
    have hnat : (5468294927 : ℕ)^2173*50000000000000^1661 ≤ 22699448425241^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468294927 10000000000 22699448425241 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1298339711/2500000000 : ℝ)^2173 ≤ (42436136436693/100000000000000 : ℝ)^1661 := by
    have hnat : (1298339711 : ℕ)^2173*100000000000000^1661 ≤ 42436136436693^1661*2500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298339711 2500000000 42436136436693 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-499592771/2500000000 : ℝ), (5468294927/10000000000 : ℝ), (1298339711/2500000000 : ℝ)] ![(3041241675177/25000000000000 : ℝ), (22699448425241/50000000000000 : ℝ), (42436136436693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-499592771/2500000000 : ℝ)|^2173 ≤ (3041241675177/25000000000000 : ℝ)^1661
        have hw : |(-499592771/2500000000 : ℝ)|=(499592771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468294927/10000000000 : ℝ)|^2173 ≤ (22699448425241/50000000000000 : ℝ)^1661
        have hw : |(5468294927/10000000000 : ℝ)|=(5468294927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1298339711/2500000000 : ℝ)|^2173 ≤ (42436136436693/100000000000000 : ℝ)^1661
        have hw : |(1298339711/2500000000 : ℝ)|=(1298339711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s2_1 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5362936727/10000000000 : ℝ)*x 0 + (-2140107927/10000000000 : ℝ)*x 1 + (519335877/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362936727/10000000000 : ℝ)^2173 ≤ (22128989406409/50000000000000 : ℝ)^1661 := by
    have hnat : (5362936727 : ℕ)^2173*50000000000000^1661 ≤ 22128989406409^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362936727 10000000000 22128989406409 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2140107927/10000000000 : ℝ)^2173 ≤ (6652942762897/50000000000000 : ℝ)^1661 := by
    have hnat : (2140107927 : ℕ)^2173*50000000000000^1661 ≤ 6652942762897^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2140107927 10000000000 6652942762897 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (519335877/1000000000 : ℝ)^2173 ≤ (42436135645633/100000000000000 : ℝ)^1661 := by
    have hnat : (519335877 : ℕ)^2173*100000000000000^1661 ≤ 42436135645633^1661*1000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519335877 1000000000 42436135645633 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362936727/10000000000 : ℝ), (-2140107927/10000000000 : ℝ), (519335877/1000000000 : ℝ)] ![(22128989406409/50000000000000 : ℝ), (6652942762897/50000000000000 : ℝ), (42436135645633/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362936727/10000000000 : ℝ)|^2173 ≤ (22128989406409/50000000000000 : ℝ)^1661
        have hw : |(5362936727/10000000000 : ℝ)|=(5362936727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2140107927/10000000000 : ℝ)|^2173 ≤ (6652942762897/50000000000000 : ℝ)^1661
        have hw : |(-2140107927/10000000000 : ℝ)|=(2140107927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(519335877/1000000000 : ℝ)|^2173 ≤ (42436135645633/100000000000000 : ℝ)^1661
        have hw : |(519335877/1000000000 : ℝ)|=(519335877/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s2_2 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (214517463/400000000 : ℝ)*x 0 + (207734357/400000000 : ℝ)*x 1 + (-85604317/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214517463/400000000 : ℝ)^2173 ≤ (8851595434353/20000000000000 : ℝ)^1661 := by
    have hnat : (214517463 : ℕ)^2173*20000000000000^1661 ≤ 8851595434353^1661*400000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214517463 400000000 8851595434353 20000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207734357/400000000 : ℝ)^2173 ≤ (42436137302583/100000000000000 : ℝ)^1661 := by
    have hnat : (207734357 : ℕ)^2173*100000000000000^1661 ≤ 42436137302583^1661*400000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207734357 400000000 42436137302583 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (85604317/400000000 : ℝ)^2173 ≤ (6652942754763/50000000000000 : ℝ)^1661 := by
    have hnat : (85604317 : ℕ)^2173*50000000000000^1661 ≤ 6652942754763^1661*400000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85604317 400000000 6652942754763 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214517463/400000000 : ℝ), (207734357/400000000 : ℝ), (-85604317/400000000 : ℝ)] ![(8851595434353/20000000000000 : ℝ), (42436137302583/100000000000000 : ℝ), (6652942754763/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214517463/400000000 : ℝ)|^2173 ≤ (8851595434353/20000000000000 : ℝ)^1661
        have hw : |(214517463/400000000 : ℝ)|=(214517463/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207734357/400000000 : ℝ)|^2173 ≤ (42436137302583/100000000000000 : ℝ)^1661
        have hw : |(207734357/400000000 : ℝ)|=(207734357/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-85604317/400000000 : ℝ)|^2173 ≤ (6652942754763/50000000000000 : ℝ)^1661
        have hw : |(-85604317/400000000 : ℝ)|=(85604317/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s2_3 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2155024407/5000000000 : ℝ)*x 0 + (2516517/6250000 : ℝ)*x 1 + (461184869/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155024407/5000000000 : ℝ)^2173 ≤ (1039111282697/3125000000000 : ℝ)^1661 := by
    have hnat : (2155024407 : ℕ)^2173*3125000000000^1661 ≤ 1039111282697^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155024407 5000000000 1039111282697 3125000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2516517/6250000 : ℝ)^2173 ≤ (950576755077/3125000000000 : ℝ)^1661 := by
    have hnat : (2516517 : ℕ)^2173*3125000000000^1661 ≤ 950576755077^1661*6250000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2516517 6250000 950576755077 3125000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (461184869/1000000000 : ℝ)^2173 ≤ (18164991388493/50000000000000 : ℝ)^1661 := by
    have hnat : (461184869 : ℕ)^2173*50000000000000^1661 ≤ 18164991388493^1661*1000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      461184869 1000000000 18164991388493 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155024407/5000000000 : ℝ), (2516517/6250000 : ℝ), (461184869/1000000000 : ℝ)] ![(1039111282697/3125000000000 : ℝ), (950576755077/3125000000000 : ℝ), (18164991388493/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155024407/5000000000 : ℝ)|^2173 ≤ (1039111282697/3125000000000 : ℝ)^1661
        have hw : |(2155024407/5000000000 : ℝ)|=(2155024407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2516517/6250000 : ℝ)|^2173 ≤ (950576755077/3125000000000 : ℝ)^1661
        have hw : |(2516517/6250000 : ℝ)|=(2516517/6250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(461184869/1000000000 : ℝ)|^2173 ≤ (18164991388493/50000000000000 : ℝ)^1661
        have hw : |(461184869/1000000000 : ℝ)|=(461184869/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s2_4 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-999212613/5000000000 : ℝ)*x 0 + (5195003177/10000000000 : ℝ)*x 1 + (5466636679/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (999212613/5000000000 : ℝ)^2173 ≤ (190084341923/1562500000000 : ℝ)^1661 := by
    have hnat : (999212613 : ℕ)^2173*1562500000000^1661 ≤ 190084341923^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      999212613 5000000000 190084341923 1562500000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5195003177/10000000000 : ℝ)^2173 ≤ (21226857604943/50000000000000 : ℝ)^1661 := by
    have hnat : (5195003177 : ℕ)^2173*50000000000000^1661 ≤ 21226857604943^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195003177 10000000000 21226857604943 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5466636679/10000000000 : ℝ)^2173 ≤ (45380886894703/100000000000000 : ℝ)^1661 := by
    have hnat : (5466636679 : ℕ)^2173*100000000000000^1661 ≤ 45380886894703^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5466636679 10000000000 45380886894703 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-999212613/5000000000 : ℝ), (5195003177/10000000000 : ℝ), (5466636679/10000000000 : ℝ)] ![(190084341923/1562500000000 : ℝ), (21226857604943/50000000000000 : ℝ), (45380886894703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-999212613/5000000000 : ℝ)|^2173 ≤ (190084341923/1562500000000 : ℝ)^1661
        have hw : |(-999212613/5000000000 : ℝ)|=(999212613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5195003177/10000000000 : ℝ)|^2173 ≤ (21226857604943/50000000000000 : ℝ)^1661
        have hw : |(5195003177/10000000000 : ℝ)|=(5195003177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5466636679/10000000000 : ℝ)|^2173 ≤ (45380886894703/100000000000000 : ℝ)^1661
        have hw : |(5466636679/10000000000 : ℝ)|=(5466636679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s2_5 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2645871893/5000000000 : ℝ)*x 0 + (-1866830663/10000000000 : ℝ)*x 1 + (1366659091/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645871893/5000000000 : ℝ)^2173 ≤ (173963714957/400000000000 : ℝ)^1661 := by
    have hnat : (2645871893 : ℕ)^2173*400000000000^1661 ≤ 173963714957^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645871893 5000000000 173963714957 400000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1866830663/10000000000 : ℝ)^2173 ≤ (5564093886199/50000000000000 : ℝ)^1661 := by
    have hnat : (1866830663 : ℕ)^2173*50000000000000^1661 ≤ 5564093886199^1661*10000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1866830663 10000000000 5564093886199 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1366659091/2500000000 : ℝ)^2173 ≤ (453808834737/1000000000000 : ℝ)^1661 := by
    have hnat : (1366659091 : ℕ)^2173*1000000000000^1661 ≤ 453808834737^1661*2500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1366659091 2500000000 453808834737 1000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645871893/5000000000 : ℝ), (-1866830663/10000000000 : ℝ), (1366659091/2500000000 : ℝ)] ![(173963714957/400000000000 : ℝ), (5564093886199/50000000000000 : ℝ), (453808834737/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645871893/5000000000 : ℝ)|^2173 ≤ (173963714957/400000000000 : ℝ)^1661
        have hw : |(2645871893/5000000000 : ℝ)|=(2645871893/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1866830663/10000000000 : ℝ)|^2173 ≤ (5564093886199/50000000000000 : ℝ)^1661
        have hw : |(-1866830663/10000000000 : ℝ)|=(1866830663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1366659091/2500000000 : ℝ)|^2173 ≤ (453808834737/1000000000000 : ℝ)^1661
        have hw : |(1366659091/2500000000 : ℝ)|=(1366659091/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s2_6 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1058349049/2000000000 : ℝ)*x 0 + (1093327281/2000000000 : ℝ)*x 1 + (-373365719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058349049/2000000000 : ℝ)^2173 ≤ (10872736106611/25000000000000 : ℝ)^1661 := by
    have hnat : (1058349049 : ℕ)^2173*25000000000000^1661 ≤ 10872736106611^1661*2000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058349049 2000000000 10872736106611 25000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1093327281/2000000000 : ℝ)^2173 ≤ (22690441959487/50000000000000 : ℝ)^1661 := by
    have hnat : (1093327281 : ℕ)^2173*50000000000000^1661 ≤ 22690441959487^1661*2000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1093327281 2000000000 22690441959487 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (373365719/2000000000 : ℝ)^2173 ≤ (11128171645157/100000000000000 : ℝ)^1661 := by
    have hnat : (373365719 : ℕ)^2173*100000000000000^1661 ≤ 11128171645157^1661*2000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      373365719 2000000000 11128171645157 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058349049/2000000000 : ℝ), (1093327281/2000000000 : ℝ), (-373365719/2000000000 : ℝ)] ![(10872736106611/25000000000000 : ℝ), (22690441959487/50000000000000 : ℝ), (11128171645157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058349049/2000000000 : ℝ)|^2173 ≤ (10872736106611/25000000000000 : ℝ)^1661
        have hw : |(1058349049/2000000000 : ℝ)|=(1058349049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1093327281/2000000000 : ℝ)|^2173 ≤ (22690441959487/50000000000000 : ℝ)^1661
        have hw : |(1093327281/2000000000 : ℝ)|=(1093327281/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-373365719/2000000000 : ℝ)|^2173 ≤ (11128171645157/100000000000000 : ℝ)^1661
        have hw : |(-373365719/2000000000 : ℝ)|=(373365719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1386_s2_7 (p : ℝ) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2155082797/5000000000 : ℝ)*x 0 + (288021747/625000000 : ℝ)*x 1 + (1007489343/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155082797/5000000000 : ℝ)^2173 ≤ (33252739710871/100000000000000 : ℝ)^1661 := by
    have hnat : (2155082797 : ℕ)^2173*100000000000000^1661 ≤ 33252739710871^1661*5000000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155082797 5000000000 33252739710871 100000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (288021747/625000000 : ℝ)^2173 ≤ (18146954607659/50000000000000 : ℝ)^1661 := by
    have hnat : (288021747 : ℕ)^2173*50000000000000^1661 ≤ 18146954607659^1661*625000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      288021747 625000000 18146954607659 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1007489343/2500000000 : ℝ)^2173 ≤ (15226675530773/50000000000000 : ℝ)^1661 := by
    have hnat : (1007489343 : ℕ)^2173*50000000000000^1661 ≤ 15226675530773^1661*2500000000^2173 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1007489343 2500000000 15226675530773 50000000000000 2173 1661 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2173/512 : ℝ)) 2173 1661 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155082797/5000000000 : ℝ), (288021747/625000000 : ℝ), (1007489343/2500000000 : ℝ)] ![(33252739710871/100000000000000 : ℝ), (18146954607659/50000000000000 : ℝ), (15226675530773/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155082797/5000000000 : ℝ)|^2173 ≤ (33252739710871/100000000000000 : ℝ)^1661
        have hw : |(2155082797/5000000000 : ℝ)|=(2155082797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(288021747/625000000 : ℝ)|^2173 ≤ (18146954607659/50000000000000 : ℝ)^1661
        have hw : |(288021747/625000000 : ℝ)|=(288021747/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1007489343/2500000000 : ℝ)|^2173 ≤ (15226675530773/50000000000000 : ℝ)^1661
        have hw : |(1007489343/2500000000 : ℝ)|=(1007489343/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1386_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7287/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5063/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (797/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (19141/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (7287/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (19141/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (7287/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (19141/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (7287/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (19141/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (7287/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (19141/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (7287/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (19141/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (7287/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (7287/100000 : ℝ) ^ (4345/1024 : ℝ) ≤ (186430871179459/12500000000000000000 : ℝ) := by
    have hpowers : (7287/100000 : ℝ)^4345 ≤ (186430871179459/12500000000000000000 : ℝ)^1024 := by
      have hnat : (7287 : ℕ)^4345*12500000000000000000^1024 ≤ 186430871179459^1024*100000^4345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7287 100000 186430871179459 12500000000000000000 4345 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7287/100000 : ℝ)) (X := (186430871179459/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (19141/100000 : ℝ) ^ (4345/1024 : ℝ) ≤ (11224528495640637/12500000000000000000 : ℝ) := by
    have hpowers : (19141/100000 : ℝ)^4345 ≤ (11224528495640637/12500000000000000000 : ℝ)^1024 := by
      have hnat : (19141 : ℕ)^4345*12500000000000000000^1024 ≤ 11224528495640637^1024*100000^4345 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        19141 100000 11224528495640637 12500000000000000000 4345 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (19141/100000 : ℝ)) (X := (11224528495640637/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250186430871179459/6250000000000000000 : ℝ) ≤ (10000070298010917/10000000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (6250186430871179459/6250000000000000000 : ℝ)^1024 ≤ (10000070298010917/10000000000000000 : ℝ)^4345 := by
      have hnat : (6250186430871179459 : ℕ)^1024*10000000000000000^4345 ≤ 10000070298010917^4345*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250186430871179459 6250000000000000000 10000070298010917 10000000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000070298010917/10000000000000000 : ℝ)) (X := (6250186430871179459/6250000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (48872699060026641/48828125000000000 : ℝ) ≤ (62513441597373/62500000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (48872699060026641/48828125000000000 : ℝ)^1024 ≤ (62513441597373/62500000000000 : ℝ)^4345 := by
      have hnat : (48872699060026641 : ℕ)^1024*62500000000000^4345 ≤ 62513441597373^4345*48828125000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        48872699060026641 48828125000000000 62513441597373 62500000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62513441597373/62500000000000 : ℝ)) (X := (48872699060026641/48828125000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6261224528495640637/6250000000000000000 : ℝ) ≤ (10004231013148443/10000000000000000 : ℝ) ^ (4345/1024 : ℝ) := by
    have hpowers : (6261224528495640637/6250000000000000000 : ℝ)^1024 ≤ (10004231013148443/10000000000000000 : ℝ)^4345 := by
      have hnat : (6261224528495640637 : ℕ)^1024*10000000000000000^4345 ≤ 10004231013148443^4345*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6261224528495640637 6250000000000000000 10004231013148443 10000000000000000 1024 4345 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004231013148443/10000000000000000 : ℝ)) (X := (6261224528495640637/6250000000000000000 : ℝ)) (by norm_num) 4345 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(186430871179459/12500000000000000000 : ℝ) ≤ ((29627628545353564539/29635000000000000000 : ℝ)+2*(2080357568763/1185400000000000 : ℝ)*(7287/100000 : ℝ))^(4345/1024 : ℝ) := by
    rw [show (29627628545353564539/29635000000000000000 : ℝ)+2*(2080357568763/1185400000000000 : ℝ)*(7287/100000 : ℝ)=(10000070298010917/10000000000000000 : ℝ) by norm_num, show 1+2*(186430871179459/12500000000000000000 : ℝ)=(6250186430871179459/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11224528495640637/12500000000000000000 : ℝ)+(186430871179459/12500000000000000000 : ℝ) ≤ ((29627628545353564539/29635000000000000000 : ℝ)+(2080357568763/1185400000000000 : ℝ)*((19141/100000 : ℝ)+(7287/100000 : ℝ)))^(4345/1024 : ℝ) := by
    rw [show (29627628545353564539/29635000000000000000 : ℝ)+(2080357568763/1185400000000000 : ℝ)*((19141/100000 : ℝ)+(7287/100000 : ℝ))=(62513441597373/62500000000000 : ℝ) by norm_num, show 1+(11224528495640637/12500000000000000000 : ℝ)+(186430871179459/12500000000000000000 : ℝ)=(48872699060026641/48828125000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11224528495640637/12500000000000000000 : ℝ) ≤ ((29627628545353564539/29635000000000000000 : ℝ)+2*(2080357568763/1185400000000000 : ℝ)*(19141/100000 : ℝ))^(4345/1024 : ℝ) := by
    rw [show (29627628545353564539/29635000000000000000 : ℝ)+2*(2080357568763/1185400000000000 : ℝ)*(19141/100000 : ℝ)=(10004231013148443/10000000000000000 : ℝ) by norm_num, show 1+2*(11224528495640637/12500000000000000000 : ℝ)=(6261224528495640637/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (29627628545353564539/29635000000000000000 : ℝ)*(X 1 0+X 2 0)+(2080357568763/1185400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (7287/100000 : ℝ)) (hi := (19141/100000 : ℝ)) (c := (29627628545353564539/29635000000000000000 : ℝ)) (alpha := (2080357568763/1185400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (29627628545353564539/29635000000000000000 : ℝ)*(X 0 1+X 2 1)+(2080357568763/1185400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (7287/100000 : ℝ)) (hi := (19141/100000 : ℝ)) (c := (29627628545353564539/29635000000000000000 : ℝ)) (alpha := (2080357568763/1185400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (29627628545353564539/29635000000000000000 : ℝ)*(X 0 2+X 1 2)+(2080357568763/1185400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4345/1024 : ℝ)) (lo := (7287/100000 : ℝ)) (hi := (19141/100000 : ℝ)) (c := (29627628545353564539/29635000000000000000 : ℝ)) (alpha := (2080357568763/1185400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-499592771/2500000000 : ℝ)*X 0 0+(5468294927/10000000000 : ℝ)*X 0 1+(1298339711/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5362936727/10000000000 : ℝ)*X 1 0+(-2140107927/10000000000 : ℝ)*X 1 1+(519335877/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214517463/400000000 : ℝ)*X 2 0+(207734357/400000000 : ℝ)*X 2 1+(-85604317/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2155024407/5000000000 : ℝ)*X 0 0+(2516517/6250000 : ℝ)*X 0 1+(461184869/1000000000 : ℝ)*X 0 2+(2155024407/5000000000 : ℝ)*X 1 0+(2516517/6250000 : ℝ)*X 1 1+(461184869/1000000000 : ℝ)*X 1 2+(2155024407/5000000000 : ℝ)*X 2 0+(2516517/6250000 : ℝ)*X 2 1+(461184869/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-999212613/5000000000 : ℝ)*X 0 0+(5195003177/10000000000 : ℝ)*X 0 1+(5466636679/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2645871893/5000000000 : ℝ)*X 1 0+(-1866830663/10000000000 : ℝ)*X 1 1+(1366659091/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1058349049/2000000000 : ℝ)*X 2 0+(1093327281/2000000000 : ℝ)*X 2 1+(-373365719/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155082797/5000000000 : ℝ)*X 0 0+(288021747/625000000 : ℝ)*X 0 1+(1007489343/2500000000 : ℝ)*X 0 2+(2155082797/5000000000 : ℝ)*X 1 0+(288021747/625000000 : ℝ)*X 1 1+(1007489343/2500000000 : ℝ)*X 1 2+(2155082797/5000000000 : ℝ)*X 2 0+(288021747/625000000 : ℝ)*X 2 1+(1007489343/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1386_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3124546773320724779068996119/740875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (188058383/25000000000000 : ℝ)*(base19) + (17301907/3125000000000 : ℝ)*(base23) + (12801843/25000000000000 : ℝ)*(lower2) + (29167499/20000000000000 : ℝ)*(upper3) + (5047713/10000000000000 : ℝ)*(upper5) + (2672702140963271/100000000000000 : ℝ)*(major0) + (2672702140963271/100000000000000 : ℝ)*(major1) + (334087767620409/12500000000000 : ℝ)*(major2) + (3637217890139091/100000000000000 : ℝ)*(sp0) + (3637224047310139/100000000000000 : ℝ)*(sp1) + (454653030735331/12500000000000 : ℝ)*(sp2) + (341634934983683/20000000000000 : ℝ)*(sp3) + (345470229/5000000000000 : ℝ)*(sp4) + (4666885321/100000000000000 : ℝ)*(sp7) + (341635868360747/20000000000000 : ℝ)*(f.failure) + (454653099942959/12500000000000 : ℝ)*(f.sum) + (308023370785909/118540000000000000000000000000 : ℝ)*base65 + (15373495148031052931/2963500000000000000000000000000000 : ℝ)*base68 + (111532469516751981/92609375000000000000000000000000 : ℝ)*base70 + (30003962522659052931/2963500000000000000000000000000000 : ℝ)*base72 + (800770507344751/118540000000000000000000000000 : ℝ)*base74 + (71896435491158231/92609375000000000000000000000000 : ℝ)*base76 + (18541219745412627931/2963500000000000000000000000000000 : ℝ)*base78 + (31948176450770627931/2963500000000000000000000000000000 : ℝ)*base80 + (71152166341967/59270000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (6714133/2000000000000000000000 : ℝ)*base90 + (6714133/2000000000000000000000 : ℝ)*base92 + (26714133/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (483985792365749263245142587/185218750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (72060407/12500000000000 : ℝ)*(base19) + (2234340887/100000000000000 : ℝ)*(base23) + (851963/800000000000 : ℝ)*(lower2) + (72687837/50000000000000 : ℝ)*(upper3) + (96419879/50000000000000 : ℝ)*(lower4) + (676296839826589/25000000000000 : ℝ)*(major0) + (676296839826589/25000000000000 : ℝ)*(major1) + (676296839826589/25000000000000 : ℝ)*(major2) + (8913676843/25000000000000 : ℝ)*(sp2) + (819415019/100000000000000 : ℝ)*(sp3) + (1840716656632567/50000000000000 : ℝ)*(sp4) + (1840716368390939/50000000000000 : ℝ)*(sp5) + (920348856054219/25000000000000 : ℝ)*(sp6) + (108058781176931/6250000000000 : ℝ)*(sp7) + (864470659122957/50000000000000 : ℝ)*(f.failure) + (1840716656632567/50000000000000 : ℝ)*(f.sum) + (32274492754499/7408750000000000000000000000 : ℝ)*base66 + (5132391709918652471/740875000000000000000000000000000 : ℝ)*base67 + (3010134150262097529/740875000000000000000000000000000 : ℝ)*base70 + (1855081295421652471/740875000000000000000000000000000 : ℝ)*base71 + (24915064818429/7408750000000000000000000000 : ℝ)*base74 + (75786844892652471/740875000000000000000000000000000 : ℝ)*base75 + (1041026062056152471/740875000000000000000000000000000 : ℝ)*base77 + (2003576446771902471/740875000000000000000000000000000 : ℝ)*base79 + (9457681630989/7408750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (38790323/5000000000000000000000 : ℝ)*base90 + (38790323/5000000000000000000000 : ℝ)*base92 + (38790323/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1386_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (19141/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (7287/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5063/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (797/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1386_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1386_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5063/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (797/5000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1386_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1386_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1386_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4345/1024 : ℝ) ≤ p) (hpb : p ≤ (2173/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (156464961/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5063/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (797/5000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1386_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
