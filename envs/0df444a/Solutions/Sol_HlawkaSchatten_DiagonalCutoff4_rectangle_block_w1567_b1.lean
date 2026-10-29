-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1567_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:26:32.288504+00:00
-- url     : https://prove2.me/submissions/b3cebe83-5f92-4ada-a969-3611aca4ba5e

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
theorem support_rectangle_w1567_s3_0 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-223682679/1250000000 : ℝ)*x 0 + (5427903037/10000000000 : ℝ)*x 1 + (5218399587/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (223682679/1250000000 : ℝ)^4631 ≤ (1372416353673/12500000000000 : ℝ)^3607 := by
    have hnat : (223682679 : ℕ)^4631*12500000000000^3607 ≤ 1372416353673^3607*1250000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      223682679 1250000000 1372416353673 12500000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5427903037/10000000000 : ℝ)^4631 ≤ (22817399244471/50000000000000 : ℝ)^3607 := by
    have hnat : (5427903037 : ℕ)^4631*50000000000000^3607 ≤ 22817399244471^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5427903037 10000000000 22817399244471 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218399587/10000000000 : ℝ)^4631 ≤ (21692935334289/50000000000000 : ℝ)^3607 := by
    have hnat : (5218399587 : ℕ)^4631*50000000000000^3607 ≤ 21692935334289^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218399587 10000000000 21692935334289 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-223682679/1250000000 : ℝ), (5427903037/10000000000 : ℝ), (5218399587/10000000000 : ℝ)] ![(1372416353673/12500000000000 : ℝ), (22817399244471/50000000000000 : ℝ), (21692935334289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-223682679/1250000000 : ℝ)|^4631 ≤ (1372416353673/12500000000000 : ℝ)^3607
        have hw : |(-223682679/1250000000 : ℝ)|=(223682679/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5427903037/10000000000 : ℝ)|^4631 ≤ (22817399244471/50000000000000 : ℝ)^3607
        have hw : |(5427903037/10000000000 : ℝ)|=(5427903037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218399587/10000000000 : ℝ)|^4631 ≤ (21692935334289/50000000000000 : ℝ)^3607
        have hw : |(5218399587/10000000000 : ℝ)|=(5218399587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s3_1 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348833653/10000000000 : ℝ)*x 0 + (-948342347/5000000000 : ℝ)*x 1 + (5218399709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348833653/10000000000 : ℝ)^4631 ≤ (5597884293943/12500000000000 : ℝ)^3607 := by
    have hnat : (5348833653 : ℕ)^4631*12500000000000^3607 ≤ 5597884293943^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348833653 10000000000 5597884293943 12500000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (948342347/5000000000 : ℝ)^4631 ≤ (739440853893/6250000000000 : ℝ)^3607 := by
    have hnat : (948342347 : ℕ)^4631*6250000000000^3607 ≤ 739440853893^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      948342347 5000000000 739440853893 6250000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218399709/10000000000 : ℝ)^4631 ≤ (43385871970843/100000000000000 : ℝ)^3607 := by
    have hnat : (5218399709 : ℕ)^4631*100000000000000^3607 ≤ 43385871970843^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218399709 10000000000 43385871970843 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348833653/10000000000 : ℝ), (-948342347/5000000000 : ℝ), (5218399709/10000000000 : ℝ)] ![(5597884293943/12500000000000 : ℝ), (739440853893/6250000000000 : ℝ), (43385871970843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348833653/10000000000 : ℝ)|^4631 ≤ (5597884293943/12500000000000 : ℝ)^3607
        have hw : |(5348833653/10000000000 : ℝ)|=(5348833653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-948342347/5000000000 : ℝ)|^4631 ≤ (739440853893/6250000000000 : ℝ)^3607
        have hw : |(-948342347/5000000000 : ℝ)|=(948342347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218399709/10000000000 : ℝ)|^4631 ≤ (43385871970843/100000000000000 : ℝ)^3607
        have hw : |(5218399709/10000000000 : ℝ)|=(5218399709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s3_2 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (167151041/312500000 : ℝ)*x 0 + (1304599973/2500000000 : ℝ)*x 1 + (-474171227/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167151041/312500000 : ℝ)^4631 ≤ (8956614137201/20000000000000 : ℝ)^3607 := by
    have hnat : (167151041 : ℕ)^4631*20000000000000^3607 ≤ 8956614137201^3607*312500000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167151041 312500000 8956614137201 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304599973/2500000000 : ℝ)^4631 ≤ (43385873924241/100000000000000 : ℝ)^3607 := by
    have hnat : (1304599973 : ℕ)^4631*100000000000000^3607 ≤ 43385873924241^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304599973 2500000000 43385873924241 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (474171227/2500000000 : ℝ)^4631 ≤ (1183105537613/10000000000000 : ℝ)^3607 := by
    have hnat : (474171227 : ℕ)^4631*10000000000000^3607 ≤ 1183105537613^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474171227 2500000000 1183105537613 10000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167151041/312500000 : ℝ), (1304599973/2500000000 : ℝ), (-474171227/2500000000 : ℝ)] ![(8956614137201/20000000000000 : ℝ), (43385873924241/100000000000000 : ℝ), (1183105537613/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167151041/312500000 : ℝ)|^4631 ≤ (8956614137201/20000000000000 : ℝ)^3607
        have hw : |(167151041/312500000 : ℝ)|=(167151041/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304599973/2500000000 : ℝ)|^4631 ≤ (43385873924241/100000000000000 : ℝ)^3607
        have hw : |(1304599973/2500000000 : ℝ)|=(1304599973/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-474171227/2500000000 : ℝ)|^4631 ≤ (1183105537613/10000000000000 : ℝ)^3607
        have hw : |(-474171227/2500000000 : ℝ)|=(474171227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s3_3 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061166409/2500000000 : ℝ)*x 0 + (2001860209/5000000000 : ℝ)*x 1 + (449725583/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061166409/2500000000 : ℝ)^4631 ≤ (33280593883353/100000000000000 : ℝ)^3607 := by
    have hnat : (1061166409 : ℕ)^4631*100000000000000^3607 ≤ 33280593883353^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061166409 2500000000 33280593883353 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2001860209/5000000000 : ℝ)^4631 ≤ (30874946109833/100000000000000 : ℝ)^3607 := by
    have hnat : (2001860209 : ℕ)^4631*100000000000000^3607 ≤ 30874946109833^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001860209 5000000000 30874946109833 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449725583/1000000000 : ℝ)^4631 ≤ (8961114997193/25000000000000 : ℝ)^3607 := by
    have hnat : (449725583 : ℕ)^4631*25000000000000^3607 ≤ 8961114997193^3607*1000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449725583 1000000000 8961114997193 25000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061166409/2500000000 : ℝ), (2001860209/5000000000 : ℝ), (449725583/1000000000 : ℝ)] ![(33280593883353/100000000000000 : ℝ), (30874946109833/100000000000000 : ℝ), (8961114997193/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061166409/2500000000 : ℝ)|^4631 ≤ (33280593883353/100000000000000 : ℝ)^3607
        have hw : |(1061166409/2500000000 : ℝ)|=(1061166409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2001860209/5000000000 : ℝ)|^4631 ≤ (30874946109833/100000000000000 : ℝ)^3607
        have hw : |(2001860209/5000000000 : ℝ)|=(2001860209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449725583/1000000000 : ℝ)|^4631 ≤ (8961114997193/25000000000000 : ℝ)^3607
        have hw : |(449725583/1000000000 : ℝ)|=(449725583/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s3_4 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-44737241/250000000 : ℝ)*x 0 + (1043901493/2000000000 : ℝ)*x 1 + (2713393409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44737241/250000000 : ℝ)^4631 ≤ (5489776517603/50000000000000 : ℝ)^3607 := by
    have hnat : (44737241 : ℕ)^4631*50000000000000^3607 ≤ 5489776517603^3607*250000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44737241 250000000 5489776517603 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043901493/2000000000 : ℝ)^4631 ≤ (21698848426537/50000000000000 : ℝ)^3607 := by
    have hnat : (1043901493 : ℕ)^4631*50000000000000^3607 ≤ 21698848426537^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043901493 2000000000 21698848426537 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713393409/5000000000 : ℝ)^4631 ≤ (356427735059/781250000000 : ℝ)^3607 := by
    have hnat : (2713393409 : ℕ)^4631*781250000000^3607 ≤ 356427735059^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713393409 5000000000 356427735059 781250000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44737241/250000000 : ℝ), (1043901493/2000000000 : ℝ), (2713393409/5000000000 : ℝ)] ![(5489776517603/50000000000000 : ℝ), (21698848426537/50000000000000 : ℝ), (356427735059/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44737241/250000000 : ℝ)|^4631 ≤ (5489776517603/50000000000000 : ℝ)^3607
        have hw : |(-44737241/250000000 : ℝ)|=(44737241/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043901493/2000000000 : ℝ)|^4631 ≤ (21698848426537/50000000000000 : ℝ)^3607
        have hw : |(1043901493/2000000000 : ℝ)|=(1043901493/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713393409/5000000000 : ℝ)|^4631 ≤ (356427735059/781250000000 : ℝ)^3607
        have hw : |(2713393409/5000000000 : ℝ)|=(2713393409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s3_5 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646712401/5000000000 : ℝ)*x 0 + (-1688297733/10000000000 : ℝ)*x 1 + (2713393401/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646712401/5000000000 : ℝ)^4631 ≤ (44188341486259/100000000000000 : ℝ)^3607 := by
    have hnat : (2646712401 : ℕ)^4631*100000000000000^3607 ≤ 44188341486259^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646712401 5000000000 44188341486259 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1688297733/10000000000 : ℝ)^4631 ≤ (2037781718797/20000000000000 : ℝ)^3607 := by
    have hnat : (1688297733 : ℕ)^4631*20000000000000^3607 ≤ 2037781718797^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688297733 10000000000 2037781718797 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713393401/5000000000 : ℝ)^4631 ≤ (22811374957427/50000000000000 : ℝ)^3607 := by
    have hnat : (2713393401 : ℕ)^4631*50000000000000^3607 ≤ 22811374957427^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713393401 5000000000 22811374957427 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646712401/5000000000 : ℝ), (-1688297733/10000000000 : ℝ), (2713393401/5000000000 : ℝ)] ![(44188341486259/100000000000000 : ℝ), (2037781718797/20000000000000 : ℝ), (22811374957427/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646712401/5000000000 : ℝ)|^4631 ≤ (44188341486259/100000000000000 : ℝ)^3607
        have hw : |(2646712401/5000000000 : ℝ)|=(2646712401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1688297733/10000000000 : ℝ)|^4631 ≤ (2037781718797/20000000000000 : ℝ)^3607
        have hw : |(-1688297733/10000000000 : ℝ)|=(1688297733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713393401/5000000000 : ℝ)|^4631 ≤ (22811374957427/50000000000000 : ℝ)^3607
        have hw : |(2713393401/5000000000 : ℝ)|=(2713393401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s3_6 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646712397/5000000000 : ℝ)*x 0 + (2713393413/5000000000 : ℝ)*x 1 + (-1688297709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646712397/5000000000 : ℝ)^4631 ≤ (22094170700259/50000000000000 : ℝ)^3607 := by
    have hnat : (2646712397 : ℕ)^4631*50000000000000^3607 ≤ 22094170700259^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646712397 5000000000 22094170700259 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713393413/5000000000 : ℝ)^4631 ≤ (45622750173901/100000000000000 : ℝ)^3607 := by
    have hnat : (2713393413 : ℕ)^4631*100000000000000^3607 ≤ 45622750173901^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713393413 5000000000 45622750173901 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1688297709/10000000000 : ℝ)^4631 ≤ (5094454204013/50000000000000 : ℝ)^3607 := by
    have hnat : (1688297709 : ℕ)^4631*50000000000000^3607 ≤ 5094454204013^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1688297709 10000000000 5094454204013 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646712397/5000000000 : ℝ), (2713393413/5000000000 : ℝ), (-1688297709/10000000000 : ℝ)] ![(22094170700259/50000000000000 : ℝ), (45622750173901/100000000000000 : ℝ), (5094454204013/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646712397/5000000000 : ℝ)|^4631 ≤ (22094170700259/50000000000000 : ℝ)^3607
        have hw : |(2646712397/5000000000 : ℝ)|=(2646712397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713393413/5000000000 : ℝ)|^4631 ≤ (45622750173901/100000000000000 : ℝ)^3607
        have hw : |(2713393413/5000000000 : ℝ)|=(2713393413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1688297709/10000000000 : ℝ)|^4631 ≤ (5094454204013/50000000000000 : ℝ)^3607
        have hw : |(-1688297709/10000000000 : ℝ)|=(1688297709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s3_7 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2122365891/5000000000 : ℝ)*x 0 + (2247322993/5000000000 : ℝ)*x 1 + (2003175053/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122365891/5000000000 : ℝ)^4631 ≤ (8320314935011/25000000000000 : ℝ)^3607 := by
    have hnat : (2122365891 : ℕ)^4631*25000000000000^3607 ≤ 8320314935011^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122365891 5000000000 8320314935011 25000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2247322993/5000000000 : ℝ)^4631 ≤ (17908877824201/50000000000000 : ℝ)^3607 := by
    have hnat : (2247322993 : ℕ)^4631*50000000000000^3607 ≤ 17908877824201^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2247322993 5000000000 17908877824201 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2003175053/5000000000 : ℝ)^4631 ≤ (6180196920147/20000000000000 : ℝ)^3607 := by
    have hnat : (2003175053 : ℕ)^4631*20000000000000^3607 ≤ 6180196920147^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003175053 5000000000 6180196920147 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2122365891/5000000000 : ℝ), (2247322993/5000000000 : ℝ), (2003175053/5000000000 : ℝ)] ![(8320314935011/25000000000000 : ℝ), (17908877824201/50000000000000 : ℝ), (6180196920147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2122365891/5000000000 : ℝ)|^4631 ≤ (8320314935011/25000000000000 : ℝ)^3607
        have hw : |(2122365891/5000000000 : ℝ)|=(2122365891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2247322993/5000000000 : ℝ)|^4631 ≤ (17908877824201/50000000000000 : ℝ)^3607
        have hw : |(2247322993/5000000000 : ℝ)|=(2247322993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2003175053/5000000000 : ℝ)|^4631 ≤ (6180196920147/20000000000000 : ℝ)^3607
        have hw : |(2003175053/5000000000 : ℝ)|=(2003175053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1567_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (791/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10803/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5539/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15521/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (791/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10803/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (791/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10803/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (791/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10803/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (791/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10803/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (791/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10803/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (791/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10803/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10803/100000 : ℝ) ^ (4629/1024 : ℝ) ≤ (2138453474997297/50000000000000000000 : ℝ) := by
    have hpowers : (10803/100000 : ℝ)^4629 ≤ (2138453474997297/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10803 : ℕ)^4629*50000000000000000000^1024 ≤ 2138453474997297^1024*100000^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10803 100000 2138453474997297 50000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10803/100000 : ℝ)) (X := (2138453474997297/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (791/5000 : ℝ) ^ (4629/1024 : ℝ) ≤ (23988695559633933/100000000000000000000 : ℝ) := by
    have hpowers : (791/5000 : ℝ)^4629 ≤ (23988695559633933/100000000000000000000 : ℝ)^1024 := by
      have hnat : (791 : ℕ)^4629*100000000000000000000^1024 ≤ 23988695559633933^1024*5000^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        791 5000 23988695559633933 100000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (791/5000 : ℝ)) (X := (23988695559633933/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002138453474997297/25000000000000000000 : ℝ) ≤ (10000189216109323/10000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (25002138453474997297/25000000000000000000 : ℝ)^1024 ≤ (10000189216109323/10000000000000000 : ℝ)^4629 := by
      have hnat : (25002138453474997297 : ℕ)^1024*10000000000000000^4629 ≤ 10000189216109323^4629*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002138453474997297 25000000000000000000 10000189216109323 10000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000189216109323/10000000000000000 : ℝ)) (X := (25002138453474997297/25000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100028265602509628527/100000000000000000000 : ℝ) ≤ (5000312603065523/5000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (100028265602509628527/100000000000000000000 : ℝ)^1024 ≤ (5000312603065523/5000000000000000 : ℝ)^4629 := by
      have hnat : (100028265602509628527 : ℕ)^1024*5000000000000000^4629 ≤ 5000312603065523^4629*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100028265602509628527 100000000000000000000 5000312603065523 5000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000312603065523/5000000000000000 : ℝ)) (X := (100028265602509628527/100000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50023988695559633933/50000000000000000000 : ℝ) ≤ (10001061196152769/10000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (50023988695559633933/50000000000000000000 : ℝ)^1024 ≤ (10001061196152769/10000000000000000 : ℝ)^4629 := by
      have hnat : (50023988695559633933 : ℕ)^1024*10000000000000000^4629 ≤ 10001061196152769^4629*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023988695559633933 50000000000000000000 10001061196152769 10000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001061196152769/10000000000000000 : ℝ)) (X := (50023988695559633933/50000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2138453474997297/50000000000000000000 : ℝ) ≤ ((50161529296811126353/50170000000000000000 : ℝ)+2*(435990021723/501700000000000 : ℝ)*(10803/100000 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (50161529296811126353/50170000000000000000 : ℝ)+2*(435990021723/501700000000000 : ℝ)*(10803/100000 : ℝ)=(10000189216109323/10000000000000000 : ℝ) by norm_num, show 1+2*(2138453474997297/50000000000000000000 : ℝ)=(25002138453474997297/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(23988695559633933/100000000000000000000 : ℝ)+(2138453474997297/50000000000000000000 : ℝ) ≤ ((50161529296811126353/50170000000000000000 : ℝ)+(435990021723/501700000000000 : ℝ)*((791/5000 : ℝ)+(10803/100000 : ℝ)))^(4629/1024 : ℝ) := by
    rw [show (50161529296811126353/50170000000000000000 : ℝ)+(435990021723/501700000000000 : ℝ)*((791/5000 : ℝ)+(10803/100000 : ℝ))=(5000312603065523/5000000000000000 : ℝ) by norm_num, show 1+(23988695559633933/100000000000000000000 : ℝ)+(2138453474997297/50000000000000000000 : ℝ)=(100028265602509628527/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(23988695559633933/100000000000000000000 : ℝ) ≤ ((50161529296811126353/50170000000000000000 : ℝ)+2*(435990021723/501700000000000 : ℝ)*(791/5000 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (50161529296811126353/50170000000000000000 : ℝ)+2*(435990021723/501700000000000 : ℝ)*(791/5000 : ℝ)=(10001061196152769/10000000000000000 : ℝ) by norm_num, show 1+2*(23988695559633933/100000000000000000000 : ℝ)=(50023988695559633933/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (50161529296811126353/50170000000000000000 : ℝ)*(X 1 0+X 2 0)+(435990021723/501700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (10803/100000 : ℝ)) (hi := (791/5000 : ℝ)) (c := (50161529296811126353/50170000000000000000 : ℝ)) (alpha := (435990021723/501700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (50161529296811126353/50170000000000000000 : ℝ)*(X 0 1+X 2 1)+(435990021723/501700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (10803/100000 : ℝ)) (hi := (791/5000 : ℝ)) (c := (50161529296811126353/50170000000000000000 : ℝ)) (alpha := (435990021723/501700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (50161529296811126353/50170000000000000000 : ℝ)*(X 0 2+X 1 2)+(435990021723/501700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (10803/100000 : ℝ)) (hi := (791/5000 : ℝ)) (c := (50161529296811126353/50170000000000000000 : ℝ)) (alpha := (435990021723/501700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-223682679/1250000000 : ℝ)*X 0 0+(5427903037/10000000000 : ℝ)*X 0 1+(5218399587/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348833653/10000000000 : ℝ)*X 1 0+(-948342347/5000000000 : ℝ)*X 1 1+(5218399709/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((167151041/312500000 : ℝ)*X 2 0+(1304599973/2500000000 : ℝ)*X 2 1+(-474171227/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1061166409/2500000000 : ℝ)*X 0 0+(2001860209/5000000000 : ℝ)*X 0 1+(449725583/1000000000 : ℝ)*X 0 2+(1061166409/2500000000 : ℝ)*X 1 0+(2001860209/5000000000 : ℝ)*X 1 1+(449725583/1000000000 : ℝ)*X 1 2+(1061166409/2500000000 : ℝ)*X 2 0+(2001860209/5000000000 : ℝ)*X 2 1+(449725583/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-44737241/250000000 : ℝ)*X 0 0+(1043901493/2000000000 : ℝ)*X 0 1+(2713393409/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646712401/5000000000 : ℝ)*X 1 0+(-1688297733/10000000000 : ℝ)*X 1 1+(2713393401/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2646712397/5000000000 : ℝ)*X 2 0+(2713393413/5000000000 : ℝ)*X 2 1+(-1688297709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2122365891/5000000000 : ℝ)*X 0 0+(2247322993/5000000000 : ℝ)*X 0 1+(2003175053/5000000000 : ℝ)*X 0 2+(2122365891/5000000000 : ℝ)*X 1 0+(2247322993/5000000000 : ℝ)*X 1 1+(2003175053/5000000000 : ℝ)*X 1 2+(2122365891/5000000000 : ℝ)*X 2 0+(2247322993/5000000000 : ℝ)*X 2 1+(2003175053/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222418604220403738745067/25085000000000000000000000000 : ℝ) := by norm_num
    linear_combination (812245169/50000000000000 : ℝ)*(base19) + (70081153/6250000000000 : ℝ)*(base23) + (106381381/100000000000000 : ℝ)*(lower2) + (201651229/50000000000000 : ℝ)*(upper3) + (8877/5000000000000 : ℝ)*(upper5) + (106241633779167/3125000000000 : ℝ)*(major0) + (106241633779167/3125000000000 : ℝ)*(major1) + (106241633779167/3125000000000 : ℝ)*(major2) + (4773223508796329/100000000000000 : ℝ)*(sp0) + (2386621300212509/50000000000000 : ℝ)*(sp1) + (1193310775904227/25000000000000 : ℝ)*(sp2) + (202620639515053/10000000000000 : ℝ)*(sp3) + (20716119027/100000000000000 : ℝ)*(sp4) + (13646247537/100000000000000 : ℝ)*(sp7) + (506555010349517/25000000000000 : ℝ)*(f.failure) + (1193311056228839/25000000000000 : ℝ)*(f.sum) + (19568887045101/12542500000000000000000000000 : ℝ)*base65 + (507423438568000451/156781250000000000000000000000000 : ℝ)*base67 + (832230839706280799/156781250000000000000000000000000 : ℝ)*base70 + (320541283214687951/156781250000000000000000000000000 : ℝ)*base71 + (69996774340831/12542500000000000000000000000 : ℝ)*base73 + (1967988322937562049/156781250000000000000000000000000 : ℝ)*base76 + (747971309135749549/156781250000000000000000000000000 : ℝ)*base78 + (528120725895000451/156781250000000000000000000000000 : ℝ)*base79 + (47842068230641/12542500000000000000000000000 : ℝ)*base81 + (5578927/625000000000000000000 : ℝ)*base89 + (5578927/625000000000000000000 : ℝ)*base91 + (5578927/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2886917303986723434383229513/313562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (177818459/12500000000000 : ℝ)*(base19) + (1520937353/100000000000000 : ℝ)*(base23) + (183859953/100000000000000 : ℝ)*(upper3) + (11639539/25000000000000 : ℝ)*(lower4) + (194729021/100000000000000 : ℝ)*(upper5) + (429521578814593/12500000000000 : ℝ)*(major0) + (429521578814593/12500000000000 : ℝ)*(major1) + (429521578814593/12500000000000 : ℝ)*(major2) + (22025470423/100000000000000 : ℝ)*(sp1) + (11859531009/50000000000000 : ℝ)*(sp2) + (1206101670756897/25000000000000 : ℝ)*(sp4) + (4824383235009493/100000000000000 : ℝ)*(sp5) + (603047680378527/12500000000000 : ℝ)*(sp6) + (1023969135555743/50000000000000 : ℝ)*(sp7) + (1023969135555743/50000000000000 : ℝ)*(f.failure) + (1206101670756897/25000000000000 : ℝ)*(f.sum) + (49138198713173/6271250000000000000000000000 : ℝ)*base65 + (531916544573169329/627125000000000000000000000000000 : ℝ)*base67 + (1498784997805330671/627125000000000000000000000000000 : ℝ)*base70 + (3849220258486044329/627125000000000000000000000000000 : ℝ)*base71 + (119793935732387/25085000000000000000000000000 : ℝ)*base73 + (269421392961955671/627125000000000000000000000000000 : ℝ)*base76 + (2821901388016669329/627125000000000000000000000000000 : ℝ)*base77 + (4730151962669329/627125000000000000000000000000000 : ℝ)*base79 + (23563626758117/6271250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (12873867/1250000000000000000000 : ℝ)*base90 + (12873867/1250000000000000000000 : ℝ)*base92 + (12873867/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1567_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (791/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10803/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5539/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15521/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1567_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1567_s4_0 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-894847733/5000000000 : ℝ)*x 0 + (1085268323/2000000000 : ℝ)*x 1 + (2609902861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (894847733/5000000000 : ℝ)^4631 ≤ (2680950791/24414062500 : ℝ)^3607 := by
    have hnat : (894847733 : ℕ)^4631*24414062500^3607 ≤ 2680950791^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894847733 5000000000 2680950791 24414062500 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085268323/2000000000 : ℝ)^4631 ≤ (45617944789143/100000000000000 : ℝ)^3607 := by
    have hnat : (1085268323 : ℕ)^4631*100000000000000^3607 ≤ 45617944789143^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085268323 2000000000 45617944789143 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2609902861/5000000000 : ℝ)^4631 ≤ (43400880757079/100000000000000 : ℝ)^3607 := by
    have hnat : (2609902861 : ℕ)^4631*100000000000000^3607 ≤ 43400880757079^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2609902861 5000000000 43400880757079 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-894847733/5000000000 : ℝ), (1085268323/2000000000 : ℝ), (2609902861/5000000000 : ℝ)] ![(2680950791/24414062500 : ℝ), (45617944789143/100000000000000 : ℝ), (43400880757079/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-894847733/5000000000 : ℝ)|^4631 ≤ (2680950791/24414062500 : ℝ)^3607
        have hw : |(-894847733/5000000000 : ℝ)|=(894847733/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085268323/2000000000 : ℝ)|^4631 ≤ (45617944789143/100000000000000 : ℝ)^3607
        have hw : |(1085268323/2000000000 : ℝ)|=(1085268323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2609902861/5000000000 : ℝ)|^4631 ≤ (43400880757079/100000000000000 : ℝ)^3607
        have hw : |(2609902861/5000000000 : ℝ)|=(2609902861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s4_1 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348419993/10000000000 : ℝ)*x 0 + (-1895365709/10000000000 : ℝ)*x 1 + (5219805717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348419993/10000000000 : ℝ)^4631 ≤ (22389313905731/50000000000000 : ℝ)^3607 := by
    have hnat : (5348419993 : ℕ)^4631*50000000000000^3607 ≤ 22389313905731^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348419993 10000000000 22389313905731 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1895365709/10000000000 : ℝ)^4631 ≤ (11820491474107/100000000000000 : ℝ)^3607 := by
    have hnat : (1895365709 : ℕ)^4631*100000000000000^3607 ≤ 11820491474107^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895365709 10000000000 11820491474107 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219805717/10000000000 : ℝ)^4631 ≤ (43400880703703/100000000000000 : ℝ)^3607 := by
    have hnat : (5219805717 : ℕ)^4631*100000000000000^3607 ≤ 43400880703703^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219805717 10000000000 43400880703703 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348419993/10000000000 : ℝ), (-1895365709/10000000000 : ℝ), (5219805717/10000000000 : ℝ)] ![(22389313905731/50000000000000 : ℝ), (11820491474107/100000000000000 : ℝ), (43400880703703/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348419993/10000000000 : ℝ)|^4631 ≤ (22389313905731/50000000000000 : ℝ)^3607
        have hw : |(5348419993/10000000000 : ℝ)|=(5348419993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1895365709/10000000000 : ℝ)|^4631 ≤ (11820491474107/100000000000000 : ℝ)^3607
        have hw : |(-1895365709/10000000000 : ℝ)|=(1895365709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219805717/10000000000 : ℝ)|^4631 ≤ (43400880703703/100000000000000 : ℝ)^3607
        have hw : |(5219805717/10000000000 : ℝ)|=(5219805717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s4_2 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337104997/2500000000 : ℝ)*x 0 + (5219805739/10000000000 : ℝ)*x 1 + (-379073137/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337104997/2500000000 : ℝ)^4631 ≤ (11194656939429/25000000000000 : ℝ)^3607 := by
    have hnat : (1337104997 : ℕ)^4631*25000000000000^3607 ≤ 11194656939429^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337104997 2500000000 11194656939429 25000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219805739/10000000000 : ℝ)^4631 ≤ (10850220234639/25000000000000 : ℝ)^3607 := by
    have hnat : (5219805739 : ℕ)^4631*25000000000000^3607 ≤ 10850220234639^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219805739 10000000000 10850220234639 25000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379073137/2000000000 : ℝ)^4631 ≤ (11820491281939/100000000000000 : ℝ)^3607 := by
    have hnat : (379073137 : ℕ)^4631*100000000000000^3607 ≤ 11820491281939^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379073137 2000000000 11820491281939 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337104997/2500000000 : ℝ), (5219805739/10000000000 : ℝ), (-379073137/2000000000 : ℝ)] ![(11194656939429/25000000000000 : ℝ), (10850220234639/25000000000000 : ℝ), (11820491281939/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337104997/2500000000 : ℝ)|^4631 ≤ (11194656939429/25000000000000 : ℝ)^3607
        have hw : |(1337104997/2500000000 : ℝ)|=(1337104997/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219805739/10000000000 : ℝ)|^4631 ≤ (10850220234639/25000000000000 : ℝ)^3607
        have hw : |(5219805739/10000000000 : ℝ)|=(5219805739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-379073137/2000000000 : ℝ)|^4631 ≤ (11820491281939/100000000000000 : ℝ)^3607
        have hw : |(-379073137/2000000000 : ℝ)|=(379073137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s4_3 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (424481267/1000000000 : ℝ)*x 0 + (2003599821/5000000000 : ℝ)*x 1 + (4493744103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424481267/1000000000 : ℝ)^4631 ≤ (33282074000631/100000000000000 : ℝ)^3607 := by
    have hnat : (424481267 : ℕ)^4631*100000000000000^3607 ≤ 33282074000631^3607*1000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424481267 1000000000 33282074000631 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2003599821/5000000000 : ℝ)^4631 ≤ (1236375900951/4000000000000 : ℝ)^3607 := by
    have hnat : (2003599821 : ℕ)^4631*4000000000000^3607 ≤ 1236375900951^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003599821 5000000000 1236375900951 4000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493744103/10000000000 : ℝ)^4631 ≤ (35808528460867/100000000000000 : ℝ)^3607 := by
    have hnat : (4493744103 : ℕ)^4631*100000000000000^3607 ≤ 35808528460867^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493744103 10000000000 35808528460867 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(424481267/1000000000 : ℝ), (2003599821/5000000000 : ℝ), (4493744103/10000000000 : ℝ)] ![(33282074000631/100000000000000 : ℝ), (1236375900951/4000000000000 : ℝ), (35808528460867/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(424481267/1000000000 : ℝ)|^4631 ≤ (33282074000631/100000000000000 : ℝ)^3607
        have hw : |(424481267/1000000000 : ℝ)|=(424481267/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2003599821/5000000000 : ℝ)|^4631 ≤ (1236375900951/4000000000000 : ℝ)^3607
        have hw : |(2003599821/5000000000 : ℝ)|=(2003599821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493744103/10000000000 : ℝ)|^4631 ≤ (35808528460867/100000000000000 : ℝ)^3607
        have hw : |(4493744103/10000000000 : ℝ)|=(4493744103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s4_4 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1789722187/10000000000 : ℝ)*x 0 + (5220882887/10000000000 : ℝ)*x 1 + (5425256687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1789722187/10000000000 : ℝ)^4631 ≤ (1372673117481/12500000000000 : ℝ)^3607 := by
    have hnat : (1789722187 : ℕ)^4631*12500000000000^3607 ≤ 1372673117481^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789722187 10000000000 1372673117481 12500000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220882887/10000000000 : ℝ)^4631 ≤ (43412379961559/100000000000000 : ℝ)^3607 := by
    have hnat : (5220882887 : ℕ)^4631*100000000000000^3607 ≤ 43412379961559^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220882887 10000000000 43412379961559 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425256687/10000000000 : ℝ)^4631 ≤ (45606235087917/100000000000000 : ℝ)^3607 := by
    have hnat : (5425256687 : ℕ)^4631*100000000000000^3607 ≤ 45606235087917^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425256687 10000000000 45606235087917 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1789722187/10000000000 : ℝ), (5220882887/10000000000 : ℝ), (5425256687/10000000000 : ℝ)] ![(1372673117481/12500000000000 : ℝ), (43412379961559/100000000000000 : ℝ), (45606235087917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1789722187/10000000000 : ℝ)|^4631 ≤ (1372673117481/12500000000000 : ℝ)^3607
        have hw : |(-1789722187/10000000000 : ℝ)|=(1789722187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220882887/10000000000 : ℝ)|^4631 ≤ (43412379961559/100000000000000 : ℝ)^3607
        have hw : |(5220882887/10000000000 : ℝ)|=(5220882887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425256687/10000000000 : ℝ)|^4631 ≤ (45606235087917/100000000000000 : ℝ)^3607
        have hw : |(5425256687/10000000000 : ℝ)|=(5425256687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s4_5 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323449097/2500000000 : ℝ)*x 0 + (-422478691/2500000000 : ℝ)*x 1 + (1085051361/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323449097/2500000000 : ℝ)^4631 ≤ (8838464810967/20000000000000 : ℝ)^3607 := by
    have hnat : (1323449097 : ℕ)^4631*20000000000000^3607 ≤ 8838464810967^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323449097 2500000000 8838464810967 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (422478691/2500000000 : ℝ)^4631 ≤ (10201439562537/100000000000000 : ℝ)^3607 := by
    have hnat : (422478691 : ℕ)^4631*100000000000000^3607 ≤ 10201439562537^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422478691 2500000000 10201439562537 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085051361/2000000000 : ℝ)^4631 ≤ (45606236361463/100000000000000 : ℝ)^3607 := by
    have hnat : (1085051361 : ℕ)^4631*100000000000000^3607 ≤ 45606236361463^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085051361 2000000000 45606236361463 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323449097/2500000000 : ℝ), (-422478691/2500000000 : ℝ), (1085051361/2000000000 : ℝ)] ![(8838464810967/20000000000000 : ℝ), (10201439562537/100000000000000 : ℝ), (45606236361463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323449097/2500000000 : ℝ)|^4631 ≤ (8838464810967/20000000000000 : ℝ)^3607
        have hw : |(1323449097/2500000000 : ℝ)|=(1323449097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-422478691/2500000000 : ℝ)|^4631 ≤ (10201439562537/100000000000000 : ℝ)^3607
        have hw : |(-422478691/2500000000 : ℝ)|=(422478691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085051361/2000000000 : ℝ)|^4631 ≤ (45606236361463/100000000000000 : ℝ)^3607
        have hw : |(1085051361/2000000000 : ℝ)|=(1085051361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s4_6 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293796361/10000000000 : ℝ)*x 0 + (5425256999/10000000000 : ℝ)*x 1 + (-422478633/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293796361/10000000000 : ℝ)^4631 ≤ (44192323765453/100000000000000 : ℝ)^3607 := by
    have hnat : (5293796361 : ℕ)^4631*100000000000000^3607 ≤ 44192323765453^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293796361 10000000000 44192323765453 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425256999/10000000000 : ℝ)^4631 ≤ (45606238455259/100000000000000 : ℝ)^3607 := by
    have hnat : (5425256999 : ℕ)^4631*100000000000000^3607 ≤ 45606238455259^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425256999 10000000000 45606238455259 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (422478633/2500000000 : ℝ)^4631 ≤ (10201437764439/100000000000000 : ℝ)^3607 := by
    have hnat : (422478633 : ℕ)^4631*100000000000000^3607 ≤ 10201437764439^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      422478633 2500000000 10201437764439 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293796361/10000000000 : ℝ), (5425256999/10000000000 : ℝ), (-422478633/2500000000 : ℝ)] ![(44192323765453/100000000000000 : ℝ), (45606238455259/100000000000000 : ℝ), (10201437764439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293796361/10000000000 : ℝ)|^4631 ≤ (44192323765453/100000000000000 : ℝ)^3607
        have hw : |(5293796361/10000000000 : ℝ)|=(5293796361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425256999/10000000000 : ℝ)|^4631 ≤ (45606238455259/100000000000000 : ℝ)^3607
        have hw : |(5425256999/10000000000 : ℝ)|=(5425256999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-422478633/2500000000 : ℝ)|^4631 ≤ (10201437764439/100000000000000 : ℝ)^3607
        have hw : |(-422478633/2500000000 : ℝ)|=(422478633/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s4_7 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4244876273/10000000000 : ℝ)*x 0 + (2245603787/5000000000 : ℝ)*x 1 + (2004877477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244876273/10000000000 : ℝ)^4631 ≤ (8320678566133/25000000000000 : ℝ)^3607 := by
    have hnat : (4244876273 : ℕ)^4631*25000000000000^3607 ≤ 8320678566133^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244876273 10000000000 8320678566133 25000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245603787/5000000000 : ℝ)^4631 ≤ (35782579987971/100000000000000 : ℝ)^3607 := by
    have hnat : (2245603787 : ℕ)^4631*100000000000000^3607 ≤ 35782579987971^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245603787 5000000000 35782579987971 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004877477/5000000000 : ℝ)^4631 ≤ (3093470573417/10000000000000 : ℝ)^3607 := by
    have hnat : (2004877477 : ℕ)^4631*10000000000000^3607 ≤ 3093470573417^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004877477 5000000000 3093470573417 10000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244876273/10000000000 : ℝ), (2245603787/5000000000 : ℝ), (2004877477/5000000000 : ℝ)] ![(8320678566133/25000000000000 : ℝ), (35782579987971/100000000000000 : ℝ), (3093470573417/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244876273/10000000000 : ℝ)|^4631 ≤ (8320678566133/25000000000000 : ℝ)^3607
        have hw : |(4244876273/10000000000 : ℝ)|=(4244876273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245603787/5000000000 : ℝ)|^4631 ≤ (35782579987971/100000000000000 : ℝ)^3607
        have hw : |(2245603787/5000000000 : ℝ)|=(2245603787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2004877477/5000000000 : ℝ)|^4631 ≤ (3093470573417/10000000000000 : ℝ)^3607
        have hw : |(2004877477/5000000000 : ℝ)|=(2004877477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1567_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15521/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5539/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2777/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (484/3125 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15521/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5539/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15521/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5539/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15521/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5539/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15521/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5539/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15521/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5539/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15521/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5539/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5539/50000 : ℝ) ^ (4629/1024 : ℝ) ≤ (479159514718561/10000000000000000000 : ℝ) := by
    have hpowers : (5539/50000 : ℝ)^4629 ≤ (479159514718561/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5539 : ℕ)^4629*10000000000000000000^1024 ≤ 479159514718561^1024*50000^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5539 50000 479159514718561 10000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5539/50000 : ℝ)) (X := (479159514718561/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15521/100000 : ℝ) ^ (4629/1024 : ℝ) ≤ (11003128435009877/50000000000000000000 : ℝ) := by
    have hpowers : (15521/100000 : ℝ)^4629 ≤ (11003128435009877/50000000000000000000 : ℝ)^1024 := by
      have hnat : (15521 : ℕ)^4629*50000000000000000000^1024 ≤ 11003128435009877^1024*100000^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15521 100000 11003128435009877 50000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15521/100000 : ℝ)) (X := (11003128435009877/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000479159514718561/5000000000000000000 : ℝ) ≤ (10000211985756983/10000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (5000479159514718561/5000000000000000000 : ℝ)^1024 ≤ (10000211985756983/10000000000000000 : ℝ)^4629 := by
      have hnat : (5000479159514718561 : ℕ)^1024*10000000000000000^4629 ≤ 10000211985756983^4629*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000479159514718561 5000000000000000000 10000211985756983 10000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000211985756983/10000000000000000 : ℝ)) (X := (5000479159514718561/5000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006699463004301341/25000000000000000000 : ℝ) ≤ (400023709775313/400000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (25006699463004301341/25000000000000000000 : ℝ)^1024 ≤ (400023709775313/400000000000000 : ℝ)^4629 := by
      have hnat : (25006699463004301341 : ℕ)^1024*400000000000000^4629 ≤ 400023709775313^4629*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006699463004301341 25000000000000000000 400023709775313 400000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400023709775313/400000000000000 : ℝ)) (X := (25006699463004301341/25000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25011003128435009877/25000000000000000000 : ℝ) ≤ (10000973503008667/10000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (25011003128435009877/25000000000000000000 : ℝ)^1024 ≤ (10000973503008667/10000000000000000 : ℝ)^4629 := by
      have hnat : (25011003128435009877 : ℕ)^1024*10000000000000000^4629 ≤ 10000973503008667^4629*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011003128435009877 25000000000000000000 10000973503008667 10000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000973503008667/10000000000000000 : ℝ)) (X := (25011003128435009877/25000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(479159514718561/10000000000000000000 : ℝ) ≤ ((44422505764604120117/44430000000000000000 : ℝ)+2*(190379312921/222150000000000 : ℝ)*(5539/50000 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (44422505764604120117/44430000000000000000 : ℝ)+2*(190379312921/222150000000000 : ℝ)*(5539/50000 : ℝ)=(10000211985756983/10000000000000000 : ℝ) by norm_num, show 1+2*(479159514718561/10000000000000000000 : ℝ)=(5000479159514718561/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11003128435009877/50000000000000000000 : ℝ)+(479159514718561/10000000000000000000 : ℝ) ≤ ((44422505764604120117/44430000000000000000 : ℝ)+(190379312921/222150000000000 : ℝ)*((15521/100000 : ℝ)+(5539/50000 : ℝ)))^(4629/1024 : ℝ) := by
    rw [show (44422505764604120117/44430000000000000000 : ℝ)+(190379312921/222150000000000 : ℝ)*((15521/100000 : ℝ)+(5539/50000 : ℝ))=(400023709775313/400000000000000 : ℝ) by norm_num, show 1+(11003128435009877/50000000000000000000 : ℝ)+(479159514718561/10000000000000000000 : ℝ)=(25006699463004301341/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11003128435009877/50000000000000000000 : ℝ) ≤ ((44422505764604120117/44430000000000000000 : ℝ)+2*(190379312921/222150000000000 : ℝ)*(15521/100000 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (44422505764604120117/44430000000000000000 : ℝ)+2*(190379312921/222150000000000 : ℝ)*(15521/100000 : ℝ)=(10000973503008667/10000000000000000 : ℝ) by norm_num, show 1+2*(11003128435009877/50000000000000000000 : ℝ)=(25011003128435009877/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (44422505764604120117/44430000000000000000 : ℝ)*(X 1 0+X 2 0)+(190379312921/222150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (5539/50000 : ℝ)) (hi := (15521/100000 : ℝ)) (c := (44422505764604120117/44430000000000000000 : ℝ)) (alpha := (190379312921/222150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (44422505764604120117/44430000000000000000 : ℝ)*(X 0 1+X 2 1)+(190379312921/222150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (5539/50000 : ℝ)) (hi := (15521/100000 : ℝ)) (c := (44422505764604120117/44430000000000000000 : ℝ)) (alpha := (190379312921/222150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (44422505764604120117/44430000000000000000 : ℝ)*(X 0 2+X 1 2)+(190379312921/222150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (5539/50000 : ℝ)) (hi := (15521/100000 : ℝ)) (c := (44422505764604120117/44430000000000000000 : ℝ)) (alpha := (190379312921/222150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-894847733/5000000000 : ℝ)*X 0 0+(1085268323/2000000000 : ℝ)*X 0 1+(2609902861/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348419993/10000000000 : ℝ)*X 1 0+(-1895365709/10000000000 : ℝ)*X 1 1+(5219805717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337104997/2500000000 : ℝ)*X 2 0+(5219805739/10000000000 : ℝ)*X 2 1+(-379073137/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((424481267/1000000000 : ℝ)*X 0 0+(2003599821/5000000000 : ℝ)*X 0 1+(4493744103/10000000000 : ℝ)*X 0 2+(424481267/1000000000 : ℝ)*X 1 0+(2003599821/5000000000 : ℝ)*X 1 1+(4493744103/10000000000 : ℝ)*X 1 2+(424481267/1000000000 : ℝ)*X 2 0+(2003599821/5000000000 : ℝ)*X 2 1+(4493744103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1789722187/10000000000 : ℝ)*X 0 0+(5220882887/10000000000 : ℝ)*X 0 1+(5425256687/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323449097/2500000000 : ℝ)*X 1 0+(-422478691/2500000000 : ℝ)*X 1 1+(1085051361/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293796361/10000000000 : ℝ)*X 2 0+(5425256999/10000000000 : ℝ)*X 2 1+(-422478633/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4244876273/10000000000 : ℝ)*X 0 0+(2245603787/5000000000 : ℝ)*X 0 1+(2004877477/5000000000 : ℝ)*X 0 2+(4244876273/10000000000 : ℝ)*X 1 0+(2245603787/5000000000 : ℝ)*X 1 1+(2004877477/5000000000 : ℝ)*X 1 2+(4244876273/10000000000 : ℝ)*X 2 0+(2245603787/5000000000 : ℝ)*X 2 1+(2004877477/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (58214843328253771762004871/5785156250000000000000000000000 : ℝ) := by norm_num
    linear_combination (867487787/50000000000000 : ℝ)*(base19) + (161686597/10000000000000 : ℝ)*(base23) + (60749063/100000000000000 : ℝ)*(lower2) + (59324033/25000000000000 : ℝ)*(upper3) + (17829617/10000000000000 : ℝ)*(upper5) + (215536450153377/6250000000000 : ℝ)*(major0) + (215536450153377/6250000000000 : ℝ)*(major1) + (215536450153377/6250000000000 : ℝ)*(major2) + (4841802472409529/100000000000000 : ℝ)*(sp0) + (4841829436981993/100000000000000 : ℝ)*(sp1) + (4841829555091597/100000000000000 : ℝ)*(sp2) + (256915274862243/12500000000000 : ℝ)*(sp3) + (14349774019/50000000000000 : ℝ)*(sp4) + (12698626033/100000000000000 : ℝ)*(sp7) + (256916862190497/12500000000000 : ℝ)*(f.failure) + (4841831171957567/100000000000000 : ℝ)*(f.sum) + (5281791753297/7405000000000000000000000000 : ℝ)*base66 + (1396084476057075797/92562500000000000000000000000000 : ℝ)*base68 + (551276880287513297/92562500000000000000000000000000 : ℝ)*base70 + (820305600861263297/92562500000000000000000000000000 : ℝ)*base72 + (16606118180317/7405000000000000000000000000 : ℝ)*base74 + (981572075643575797/92562500000000000000000000000000 : ℝ)*base76 + (140173365417049203/92562500000000000000000000000000 : ℝ)*base77 + (1574489451700950797/92562500000000000000000000000000 : ℝ)*base80 + (5857239477203/7405000000000000000000000000 : ℝ)*base81 + (1584693/312500000000000000000 : ℝ)*base90 + (1584693/312500000000000000000 : ℝ)*base92 + (1584693/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4605089805117501171062579883/740500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (153242331/50000000000000 : ℝ)*(base19) + (752698023/100000000000000 : ℝ)*(base23) + (117491493/100000000000000 : ℝ)*(upper3) + (173924217/100000000000000 : ℝ)*(lower4) + (697003974587911/20000000000000 : ℝ)*(major0) + (697003974587911/20000000000000 : ℝ)*(major1) + (871254968234889/25000000000000 : ℝ)*(major2) + (489499929/12500000000000 : ℝ)*(sp1) + (17738426327/100000000000000 : ℝ)*(sp2) + (358983629/25000000000000 : ℝ)*(sp3) + (978597720813111/20000000000000 : ℝ)*(sp4) + (4892984381581461/100000000000000 : ℝ)*(sp5) + (978594022588241/20000000000000 : ℝ)*(sp6) + (2077049498582619/100000000000000 : ℝ)*(sp7) + (129815683407321/6250000000000 : ℝ)*(f.failure) + (978597720813111/20000000000000 : ℝ)*(f.sum) + (2030604293999/22215000000000000000000000000 : ℝ)*base66 + (5116393398518654413/888600000000000000000000000000000 : ℝ)*base68 + (11679610043474662013/1110750000000000000000000000000000 : ℝ)*base69 + (7228477137475454413/888600000000000000000000000000000 : ℝ)*base72 + (52731944002741/22215000000000000000000000000 : ℝ)*base73 + (8098187091011662013/1110750000000000000000000000000000 : ℝ)*base75 + (1337764386596831471/296200000000000000000000000000000 : ℝ)*base78 + (1052765627307568529/296200000000000000000000000000000 : ℝ)*base79 + (4131321371369/888600000000000000000000000 : ℝ)*base81 + (2730151/156250000000000000000 : ℝ)*base89 + (2730151/156250000000000000000 : ℝ)*base91 + (1167651/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1567_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15521/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5539/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2777/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (484/3125 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1567_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1567_s5_0 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-89486017/500000000 : ℝ)*x 0 + (2713090221/5000000000 : ℝ)*x 1 + (1304987581/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (89486017/500000000 : ℝ)^4631 ≤ (2196274077943/20000000000000 : ℝ)^3607 := by
    have hnat : (89486017 : ℕ)^4631*20000000000000^3607 ≤ 2196274077943^3607*500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89486017 500000000 2196274077943 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713090221/5000000000 : ℝ)^4631 ≤ (5702025649503/12500000000000 : ℝ)^3607 := by
    have hnat : (2713090221 : ℕ)^4631*12500000000000^3607 ≤ 5702025649503^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713090221 5000000000 5702025649503 12500000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304987581/2500000000 : ℝ)^4631 ≤ (10850606101781/25000000000000 : ℝ)^3607 := by
    have hnat : (1304987581 : ℕ)^4631*25000000000000^3607 ≤ 10850606101781^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304987581 2500000000 10850606101781 25000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-89486017/500000000 : ℝ), (2713090221/5000000000 : ℝ), (1304987581/2500000000 : ℝ)] ![(2196274077943/20000000000000 : ℝ), (5702025649503/12500000000000 : ℝ), (10850606101781/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-89486017/500000000 : ℝ)|^4631 ≤ (2196274077943/20000000000000 : ℝ)^3607
        have hw : |(-89486017/500000000 : ℝ)|=(89486017/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713090221/5000000000 : ℝ)|^4631 ≤ (5702025649503/12500000000000 : ℝ)^3607
        have hw : |(2713090221/5000000000 : ℝ)|=(2713090221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304987581/2500000000 : ℝ)|^4631 ≤ (10850606101781/25000000000000 : ℝ)^3607
        have hw : |(1304987581/2500000000 : ℝ)|=(1304987581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s5_1 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348377167/10000000000 : ℝ)*x 0 + (-947615343/5000000000 : ℝ)*x 1 + (5219950113/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348377167/10000000000 : ℝ)^4631 ≤ (44778167469107/100000000000000 : ℝ)^3607 := by
    have hnat : (5348377167 : ℕ)^4631*100000000000000^3607 ≤ 44778167469107^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348377167 10000000000 44778167469107 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (947615343/5000000000 : ℝ)^4631 ≤ (590970517629/5000000000000 : ℝ)^3607 := by
    have hnat : (947615343 : ℕ)^4631*5000000000000^3607 ≤ 590970517629^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      947615343 5000000000 590970517629 5000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219950113/10000000000 : ℝ)^4631 ≤ (1356325692333/3125000000000 : ℝ)^3607 := by
    have hnat : (5219950113 : ℕ)^4631*3125000000000^3607 ≤ 1356325692333^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219950113 10000000000 1356325692333 3125000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348377167/10000000000 : ℝ), (-947615343/5000000000 : ℝ), (5219950113/10000000000 : ℝ)] ![(44778167469107/100000000000000 : ℝ), (590970517629/5000000000000 : ℝ), (1356325692333/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348377167/10000000000 : ℝ)|^4631 ≤ (44778167469107/100000000000000 : ℝ)^3607
        have hw : |(5348377167/10000000000 : ℝ)|=(5348377167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-947615343/5000000000 : ℝ)|^4631 ≤ (590970517629/5000000000000 : ℝ)^3607
        have hw : |(-947615343/5000000000 : ℝ)|=(947615343/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219950113/10000000000 : ℝ)|^4631 ≤ (1356325692333/3125000000000 : ℝ)^3607
        have hw : |(5219950113/10000000000 : ℝ)|=(5219950113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s5_2 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348377037/10000000000 : ℝ)*x 0 + (163123441/312500000 : ℝ)*x 1 + (-1895230863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348377037/10000000000 : ℝ)^4631 ≤ (22389083035861/50000000000000 : ℝ)^3607 := by
    have hnat : (5348377037 : ℕ)^4631*50000000000000^3607 ≤ 22389083035861^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348377037 10000000000 22389083035861 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163123441/312500000 : ℝ)^4631 ≤ (43402422143981/100000000000000 : ℝ)^3607 := by
    have hnat : (163123441 : ℕ)^4631*100000000000000^3607 ≤ 43402422143981^3607*312500000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163123441 312500000 43402422143981 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1895230863/10000000000 : ℝ)^4631 ≤ (2363882353959/20000000000000 : ℝ)^3607 := by
    have hnat : (1895230863 : ℕ)^4631*20000000000000^3607 ≤ 2363882353959^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1895230863 10000000000 2363882353959 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348377037/10000000000 : ℝ), (163123441/312500000 : ℝ), (-1895230863/10000000000 : ℝ)] ![(22389083035861/50000000000000 : ℝ), (43402422143981/100000000000000 : ℝ), (2363882353959/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348377037/10000000000 : ℝ)|^4631 ≤ (22389083035861/50000000000000 : ℝ)^3607
        have hw : |(5348377037/10000000000 : ℝ)|=(5348377037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163123441/312500000 : ℝ)|^4631 ≤ (43402422143981/100000000000000 : ℝ)^3607
        have hw : |(163123441/312500000 : ℝ)|=(163123441/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1895230863/10000000000 : ℝ)|^4631 ≤ (2363882353959/20000000000000 : ℝ)^3607
        have hw : |(-1895230863/10000000000 : ℝ)|=(1895230863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s5_3 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4244828031/10000000000 : ℝ)*x 0 + (4007557111/10000000000 : ℝ)*x 1 + (4493382953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4244828031/10000000000 : ℝ)^4631 ≤ (33282228632927/100000000000000 : ℝ)^3607 := by
    have hnat : (4244828031 : ℕ)^4631*100000000000000^3607 ≤ 33282228632927^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244828031 10000000000 33282228632927 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4007557111/10000000000 : ℝ)^4631 ≤ (30912937677193/100000000000000 : ℝ)^3607 := by
    have hnat : (4007557111 : ℕ)^4631*100000000000000^3607 ≤ 30912937677193^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4007557111 10000000000 30912937677193 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493382953/10000000000 : ℝ)^4631 ≤ (35804833673587/100000000000000 : ℝ)^3607 := by
    have hnat : (4493382953 : ℕ)^4631*100000000000000^3607 ≤ 35804833673587^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493382953 10000000000 35804833673587 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4244828031/10000000000 : ℝ), (4007557111/10000000000 : ℝ), (4493382953/10000000000 : ℝ)] ![(33282228632927/100000000000000 : ℝ), (30912937677193/100000000000000 : ℝ), (35804833673587/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4244828031/10000000000 : ℝ)|^4631 ≤ (33282228632927/100000000000000 : ℝ)^3607
        have hw : |(4244828031/10000000000 : ℝ)|=(4244828031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4007557111/10000000000 : ℝ)|^4631 ≤ (30912937677193/100000000000000 : ℝ)^3607
        have hw : |(4007557111/10000000000 : ℝ)|=(4007557111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493382953/10000000000 : ℝ)|^4631 ≤ (35804833673587/100000000000000 : ℝ)^3607
        have hw : |(4493382953/10000000000 : ℝ)|=(4493382953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s5_4 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1789747143/10000000000 : ℝ)*x 0 + (5221024051/10000000000 : ℝ)*x 1 + (5425098837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1789747143/10000000000 : ℝ)^4631 ≤ (686348846027/6250000000000 : ℝ)^3607 := by
    have hnat : (1789747143 : ℕ)^4631*6250000000000^3607 ≤ 686348846027^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1789747143 10000000000 686348846027 6250000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221024051/10000000000 : ℝ)^4631 ≤ (21706943499263/50000000000000 : ℝ)^3607 := by
    have hnat : (5221024051 : ℕ)^4631*50000000000000^3607 ≤ 21706943499263^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221024051 10000000000 21706943499263 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5425098837/10000000000 : ℝ)^4631 ≤ (45604531457593/100000000000000 : ℝ)^3607 := by
    have hnat : (5425098837 : ℕ)^4631*100000000000000^3607 ≤ 45604531457593^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425098837 10000000000 45604531457593 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1789747143/10000000000 : ℝ), (5221024051/10000000000 : ℝ), (5425098837/10000000000 : ℝ)] ![(686348846027/6250000000000 : ℝ), (21706943499263/50000000000000 : ℝ), (45604531457593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1789747143/10000000000 : ℝ)|^4631 ≤ (686348846027/6250000000000 : ℝ)^3607
        have hw : |(-1789747143/10000000000 : ℝ)|=(1789747143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221024051/10000000000 : ℝ)|^4631 ≤ (21706943499263/50000000000000 : ℝ)^3607
        have hw : |(5221024051/10000000000 : ℝ)|=(5221024051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5425098837/10000000000 : ℝ)|^4631 ≤ (45604531457593/100000000000000 : ℝ)^3607
        have hw : |(5425098837/10000000000 : ℝ)|=(5425098837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s5_5 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (330864661/625000000 : ℝ)*x 0 + (-1690081447/10000000000 : ℝ)*x 1 + (2712549591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330864661/625000000 : ℝ)^4631 ≤ (44192733349049/100000000000000 : ℝ)^3607 := by
    have hnat : (330864661 : ℕ)^4631*100000000000000^3607 ≤ 44192733349049^3607*625000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330864661 625000000 44192733349049 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1690081447/10000000000 : ℝ)^4631 ≤ (318835357627/3125000000000 : ℝ)^3607 := by
    have hnat : (1690081447 : ℕ)^4631*3125000000000^3607 ≤ 318835357627^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1690081447 10000000000 318835357627 3125000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712549591/5000000000 : ℝ)^4631 ≤ (9120907036213/20000000000000 : ℝ)^3607 := by
    have hnat : (2712549591 : ℕ)^4631*20000000000000^3607 ≤ 9120907036213^3607*5000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712549591 5000000000 9120907036213 20000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(330864661/625000000 : ℝ), (-1690081447/10000000000 : ℝ), (2712549591/5000000000 : ℝ)] ![(44192733349049/100000000000000 : ℝ), (318835357627/3125000000000 : ℝ), (9120907036213/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(330864661/625000000 : ℝ)|^4631 ≤ (44192733349049/100000000000000 : ℝ)^3607
        have hw : |(330864661/625000000 : ℝ)|=(330864661/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1690081447/10000000000 : ℝ)|^4631 ≤ (318835357627/3125000000000 : ℝ)^3607
        have hw : |(-1690081447/10000000000 : ℝ)|=(1690081447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712549591/5000000000 : ℝ)|^4631 ≤ (9120907036213/20000000000000 : ℝ)^3607
        have hw : |(2712549591/5000000000 : ℝ)|=(2712549591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s5_6 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323458619/2500000000 : ℝ)*x 0 + (5425099051/10000000000 : ℝ)*x 1 + (-169008177/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323458619/2500000000 : ℝ)^4631 ≤ (44192732277261/100000000000000 : ℝ)^3607 := by
    have hnat : (1323458619 : ℕ)^4631*100000000000000^3607 ≤ 44192732277261^3607*2500000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323458619 2500000000 44192732277261 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425099051/10000000000 : ℝ)^4631 ≤ (1824181350689/4000000000000 : ℝ)^3607 := by
    have hnat : (5425099051 : ℕ)^4631*4000000000000^3607 ≤ 1824181350689^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425099051 10000000000 1824181350689 4000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169008177/1000000000 : ℝ)^4631 ≤ (15941771793/156250000000 : ℝ)^3607 := by
    have hnat : (169008177 : ℕ)^4631*156250000000^3607 ≤ 15941771793^3607*1000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169008177 1000000000 15941771793 156250000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323458619/2500000000 : ℝ), (5425099051/10000000000 : ℝ), (-169008177/1000000000 : ℝ)] ![(44192732277261/100000000000000 : ℝ), (1824181350689/4000000000000 : ℝ), (15941771793/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323458619/2500000000 : ℝ)|^4631 ≤ (44192732277261/100000000000000 : ℝ)^3607
        have hw : |(1323458619/2500000000 : ℝ)|=(1323458619/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425099051/10000000000 : ℝ)|^4631 ≤ (1824181350689/4000000000000 : ℝ)^3607
        have hw : |(5425099051/10000000000 : ℝ)|=(5425099051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-169008177/1000000000 : ℝ)|^4631 ≤ (15941771793/156250000000 : ℝ)^3607
        have hw : |(-169008177/1000000000 : ℝ)|=(169008177/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1567_s5_7 (p : ℝ) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265305693/625000000 : ℝ)*x 0 + (4490853849/10000000000 : ℝ)*x 1 + (802021037/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265305693/625000000 : ℝ)^4631 ≤ (16641431700561/50000000000000 : ℝ)^3607 := by
    have hnat : (265305693 : ℕ)^4631*50000000000000^3607 ≤ 16641431700561^3607*625000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265305693 625000000 16641431700561 50000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490853849/10000000000 : ℝ)^4631 ≤ (35778961742213/100000000000000 : ℝ)^3607 := by
    have hnat : (4490853849 : ℕ)^4631*100000000000000^3607 ≤ 35778961742213^3607*10000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490853849 10000000000 35778961742213 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (802021037/2000000000 : ℝ)^4631 ≤ (30938174833729/100000000000000 : ℝ)^3607 := by
    have hnat : (802021037 : ℕ)^4631*100000000000000^3607 ≤ 30938174833729^3607*2000000000^4631 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802021037 2000000000 30938174833729 100000000000000 4631 3607 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4631/1024 : ℝ)) 4631 3607 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265305693/625000000 : ℝ), (4490853849/10000000000 : ℝ), (802021037/2000000000 : ℝ)] ![(16641431700561/50000000000000 : ℝ), (35778961742213/100000000000000 : ℝ), (30938174833729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265305693/625000000 : ℝ)|^4631 ≤ (16641431700561/50000000000000 : ℝ)^3607
        have hw : |(265305693/625000000 : ℝ)|=(265305693/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490853849/10000000000 : ℝ)|^4631 ≤ (35778961742213/100000000000000 : ℝ)^3607
        have hw : |(4490853849/10000000000 : ℝ)|=(4490853849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(802021037/2000000000 : ℝ)|^4631 ≤ (30938174833729/100000000000000 : ℝ)^3607
        have hw : |(802021037/2000000000 : ℝ)|=(802021037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1567_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2777/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11111/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2777/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (484/3125 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2777/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2777/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (484/3125 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2777/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2777/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (484/3125 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2777/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2777/25000 : ℝ) ^ (4629/1024 : ℝ) ≤ (4850533398044269/100000000000000000000 : ℝ) := by
    have hpowers : (2777/25000 : ℝ)^4629 ≤ (4850533398044269/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2777 : ℕ)^4629*100000000000000000000^1024 ≤ 4850533398044269^1024*25000^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2777 25000 4850533398044269 100000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2777/25000 : ℝ)) (X := (4850533398044269/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (484/3125 : ℝ) ^ (4629/1024 : ℝ) ≤ (21795538630207341/100000000000000000000 : ℝ) := by
    have hpowers : (484/3125 : ℝ)^4629 ≤ (21795538630207341/100000000000000000000 : ℝ)^1024 := by
      have hnat : (484 : ℕ)^4629*100000000000000000000^1024 ≤ 21795538630207341^1024*3125^4629 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        484 3125 21795538630207341 100000000000000000000 4629 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (484/3125 : ℝ)) (X := (21795538630207341/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50004850533398044269/50000000000000000000 : ℝ) ≤ (125002682414443/125000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (50004850533398044269/50000000000000000000 : ℝ)^1024 ≤ (125002682414443/125000000000000 : ℝ)^4629 := by
      have hnat : (50004850533398044269 : ℕ)^1024*125000000000000^4629 ≤ 125002682414443^4629*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50004850533398044269 50000000000000000000 125002682414443 125000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125002682414443/125000000000000 : ℝ)) (X := (50004850533398044269/50000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002664607202825161/10000000000000000000 : ℝ) ≤ (10000589387494257/10000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (10002664607202825161/10000000000000000000 : ℝ)^1024 ≤ (10000589387494257/10000000000000000 : ℝ)^4629 := by
      have hnat : (10002664607202825161 : ℕ)^1024*10000000000000000^4629 ≤ 10000589387494257^4629*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002664607202825161 10000000000000000000 10000589387494257 10000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000589387494257/10000000000000000 : ℝ)) (X := (10002664607202825161/10000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50021795538630207341/50000000000000000000 : ℝ) ≤ (5000482090916537/5000000000000000 : ℝ) ^ (4629/1024 : ℝ) := by
    have hpowers : (50021795538630207341/50000000000000000000 : ℝ)^1024 ≤ (5000482090916537/5000000000000000 : ℝ)^4629 := by
      have hnat : (50021795538630207341 : ℕ)^1024*5000000000000000^4629 ≤ 5000482090916537^4629*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50021795538630207341 50000000000000000000 5000482090916537 5000000000000000 1024 4629 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000482090916537/5000000000000000 : ℝ)) (X := (50021795538630207341/50000000000000000000 : ℝ)) (by norm_num) 4629 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4850533398044269/100000000000000000000 : ℝ) ≤ ((5474076685873708591/5475000000000000000 : ℝ)+2*(374794338817/438000000000000 : ℝ)*(2777/25000 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (5474076685873708591/5475000000000000000 : ℝ)+2*(374794338817/438000000000000 : ℝ)*(2777/25000 : ℝ)=(125002682414443/125000000000000 : ℝ) by norm_num, show 1+2*(4850533398044269/100000000000000000000 : ℝ)=(50004850533398044269/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(21795538630207341/100000000000000000000 : ℝ)+(4850533398044269/100000000000000000000 : ℝ) ≤ ((5474076685873708591/5475000000000000000 : ℝ)+(374794338817/438000000000000 : ℝ)*((484/3125 : ℝ)+(2777/25000 : ℝ)))^(4629/1024 : ℝ) := by
    rw [show (5474076685873708591/5475000000000000000 : ℝ)+(374794338817/438000000000000 : ℝ)*((484/3125 : ℝ)+(2777/25000 : ℝ))=(10000589387494257/10000000000000000 : ℝ) by norm_num, show 1+(21795538630207341/100000000000000000000 : ℝ)+(4850533398044269/100000000000000000000 : ℝ)=(10002664607202825161/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(21795538630207341/100000000000000000000 : ℝ) ≤ ((5474076685873708591/5475000000000000000 : ℝ)+2*(374794338817/438000000000000 : ℝ)*(484/3125 : ℝ))^(4629/1024 : ℝ) := by
    rw [show (5474076685873708591/5475000000000000000 : ℝ)+2*(374794338817/438000000000000 : ℝ)*(484/3125 : ℝ)=(5000482090916537/5000000000000000 : ℝ) by norm_num, show 1+2*(21795538630207341/100000000000000000000 : ℝ)=(50021795538630207341/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5474076685873708591/5475000000000000000 : ℝ)*(X 1 0+X 2 0)+(374794338817/438000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (2777/25000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (5474076685873708591/5475000000000000000 : ℝ)) (alpha := (374794338817/438000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5474076685873708591/5475000000000000000 : ℝ)*(X 0 1+X 2 1)+(374794338817/438000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (2777/25000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (5474076685873708591/5475000000000000000 : ℝ)) (alpha := (374794338817/438000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5474076685873708591/5475000000000000000 : ℝ)*(X 0 2+X 1 2)+(374794338817/438000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4629/1024 : ℝ)) (lo := (2777/25000 : ℝ)) (hi := (484/3125 : ℝ)) (c := (5474076685873708591/5475000000000000000 : ℝ)) (alpha := (374794338817/438000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-89486017/500000000 : ℝ)*X 0 0+(2713090221/5000000000 : ℝ)*X 0 1+(1304987581/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348377167/10000000000 : ℝ)*X 1 0+(-947615343/5000000000 : ℝ)*X 1 1+(5219950113/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348377037/10000000000 : ℝ)*X 2 0+(163123441/312500000 : ℝ)*X 2 1+(-1895230863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4244828031/10000000000 : ℝ)*X 0 0+(4007557111/10000000000 : ℝ)*X 0 1+(4493382953/10000000000 : ℝ)*X 0 2+(4244828031/10000000000 : ℝ)*X 1 0+(4007557111/10000000000 : ℝ)*X 1 1+(4493382953/10000000000 : ℝ)*X 1 2+(4244828031/10000000000 : ℝ)*X 2 0+(4007557111/10000000000 : ℝ)*X 2 1+(4493382953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1789747143/10000000000 : ℝ)*X 0 0+(5221024051/10000000000 : ℝ)*X 0 1+(5425098837/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((330864661/625000000 : ℝ)*X 1 0+(-1690081447/10000000000 : ℝ)*X 1 1+(2712549591/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1323458619/2500000000 : ℝ)*X 2 0+(5425099051/10000000000 : ℝ)*X 2 1+(-169008177/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((265305693/625000000 : ℝ)*X 0 0+(4490853849/10000000000 : ℝ)*X 0 1+(802021037/2000000000 : ℝ)*X 0 2+(265305693/625000000 : ℝ)*X 1 0+(4490853849/10000000000 : ℝ)*X 1 1+(802021037/2000000000 : ℝ)*X 1 2+(265305693/625000000 : ℝ)*X 2 0+(4490853849/10000000000 : ℝ)*X 2 1+(802021037/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1567_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48355851077326704810296887/4562500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (417959973/20000000000000 : ℝ)*(base19) + (1824120689/100000000000000 : ℝ)*(base23) + (4941137/6250000000000 : ℝ)*(lower2) + (216260967/50000000000000 : ℝ)*(upper3) + (130933059/100000000000000 : ℝ)*(upper5) + (345369327518007/10000000000000 : ℝ)*(major0) + (345369327518007/10000000000000 : ℝ)*(major1) + (431711659397509/12500000000000 : ℝ)*(major2) + (4848983104289437/100000000000000 : ℝ)*(sp0) + (1212250909266679/25000000000000 : ℝ)*(sp1) + (1212250975686473/25000000000000 : ℝ)*(sp2) + (257295479372601/12500000000000 : ℝ)*(sp3) + (22622577143/100000000000000 : ℝ)*(sp4) + (8317613993/50000000000000 : ℝ)*(sp7) + (1029190235104397/50000000000000 : ℝ)*(f.failure) + (4849005726866581/100000000000000 : ℝ)*(f.sum) + (36966747519293/21900000000000000000000000000 : ℝ)*base66 + (814555979891121863/54750000000000000000000000000000 : ℝ)*base68 + (80492629082860847/34218750000000000000000000000000 : ℝ)*base69 + (324471765001371863/54750000000000000000000000000000 : ℝ)*base72 + (20311355993393/21900000000000000000000000000 : ℝ)*base74 + (66056991190732903/34218750000000000000000000000000 : ℝ)*base76 + (314855337500138121/18250000000000000000000000000000 : ℝ)*base78 + (408532293419638121/18250000000000000000000000000000 : ℝ)*base80 + (2677410113167/730000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (22876207/1250000000000000000000 : ℝ)*base89 + (22876207/1250000000000000000000 : ℝ)*base91 + (2123793/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (384947809060677588297944241/45625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (839349743/50000000000000 : ℝ)*(base19) + (1693867853/100000000000000 : ℝ)*(base23) + (583017279/100000000000000 : ℝ)*(lower1) + (354025369/100000000000000 : ℝ)*(upper3) + (48843941/100000000000000 : ℝ)*(lower4) + (11369723/50000000000000 : ℝ)*(upper5) + (1745051013782849/50000000000000 : ℝ)*(major0) + (1745051013782849/50000000000000 : ℝ)*(major1) + (1745051013782849/50000000000000 : ℝ)*(major2) + (1501059453/100000000000000 : ℝ)*(sp2) + (980024781141811/20000000000000 : ℝ)*(sp4) + (4900122227009569/100000000000000 : ℝ)*(sp5) + (4900120710781749/100000000000000 : ℝ)*(sp6) + (13000499176137/625000000000 : ℝ)*(sp7) + (13000499176137/625000000000 : ℝ)*(f.failure) + (980024781141811/20000000000000 : ℝ)*(f.sum) + (47183008040617/10950000000000000000000000000 : ℝ)*base66 + (1313276121810472753/91250000000000000000000000000000 : ℝ)*base67 + (752042830127027247/91250000000000000000000000000000 : ℝ)*base70 + (422161530423277247/91250000000000000000000000000000 : ℝ)*base72 + (34159019370517/10950000000000000000000000000 : ℝ)*base74 + (6625774848399222753/91250000000000000000000000000000 : ℝ)*base75 + (498578203960472753/91250000000000000000000000000000 : ℝ)*base77 + (454563696197972753/91250000000000000000000000000000 : ℝ)*base79 + (53346680214817/10950000000000000000000000000 : ℝ)*base82 + (45647/15625000000000000000 : ℝ)*base89 + (45647/15625000000000000000 : ℝ)*base91 + (45647/15625000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1567_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (484/3125 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2777/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11111/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1567_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1567_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (791/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10803/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11111/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1567_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1567_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1567_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4629/1024 : ℝ) ≤ p) (hpb : p ≤ (4631/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (41946731/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (791/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10803/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11111/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1567_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
