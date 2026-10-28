-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1293_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:26:56.666574+00:00
-- url     : https://prove2.me/submissions/1c1a0dd2-416a-462f-8e2f-eefd0c7efb5f

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
theorem support_rectangle_w1293_s0_0 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-73538859/400000000 : ℝ)*x 0 + (3009175171/5000000000 : ℝ)*x 1 + (4799084131/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (73538859/400000000 : ℝ)^4253 ≤ (10744767444499/100000000000000 : ℝ)^3229 := by
    have hnat : (73538859 : ℕ)^4253*100000000000000^3229 ≤ 10744767444499^3229*400000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      73538859 400000000 10744767444499 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3009175171/5000000000 : ℝ)^4253 ≤ (51232320385901/100000000000000 : ℝ)^3229 := by
    have hnat : (3009175171 : ℕ)^4253*100000000000000^3229 ≤ 51232320385901^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3009175171 5000000000 51232320385901 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4799084131/10000000000 : ℝ)^4253 ≤ (38022912156783/100000000000000 : ℝ)^3229 := by
    have hnat : (4799084131 : ℕ)^4253*100000000000000^3229 ≤ 38022912156783^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4799084131 10000000000 38022912156783 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-73538859/400000000 : ℝ), (3009175171/5000000000 : ℝ), (4799084131/10000000000 : ℝ)] ![(10744767444499/100000000000000 : ℝ), (51232320385901/100000000000000 : ℝ), (38022912156783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-73538859/400000000 : ℝ)|^4253 ≤ (10744767444499/100000000000000 : ℝ)^3229
        have hw : |(-73538859/400000000 : ℝ)|=(73538859/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3009175171/5000000000 : ℝ)|^4253 ≤ (51232320385901/100000000000000 : ℝ)^3229
        have hw : |(3009175171/5000000000 : ℝ)|=(3009175171/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4799084131/10000000000 : ℝ)|^4253 ≤ (38022912156783/100000000000000 : ℝ)^3229
        have hw : |(4799084131/10000000000 : ℝ)|=(4799084131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s0_1 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5507306569/10000000000 : ℝ)*x 0 + (-633500777/2500000000 : ℝ)*x 1 + (4799084147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5507306569/10000000000 : ℝ)^4253 ≤ (9116210354743/20000000000000 : ℝ)^3229 := by
    have hnat : (5507306569 : ℕ)^4253*20000000000000^3229 ≤ 9116210354743^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507306569 10000000000 9116210354743 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (633500777/2500000000 : ℝ)^4253 ≤ (16396035892607/100000000000000 : ℝ)^3229 := by
    have hnat : (633500777 : ℕ)^4253*100000000000000^3229 ≤ 16396035892607^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      633500777 2500000000 16396035892607 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4799084147/10000000000 : ℝ)^4253 ≤ (38022912323751/100000000000000 : ℝ)^3229 := by
    have hnat : (4799084147 : ℕ)^4253*100000000000000^3229 ≤ 38022912323751^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4799084147 10000000000 38022912323751 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5507306569/10000000000 : ℝ), (-633500777/2500000000 : ℝ), (4799084147/10000000000 : ℝ)] ![(9116210354743/20000000000000 : ℝ), (16396035892607/100000000000000 : ℝ), (38022912323751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5507306569/10000000000 : ℝ)|^4253 ≤ (9116210354743/20000000000000 : ℝ)^3229
        have hw : |(5507306569/10000000000 : ℝ)|=(5507306569/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-633500777/2500000000 : ℝ)|^4253 ≤ (16396035892607/100000000000000 : ℝ)^3229
        have hw : |(-633500777/2500000000 : ℝ)|=(633500777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4799084147/10000000000 : ℝ)|^4253 ≤ (38022912323751/100000000000000 : ℝ)^3229
        have hw : |(4799084147/10000000000 : ℝ)|=(4799084147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s0_2 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5507306243/10000000000 : ℝ)*x 0 + (4799084587/10000000000 : ℝ)*x 1 + (-506800597/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5507306243/10000000000 : ℝ)^4253 ≤ (45581048219939/100000000000000 : ℝ)^3229 := by
    have hnat : (5507306243 : ℕ)^4253*100000000000000^3229 ≤ 45581048219939^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5507306243 10000000000 45581048219939 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4799084587/10000000000 : ℝ)^4253 ≤ (38022916915383/100000000000000 : ℝ)^3229 := by
    have hnat : (4799084587 : ℕ)^4253*100000000000000^3229 ≤ 38022916915383^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4799084587 10000000000 38022916915383 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (506800597/2000000000 : ℝ)^4253 ≤ (8198017422179/50000000000000 : ℝ)^3229 := by
    have hnat : (506800597 : ℕ)^4253*50000000000000^3229 ≤ 8198017422179^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      506800597 2000000000 8198017422179 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5507306243/10000000000 : ℝ), (4799084587/10000000000 : ℝ), (-506800597/2000000000 : ℝ)] ![(45581048219939/100000000000000 : ℝ), (38022916915383/100000000000000 : ℝ), (8198017422179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5507306243/10000000000 : ℝ)|^4253 ≤ (45581048219939/100000000000000 : ℝ)^3229
        have hw : |(5507306243/10000000000 : ℝ)|=(5507306243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4799084587/10000000000 : ℝ)|^4253 ≤ (38022916915383/100000000000000 : ℝ)^3229
        have hw : |(4799084587/10000000000 : ℝ)|=(4799084587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-506800597/2000000000 : ℝ)|^4253 ≤ (8198017422179/50000000000000 : ℝ)^3229
        have hw : |(-506800597/2000000000 : ℝ)|=(506800597/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s0_3 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4186178279/10000000000 : ℝ)*x 0 + (3109368557/10000000000 : ℝ)*x 1 + (1123241193/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4186178279/10000000000 : ℝ)^4253 ≤ (15880211176323/50000000000000 : ℝ)^3229 := by
    have hnat : (4186178279 : ℕ)^4253*50000000000000^3229 ≤ 15880211176323^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4186178279 10000000000 15880211176323 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3109368557/10000000000 : ℝ)^4253 ≤ (21467691441149/100000000000000 : ℝ)^3229 := by
    have hnat : (3109368557 : ℕ)^4253*100000000000000^3229 ≤ 21467691441149^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3109368557 10000000000 21467691441149 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1123241193/2000000000 : ℝ)^4253 ≤ (46771886197791/100000000000000 : ℝ)^3229 := by
    have hnat : (1123241193 : ℕ)^4253*100000000000000^3229 ≤ 46771886197791^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1123241193 2000000000 46771886197791 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4186178279/10000000000 : ℝ), (3109368557/10000000000 : ℝ), (1123241193/2000000000 : ℝ)] ![(15880211176323/50000000000000 : ℝ), (21467691441149/100000000000000 : ℝ), (46771886197791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4186178279/10000000000 : ℝ)|^4253 ≤ (15880211176323/50000000000000 : ℝ)^3229
        have hw : |(4186178279/10000000000 : ℝ)|=(4186178279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3109368557/10000000000 : ℝ)|^4253 ≤ (21467691441149/100000000000000 : ℝ)^3229
        have hw : |(3109368557/10000000000 : ℝ)|=(3109368557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1123241193/2000000000 : ℝ)|^4253 ≤ (46771886197791/100000000000000 : ℝ)^3229
        have hw : |(1123241193/2000000000 : ℝ)|=(1123241193/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s0_4 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-230398699/1250000000 : ℝ)*x 0 + (4830551667/10000000000 : ℝ)*x 1 + (2992881907/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (230398699/1250000000 : ℝ)^4253 ≤ (5390550703111/50000000000000 : ℝ)^3229 := by
    have hnat : (230398699 : ℕ)^4253*50000000000000^3229 ≤ 5390550703111^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230398699 1250000000 5390550703111 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4830551667/10000000000 : ℝ)^4253 ≤ (38351633358841/100000000000000 : ℝ)^3229 := by
    have hnat : (4830551667 : ℕ)^4253*100000000000000^3229 ≤ 38351633358841^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4830551667 10000000000 38351633358841 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2992881907/5000000000 : ℝ)^4253 ≤ (50867265213307/100000000000000 : ℝ)^3229 := by
    have hnat : (2992881907 : ℕ)^4253*100000000000000^3229 ≤ 50867265213307^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2992881907 5000000000 50867265213307 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-230398699/1250000000 : ℝ), (4830551667/10000000000 : ℝ), (2992881907/5000000000 : ℝ)] ![(5390550703111/50000000000000 : ℝ), (38351633358841/100000000000000 : ℝ), (50867265213307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-230398699/1250000000 : ℝ)|^4253 ≤ (5390550703111/50000000000000 : ℝ)^3229
        have hw : |(-230398699/1250000000 : ℝ)|=(230398699/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4830551667/10000000000 : ℝ)|^4253 ≤ (38351633358841/100000000000000 : ℝ)^3229
        have hw : |(4830551667/10000000000 : ℝ)|=(4830551667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2992881907/5000000000 : ℝ)|^4253 ≤ (50867265213307/100000000000000 : ℝ)^3229
        have hw : |(2992881907/5000000000 : ℝ)|=(2992881907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s0_5 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1293840529/2500000000 : ℝ)*x 0 + (-26946423/200000000 : ℝ)*x 1 + (119715329/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1293840529/2500000000 : ℝ)^4253 ≤ (2624846546033/6250000000000 : ℝ)^3229 := by
    have hnat : (1293840529 : ℕ)^4253*6250000000000^3229 ≤ 2624846546033^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293840529 2500000000 2624846546033 6250000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26946423/200000000 : ℝ)^4253 ≤ (7135160532617/100000000000000 : ℝ)^3229 := by
    have hnat : (26946423 : ℕ)^4253*100000000000000^3229 ≤ 7135160532617^3229*200000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26946423 200000000 7135160532617 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (119715329/200000000 : ℝ)^4253 ≤ (50867294718033/100000000000000 : ℝ)^3229 := by
    have hnat : (119715329 : ℕ)^4253*100000000000000^3229 ≤ 50867294718033^3229*200000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      119715329 200000000 50867294718033 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1293840529/2500000000 : ℝ), (-26946423/200000000 : ℝ), (119715329/200000000 : ℝ)] ![(2624846546033/6250000000000 : ℝ), (7135160532617/100000000000000 : ℝ), (50867294718033/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1293840529/2500000000 : ℝ)|^4253 ≤ (2624846546033/6250000000000 : ℝ)^3229
        have hw : |(1293840529/2500000000 : ℝ)|=(1293840529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26946423/200000000 : ℝ)|^4253 ≤ (7135160532617/100000000000000 : ℝ)^3229
        have hw : |(-26946423/200000000 : ℝ)|=(26946423/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(119715329/200000000 : ℝ)|^4253 ≤ (50867294718033/100000000000000 : ℝ)^3229
        have hw : |(119715329/200000000 : ℝ)|=(119715329/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s0_6 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2587681707/5000000000 : ℝ)*x 0 + (2992882101/5000000000 : ℝ)*x 1 + (-1347322769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587681707/5000000000 : ℝ)^4253 ≤ (20998779305001/50000000000000 : ℝ)^3229 := by
    have hnat : (2587681707 : ℕ)^4253*50000000000000^3229 ≤ 20998779305001^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587681707 5000000000 20998779305001 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2992882101/5000000000 : ℝ)^4253 ≤ (12716817389047/25000000000000 : ℝ)^3229 := by
    have hnat : (2992882101 : ℕ)^4253*25000000000000^3229 ≤ 12716817389047^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2992882101 5000000000 12716817389047 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1347322769/10000000000 : ℝ)^4253 ≤ (3567585912777/50000000000000 : ℝ)^3229 := by
    have hnat : (1347322769 : ℕ)^4253*50000000000000^3229 ≤ 3567585912777^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1347322769 10000000000 3567585912777 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587681707/5000000000 : ℝ), (2992882101/5000000000 : ℝ), (-1347322769/10000000000 : ℝ)] ![(20998779305001/50000000000000 : ℝ), (12716817389047/25000000000000 : ℝ), (3567585912777/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587681707/5000000000 : ℝ)|^4253 ≤ (20998779305001/50000000000000 : ℝ)^3229
        have hw : |(2587681707/5000000000 : ℝ)|=(2587681707/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2992882101/5000000000 : ℝ)|^4253 ≤ (12716817389047/25000000000000 : ℝ)^3229
        have hw : |(2992882101/5000000000 : ℝ)|=(2992882101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1347322769/10000000000 : ℝ)|^4253 ≤ (3567585912777/50000000000000 : ℝ)^3229
        have hw : |(-1347322769/10000000000 : ℝ)|=(1347322769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s0_7 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4195883453/10000000000 : ℝ)*x 0 + (1387879083/2500000000 : ℝ)*x 1 + (158817969/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4195883453/10000000000 : ℝ)^4253 ≤ (31857441789739/100000000000000 : ℝ)^3229 := by
    have hnat : (4195883453 : ℕ)^4253*100000000000000^3229 ≤ 31857441789739^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195883453 10000000000 31857441789739 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1387879083/2500000000 : ℝ)^4253 ≤ (23031800738841/50000000000000 : ℝ)^3229 := by
    have hnat : (1387879083 : ℕ)^4253*50000000000000^3229 ≤ 23031800738841^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1387879083 2500000000 23031800738841 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (158817969/500000000 : ℝ)^4253 ≤ (11039478355239/50000000000000 : ℝ)^3229 := by
    have hnat : (158817969 : ℕ)^4253*50000000000000^3229 ≤ 11039478355239^3229*500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      158817969 500000000 11039478355239 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4195883453/10000000000 : ℝ), (1387879083/2500000000 : ℝ), (158817969/500000000 : ℝ)] ![(31857441789739/100000000000000 : ℝ), (23031800738841/50000000000000 : ℝ), (11039478355239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4195883453/10000000000 : ℝ)|^4253 ≤ (31857441789739/100000000000000 : ℝ)^3229
        have hw : |(4195883453/10000000000 : ℝ)|=(4195883453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1387879083/2500000000 : ℝ)|^4253 ≤ (23031800738841/50000000000000 : ℝ)^3229
        have hw : |(1387879083/2500000000 : ℝ)|=(1387879083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(158817969/500000000 : ℝ)|^4253 ≤ (11039478355239/50000000000000 : ℝ)^3229
        have hw : |(158817969/500000000 : ℝ)|=(158817969/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1293_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (13/1250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (6807/25000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1063/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1063 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1063*1^256 ≤ 0^256*1^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1063/256 : ℝ) ≤ (222646715163667871/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1063 ≤ (222646715163667871/10000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1063*10000000000000000000^256 ≤ 222646715163667871^256*5^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 222646715163667871 10000000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (222646715163667871/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1063 := by
      have hnat : (1 : ℕ)^256*1^1063 ≤ 1^1063*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (10222646715163667871/10000000000000000000 : ℝ) ≤ (1005317219783413/1000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (10222646715163667871/10000000000000000000 : ℝ)^256 ≤ (1005317219783413/1000000000000000 : ℝ)^1063 := by
      have hnat : (10222646715163667871 : ℕ)^256*1000000000000000^1063 ≤ 1005317219783413^1063*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10222646715163667871 10000000000000000000 1005317219783413 1000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1005317219783413/1000000000000000 : ℝ)) (X := (10222646715163667871/10000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5222646715163667871/5000000000000000000 : ℝ) ≤ (505317219783413/500000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (5222646715163667871/5000000000000000000 : ℝ)^256 ≤ (505317219783413/500000000000000 : ℝ)^1063 := by
      have hnat : (5222646715163667871 : ℕ)^256*500000000000000^1063 ≤ 505317219783413^1063*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5222646715163667871 5000000000000000000 505317219783413 500000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (505317219783413/500000000000000 : ℝ)) (X := (5222646715163667871/5000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(5317219783413/400000000000000 : ℝ)*(0 : ℝ))^(1063/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(5317219783413/400000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(222646715163667871/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(5317219783413/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1063/256 : ℝ) := by
    rw [show (1 : ℝ)+(5317219783413/400000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(1005317219783413/1000000000000000 : ℝ) by norm_num, show 1+(222646715163667871/10000000000000000000 : ℝ)+(0 : ℝ)=(10222646715163667871/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(222646715163667871/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(5317219783413/400000000000000 : ℝ)*(2/5 : ℝ))^(1063/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(5317219783413/400000000000000 : ℝ)*(2/5 : ℝ)=(505317219783413/500000000000000 : ℝ) by norm_num, show 1+2*(222646715163667871/10000000000000000000 : ℝ)=(5222646715163667871/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(5317219783413/400000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5317219783413/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(5317219783413/400000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5317219783413/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(5317219783413/400000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (5317219783413/400000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-73538859/400000000 : ℝ)*X 0 0+(3009175171/5000000000 : ℝ)*X 0 1+(4799084131/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5507306569/10000000000 : ℝ)*X 1 0+(-633500777/2500000000 : ℝ)*X 1 1+(4799084147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5507306243/10000000000 : ℝ)*X 2 0+(4799084587/10000000000 : ℝ)*X 2 1+(-506800597/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4186178279/10000000000 : ℝ)*X 0 0+(3109368557/10000000000 : ℝ)*X 0 1+(1123241193/2000000000 : ℝ)*X 0 2+(4186178279/10000000000 : ℝ)*X 1 0+(3109368557/10000000000 : ℝ)*X 1 1+(1123241193/2000000000 : ℝ)*X 1 2+(4186178279/10000000000 : ℝ)*X 2 0+(3109368557/10000000000 : ℝ)*X 2 1+(1123241193/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-230398699/1250000000 : ℝ)*X 0 0+(4830551667/10000000000 : ℝ)*X 0 1+(2992881907/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1293840529/2500000000 : ℝ)*X 1 0+(-26946423/200000000 : ℝ)*X 1 1+(119715329/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2587681707/5000000000 : ℝ)*X 2 0+(2992882101/5000000000 : ℝ)*X 2 1+(-1347322769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4195883453/10000000000 : ℝ)*X 0 0+(1387879083/2500000000 : ℝ)*X 0 1+(158817969/500000000 : ℝ)*X 0 2+(4195883453/10000000000 : ℝ)*X 1 0+(1387879083/2500000000 : ℝ)*X 1 1+(158817969/500000000 : ℝ)*X 1 2+(4195883453/10000000000 : ℝ)*X 2 0+(1387879083/2500000000 : ℝ)*X 2 1+(158817969/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9996276209958200157/1953125000000000000000000 : ℝ) := by norm_num
    linear_combination (28478959/25000000000000 : ℝ)*(base1) + (83065589/6250000000000 : ℝ)*(base19) + (640250039/50000000000000 : ℝ)*(base23) + (139348233/100000000000000 : ℝ)*(upper3) + (7686009/5000000000000 : ℝ)*(upper5) + (19048225214507/3125000000000 : ℝ)*(major0) + (19048225214507/3125000000000 : ℝ)*(major1) + (19048225214507/3125000000000 : ℝ)*(major2) + (164033876878029/20000000000000 : ℝ)*(sp0) + (205043035602351/25000000000000 : ℝ)*(sp1) + (820172190958751/100000000000000 : ℝ)*(sp2) + (9972770319627/2500000000000 : ℝ)*(sp3) + (105024613/2500000000000 : ℝ)*(sp4) + (922482793/50000000000000 : ℝ)*(sp7) + (199456385833251/50000000000000 : ℝ)*(f.failure) + (205043367864707/25000000000000 : ℝ)*(f.sum) + (237717745873/78125000000000000000000000 : ℝ)*base66 + (490312605109/1250000000000000000000000000 : ℝ)*base68 + (43678371359/1250000000000000000000000000 : ℝ)*base70 + (1481379754891/1250000000000000000000000000 : ℝ)*base71 + (1833527227609/625000000000000000000000000 : ℝ)*base74 + (228266012609/1250000000000000000000000000 : ℝ)*base76 + (2770129766359/1250000000000000000000000000 : ℝ)*base78 + (10399683113859/1250000000000000000000000000 : ℝ)*base80 + (516193196617/312500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (520313/2500000000000000000000 : ℝ)*base89 + (520313/2500000000000000000000 : ℝ)*base91 + (520313/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (109704818901220840880127/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (442468667/100000000000000 : ℝ)*(base1) + (960403091/100000000000000 : ℝ)*(base19) + (569993191/50000000000000 : ℝ)*(base23) + (83011959/50000000000000 : ℝ)*(upper3) + (643333726576193/100000000000000 : ℝ)*(major0) + (643333726576193/100000000000000 : ℝ)*(major1) + (643333726576193/100000000000000 : ℝ)*(major2) + (1540731167/100000000000000 : ℝ)*(sp1) + (955724541/100000000000000 : ℝ)*(sp2) + (520314071/100000000000000 : ℝ)*(sp3) + (432820444801439/50000000000000 : ℝ)*(sp4) + (865637945999953/100000000000000 : ℝ)*(sp5) + (108204793927911/12500000000000 : ℝ)*(sp6) + (421025860394071/100000000000000 : ℝ)*(sp7) + (421026823176809/100000000000000 : ℝ)*(f.failure) + (865640447134211/100000000000000 : ℝ)*(f.sum) + (1032998166709/20000000000000000000000000000 : ℝ)*base65 + (41688272286709/40000000000000000000000000000 : ℝ)*base67 + (18964454606709/40000000000000000000000000000 : ℝ)*base69 + (126202000366709/40000000000000000000000000000 : ℝ)*base71 + (34857700573291/20000000000000000000000000000 : ℝ)*base74 + (90828733673291/40000000000000000000000000000 : ℝ)*base76 + (1969124593291/40000000000000000000000000000 : ℝ)*base78 + (34287252393291/40000000000000000000000000000 : ℝ)*base80 + (15491900673291/20000000000000000000000000000 : ℝ)*base82 + (6143467/5000000000000000000000 : ℝ)*base89 + (6143467/5000000000000000000000 : ℝ)*base91 + (6143467/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1293_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (13/1250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (6807/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1293_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1293_s1_0 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2030371021/10000000000 : ℝ)*x 0 + (226593441/400000000 : ℝ)*x 1 + (1005948297/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2030371021/10000000000 : ℝ)^4253 ≤ (12245866854493/100000000000000 : ℝ)^3229 := by
    have hnat : (2030371021 : ℕ)^4253*100000000000000^3229 ≤ 12245866854493^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030371021 10000000000 12245866854493 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (226593441/400000000 : ℝ)^4253 ≤ (47306042921627/100000000000000 : ℝ)^3229 := by
    have hnat : (226593441 : ℕ)^4253*100000000000000^3229 ≤ 47306042921627^3229*400000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      226593441 400000000 47306042921627 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1005948297/2000000000 : ℝ)^4253 ≤ (40448090208981/100000000000000 : ℝ)^3229 := by
    have hnat : (1005948297 : ℕ)^4253*100000000000000^3229 ≤ 40448090208981^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005948297 2000000000 40448090208981 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2030371021/10000000000 : ℝ), (226593441/400000000 : ℝ), (1005948297/2000000000 : ℝ)] ![(12245866854493/100000000000000 : ℝ), (47306042921627/100000000000000 : ℝ), (40448090208981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2030371021/10000000000 : ℝ)|^4253 ≤ (12245866854493/100000000000000 : ℝ)^3229
        have hw : |(-2030371021/10000000000 : ℝ)|=(2030371021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(226593441/400000000 : ℝ)|^4253 ≤ (47306042921627/100000000000000 : ℝ)^3229
        have hw : |(226593441/400000000 : ℝ)|=(226593441/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1005948297/2000000000 : ℝ)|^4253 ≤ (40448090208981/100000000000000 : ℝ)^3229
        have hw : |(1005948297/2000000000 : ℝ)|=(1005948297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s1_1 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5410879859/10000000000 : ℝ)*x 0 + (-2370741201/10000000000 : ℝ)*x 1 + (5029741481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5410879859/10000000000 : ℝ)^4253 ≤ (44532819489647/100000000000000 : ℝ)^3229 := by
    have hnat : (5410879859 : ℕ)^4253*100000000000000^3229 ≤ 44532819489647^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410879859 10000000000 44532819489647 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2370741201/10000000000 : ℝ)^4253 ≤ (1501909032661/10000000000000 : ℝ)^3229 := by
    have hnat : (2370741201 : ℕ)^4253*10000000000000^3229 ≤ 1501909032661^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370741201 10000000000 1501909032661 10000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5029741481/10000000000 : ℝ)^4253 ≤ (40448090166613/100000000000000 : ℝ)^3229 := by
    have hnat : (5029741481 : ℕ)^4253*100000000000000^3229 ≤ 40448090166613^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5029741481 10000000000 40448090166613 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5410879859/10000000000 : ℝ), (-2370741201/10000000000 : ℝ), (5029741481/10000000000 : ℝ)] ![(44532819489647/100000000000000 : ℝ), (1501909032661/10000000000000 : ℝ), (40448090166613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5410879859/10000000000 : ℝ)|^4253 ≤ (44532819489647/100000000000000 : ℝ)^3229
        have hw : |(5410879859/10000000000 : ℝ)|=(5410879859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2370741201/10000000000 : ℝ)|^4253 ≤ (1501909032661/10000000000000 : ℝ)^3229
        have hw : |(-2370741201/10000000000 : ℝ)|=(2370741201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5029741481/10000000000 : ℝ)|^4253 ≤ (40448090166613/100000000000000 : ℝ)^3229
        have hw : |(5029741481/10000000000 : ℝ)|=(5029741481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s1_2 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (21643519/40000000 : ℝ)*x 0 + (5029741479/10000000000 : ℝ)*x 1 + (-474148269/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21643519/40000000 : ℝ)^4253 ≤ (44532818308059/100000000000000 : ℝ)^3229 := by
    have hnat : (21643519 : ℕ)^4253*100000000000000^3229 ≤ 44532818308059^3229*40000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21643519 40000000 44532818308059 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5029741479/10000000000 : ℝ)^4253 ≤ (40448090145429/100000000000000 : ℝ)^3229 := by
    have hnat : (5029741479 : ℕ)^4253*100000000000000^3229 ≤ 40448090145429^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5029741479 10000000000 40448090145429 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (474148269/2000000000 : ℝ)^4253 ≤ (15019091528181/100000000000000 : ℝ)^3229 := by
    have hnat : (474148269 : ℕ)^4253*100000000000000^3229 ≤ 15019091528181^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474148269 2000000000 15019091528181 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(21643519/40000000 : ℝ), (5029741479/10000000000 : ℝ), (-474148269/2000000000 : ℝ)] ![(44532818308059/100000000000000 : ℝ), (40448090145429/100000000000000 : ℝ), (15019091528181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(21643519/40000000 : ℝ)|^4253 ≤ (44532818308059/100000000000000 : ℝ)^3229
        have hw : |(21643519/40000000 : ℝ)|=(21643519/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5029741479/10000000000 : ℝ)|^4253 ≤ (40448090145429/100000000000000 : ℝ)^3229
        have hw : |(5029741479/10000000000 : ℝ)|=(5029741479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-474148269/2000000000 : ℝ)|^4253 ≤ (15019091528181/100000000000000 : ℝ)^3229
        have hw : |(-474148269/2000000000 : ℝ)|=(474148269/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s1_3 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (215048247/500000000 : ℝ)*x 0 + (230937839/625000000 : ℝ)*x 1 + (1000154729/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215048247/500000000 : ℝ)^4253 ≤ (16456220975327/50000000000000 : ℝ)^3229 := by
    have hnat : (215048247 : ℕ)^4253*50000000000000^3229 ≤ 16456220975327^3229*500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215048247 500000000 16456220975327 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (230937839/625000000 : ℝ)^4253 ≤ (26946015833067/100000000000000 : ℝ)^3229 := by
    have hnat : (230937839 : ℕ)^4253*100000000000000^3229 ≤ 26946015833067^3229*625000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230937839 625000000 26946015833067 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000154729/2000000000 : ℝ)^4253 ≤ (401415421991/1000000000000 : ℝ)^3229 := by
    have hnat : (1000154729 : ℕ)^4253*1000000000000^3229 ≤ 401415421991^3229*2000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000154729 2000000000 401415421991 1000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215048247/500000000 : ℝ), (230937839/625000000 : ℝ), (1000154729/2000000000 : ℝ)] ![(16456220975327/50000000000000 : ℝ), (26946015833067/100000000000000 : ℝ), (401415421991/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215048247/500000000 : ℝ)|^4253 ≤ (16456220975327/50000000000000 : ℝ)^3229
        have hw : |(215048247/500000000 : ℝ)|=(215048247/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(230937839/625000000 : ℝ)|^4253 ≤ (26946015833067/100000000000000 : ℝ)^3229
        have hw : |(230937839/625000000 : ℝ)|=(230937839/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1000154729/2000000000 : ℝ)|^4253 ≤ (401415421991/1000000000000 : ℝ)^3229
        have hw : |(1000154729/2000000000 : ℝ)|=(1000154729/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s1_4 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2031005923/10000000000 : ℝ)*x 0 + (5038015451/10000000000 : ℝ)*x 1 + (565640561/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2031005923/10000000000 : ℝ)^4253 ≤ (12250910791933/100000000000000 : ℝ)^3229 := by
    have hnat : (2031005923 : ℕ)^4253*100000000000000^3229 ≤ 12250910791933^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031005923 10000000000 12250910791933 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5038015451/10000000000 : ℝ)^4253 ≤ (40535751255189/100000000000000 : ℝ)^3229 := by
    have hnat : (5038015451 : ℕ)^4253*100000000000000^3229 ≤ 40535751255189^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5038015451 10000000000 40535751255189 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (565640561/1000000000 : ℝ)^4253 ≤ (47213337946651/100000000000000 : ℝ)^3229 := by
    have hnat : (565640561 : ℕ)^4253*100000000000000^3229 ≤ 47213337946651^3229*1000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      565640561 1000000000 47213337946651 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2031005923/10000000000 : ℝ), (5038015451/10000000000 : ℝ), (565640561/1000000000 : ℝ)] ![(12250910791933/100000000000000 : ℝ), (40535751255189/100000000000000 : ℝ), (47213337946651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2031005923/10000000000 : ℝ)|^4253 ≤ (12250910791933/100000000000000 : ℝ)^3229
        have hw : |(-2031005923/10000000000 : ℝ)|=(2031005923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5038015451/10000000000 : ℝ)|^4253 ≤ (40535751255189/100000000000000 : ℝ)^3229
        have hw : |(5038015451/10000000000 : ℝ)|=(5038015451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(565640561/1000000000 : ℝ)|^4253 ≤ (47213337946651/100000000000000 : ℝ)^3229
        have hw : |(565640561/1000000000 : ℝ)|=(565640561/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s1_5 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2623389323/5000000000 : ℝ)*x 0 + (-1744076709/10000000000 : ℝ)*x 1 + (1414101569/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2623389323/5000000000 : ℝ)^4253 ≤ (42762534292623/100000000000000 : ℝ)^3229 := by
    have hnat : (2623389323 : ℕ)^4253*100000000000000^3229 ≤ 42762534292623^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623389323 5000000000 42762534292623 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1744076709/10000000000 : ℝ)^4253 ≤ (5012060207659/50000000000000 : ℝ)^3229 := by
    have hnat : (1744076709 : ℕ)^4253*50000000000000^3229 ≤ 5012060207659^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1744076709 10000000000 5012060207659 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414101569/2500000000 : ℝ)^4253 ≤ (5901668158573/12500000000000 : ℝ)^3229 := by
    have hnat : (1414101569 : ℕ)^4253*12500000000000^3229 ≤ 5901668158573^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414101569 2500000000 5901668158573 12500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2623389323/5000000000 : ℝ), (-1744076709/10000000000 : ℝ), (1414101569/2500000000 : ℝ)] ![(42762534292623/100000000000000 : ℝ), (5012060207659/50000000000000 : ℝ), (5901668158573/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2623389323/5000000000 : ℝ)|^4253 ≤ (42762534292623/100000000000000 : ℝ)^3229
        have hw : |(2623389323/5000000000 : ℝ)|=(2623389323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1744076709/10000000000 : ℝ)|^4253 ≤ (5012060207659/50000000000000 : ℝ)^3229
        have hw : |(-1744076709/10000000000 : ℝ)|=(1744076709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1414101569/2500000000 : ℝ)|^4253 ≤ (5901668158573/12500000000000 : ℝ)^3229
        have hw : |(1414101569/2500000000 : ℝ)|=(1414101569/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s1_6 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1311694639/2500000000 : ℝ)*x 0 + (5656405881/10000000000 : ℝ)*x 1 + (-436019353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311694639/2500000000 : ℝ)^4253 ≤ (21381266663241/50000000000000 : ℝ)^3229 := by
    have hnat : (1311694639 : ℕ)^4253*50000000000000^3229 ≤ 21381266663241^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311694639 2500000000 21381266663241 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5656405881/10000000000 : ℝ)^4253 ≤ (11803335231499/25000000000000 : ℝ)^3229 := by
    have hnat : (5656405881 : ℕ)^4253*25000000000000^3229 ≤ 11803335231499^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5656405881 10000000000 11803335231499 25000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436019353/2500000000 : ℝ)^4253 ≤ (5012062868589/50000000000000 : ℝ)^3229 := by
    have hnat : (436019353 : ℕ)^4253*50000000000000^3229 ≤ 5012062868589^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436019353 2500000000 5012062868589 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311694639/2500000000 : ℝ), (5656405881/10000000000 : ℝ), (-436019353/2500000000 : ℝ)] ![(21381266663241/50000000000000 : ℝ), (11803335231499/25000000000000 : ℝ), (5012062868589/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311694639/2500000000 : ℝ)|^4253 ≤ (21381266663241/50000000000000 : ℝ)^3229
        have hw : |(1311694639/2500000000 : ℝ)|=(1311694639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5656405881/10000000000 : ℝ)|^4253 ≤ (11803335231499/25000000000000 : ℝ)^3229
        have hw : |(5656405881/10000000000 : ℝ)|=(5656405881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-436019353/2500000000 : ℝ)|^4253 ≤ (5012062868589/50000000000000 : ℝ)^3229
        have hw : |(-436019353/2500000000 : ℝ)|=(436019353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s1_7 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (537783697/1250000000 : ℝ)*x 0 + (1245940667/2500000000 : ℝ)*x 1 + (928084429/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (537783697/1250000000 : ℝ)^4253 ≤ (6585118426669/20000000000000 : ℝ)^3229 := by
    have hnat : (537783697 : ℕ)^4253*20000000000000^3229 ≤ 6585118426669^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537783697 1250000000 6585118426669 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1245940667/2500000000 : ℝ)^4253 ≤ (39961788036003/100000000000000 : ℝ)^3229 := by
    have hnat : (1245940667 : ℕ)^4253*100000000000000^3229 ≤ 39961788036003^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245940667 2500000000 39961788036003 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (928084429/2500000000 : ℝ)^4253 ≤ (1355630990603/5000000000000 : ℝ)^3229 := by
    have hnat : (928084429 : ℕ)^4253*5000000000000^3229 ≤ 1355630990603^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928084429 2500000000 1355630990603 5000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(537783697/1250000000 : ℝ), (1245940667/2500000000 : ℝ), (928084429/2500000000 : ℝ)] ![(6585118426669/20000000000000 : ℝ), (39961788036003/100000000000000 : ℝ), (1355630990603/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(537783697/1250000000 : ℝ)|^4253 ≤ (6585118426669/20000000000000 : ℝ)^3229
        have hw : |(537783697/1250000000 : ℝ)|=(537783697/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1245940667/2500000000 : ℝ)|^4253 ≤ (39961788036003/100000000000000 : ℝ)^3229
        have hw : |(1245940667/2500000000 : ℝ)|=(1245940667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(928084429/2500000000 : ℝ)|^4253 ≤ (1355630990603/5000000000000 : ℝ)^3229
        have hw : |(928084429/2500000000 : ℝ)|=(928084429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1293_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6807/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (13/1250 : ℝ)*pair X i i ≤ pair X i h) :
    (6419/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9921/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (6807/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (13/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (6807/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (13/1250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (6807/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (13/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (6807/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (13/1250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (6807/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (13/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (6807/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (13/1250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (13/1250 : ℝ) ^ (1063/256 : ℝ) ≤ (23339995679/4000000000000000000 : ℝ) := by
    have hpowers : (13/1250 : ℝ)^1063 ≤ (23339995679/4000000000000000000 : ℝ)^256 := by
      have hnat : (13 : ℕ)^1063*4000000000000000000^256 ≤ 23339995679^256*1250^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13 1250 23339995679 4000000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13/1250 : ℝ)) (X := (23339995679/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hpowhi : (6807/25000 : ℝ) ^ (1063/256 : ℝ) ≤ (450807515004721931/100000000000000000000 : ℝ) := by
    have hpowers : (6807/25000 : ℝ)^1063 ≤ (450807515004721931/100000000000000000000 : ℝ)^256 := by
      have hnat : (6807 : ℕ)^1063*100000000000000000000^256 ≤ 450807515004721931^256*25000^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6807 25000 450807515004721931 100000000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6807/25000 : ℝ)) (X := (450807515004721931/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (2000000023339995679/2000000000000000000 : ℝ) ≤ (2000000005620921/2000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (2000000023339995679/2000000000000000000 : ℝ)^256 ≤ (2000000005620921/2000000000000000 : ℝ)^1063 := by
      have hnat : (2000000023339995679 : ℕ)^256*2000000000000000^1063 ≤ 2000000005620921^1063*2000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000000023339995679 2000000000000000000 2000000005620921 2000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000000005620921/2000000000000000 : ℝ)) (X := (2000000023339995679/2000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50225404049252306953/50000000000000000000 : ℝ) ≤ (2502709546304257/2500000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (50225404049252306953/50000000000000000000 : ℝ)^256 ≤ (2502709546304257/2500000000000000 : ℝ)^1063 := by
      have hnat : (50225404049252306953 : ℕ)^256*2500000000000000^1063 ≤ 2502709546304257^1063*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50225404049252306953 50000000000000000000 2502709546304257 2500000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502709546304257/2500000000000000 : ℝ)) (X := (50225404049252306953/50000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50450807515004721931/50000000000000000000 : ℝ) ≤ (10021676342329451/10000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (50450807515004721931/50000000000000000000 : ℝ)^256 ≤ (10021676342329451/10000000000000000 : ℝ)^1063 := by
      have hnat : (50450807515004721931 : ℕ)^256*10000000000000000^1063 ≤ 10021676342329451^1063*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50450807515004721931 50000000000000000000 10021676342329451 10000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10021676342329451/10000000000000000 : ℝ)) (X := (50450807515004721931/50000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(23339995679/4000000000000000000 : ℝ) ≤ ((2618574573692095559/2618800000000000000 : ℝ)+2*(10838157112423/2618800000000000 : ℝ)*(13/1250 : ℝ))^(1063/256 : ℝ) := by
    rw [show (2618574573692095559/2618800000000000000 : ℝ)+2*(10838157112423/2618800000000000 : ℝ)*(13/1250 : ℝ)=(2000000005620921/2000000000000000 : ℝ) by norm_num, show 1+2*(23339995679/4000000000000000000 : ℝ)=(2000000023339995679/2000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(450807515004721931/100000000000000000000 : ℝ)+(23339995679/4000000000000000000 : ℝ) ≤ ((2618574573692095559/2618800000000000000 : ℝ)+(10838157112423/2618800000000000 : ℝ)*((6807/25000 : ℝ)+(13/1250 : ℝ)))^(1063/256 : ℝ) := by
    rw [show (2618574573692095559/2618800000000000000 : ℝ)+(10838157112423/2618800000000000 : ℝ)*((6807/25000 : ℝ)+(13/1250 : ℝ))=(2502709546304257/2500000000000000 : ℝ) by norm_num, show 1+(450807515004721931/100000000000000000000 : ℝ)+(23339995679/4000000000000000000 : ℝ)=(50225404049252306953/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(450807515004721931/100000000000000000000 : ℝ) ≤ ((2618574573692095559/2618800000000000000 : ℝ)+2*(10838157112423/2618800000000000 : ℝ)*(6807/25000 : ℝ))^(1063/256 : ℝ) := by
    rw [show (2618574573692095559/2618800000000000000 : ℝ)+2*(10838157112423/2618800000000000 : ℝ)*(6807/25000 : ℝ)=(10021676342329451/10000000000000000 : ℝ) by norm_num, show 1+2*(450807515004721931/100000000000000000000 : ℝ)=(50450807515004721931/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2618574573692095559/2618800000000000000 : ℝ)*(X 1 0+X 2 0)+(10838157112423/2618800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (13/1250 : ℝ)) (hi := (6807/25000 : ℝ)) (c := (2618574573692095559/2618800000000000000 : ℝ)) (alpha := (10838157112423/2618800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2618574573692095559/2618800000000000000 : ℝ)*(X 0 1+X 2 1)+(10838157112423/2618800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (13/1250 : ℝ)) (hi := (6807/25000 : ℝ)) (c := (2618574573692095559/2618800000000000000 : ℝ)) (alpha := (10838157112423/2618800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2618574573692095559/2618800000000000000 : ℝ)*(X 0 2+X 1 2)+(10838157112423/2618800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (13/1250 : ℝ)) (hi := (6807/25000 : ℝ)) (c := (2618574573692095559/2618800000000000000 : ℝ)) (alpha := (10838157112423/2618800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2030371021/10000000000 : ℝ)*X 0 0+(226593441/400000000 : ℝ)*X 0 1+(1005948297/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5410879859/10000000000 : ℝ)*X 1 0+(-2370741201/10000000000 : ℝ)*X 1 1+(5029741481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((21643519/40000000 : ℝ)*X 2 0+(5029741479/10000000000 : ℝ)*X 2 1+(-474148269/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((215048247/500000000 : ℝ)*X 0 0+(230937839/625000000 : ℝ)*X 0 1+(1000154729/2000000000 : ℝ)*X 0 2+(215048247/500000000 : ℝ)*X 1 0+(230937839/625000000 : ℝ)*X 1 1+(1000154729/2000000000 : ℝ)*X 1 2+(215048247/500000000 : ℝ)*X 2 0+(230937839/625000000 : ℝ)*X 2 1+(1000154729/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2031005923/10000000000 : ℝ)*X 0 0+(5038015451/10000000000 : ℝ)*X 0 1+(565640561/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2623389323/5000000000 : ℝ)*X 1 0+(-1744076709/10000000000 : ℝ)*X 1 1+(1414101569/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1311694639/2500000000 : ℝ)*X 2 0+(5656405881/10000000000 : ℝ)*X 2 1+(-436019353/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((537783697/1250000000 : ℝ)*X 0 0+(1245940667/2500000000 : ℝ)*X 0 1+(928084429/2500000000 : ℝ)*X 0 2+(537783697/1250000000 : ℝ)*X 1 0+(1245940667/2500000000 : ℝ)*X 1 1+(928084429/2500000000 : ℝ)*X 1 2+(537783697/1250000000 : ℝ)*X 2 0+(1245940667/2500000000 : ℝ)*X 2 1+(928084429/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17755135046137667437281/8183750000000000000000000000 : ℝ) := by norm_num
    linear_combination (17040507/100000000000000 : ℝ)*(base1) + (366751111/100000000000000 : ℝ)*(base19) + (335031983/100000000000000 : ℝ)*(base23) + (69558501/100000000000000 : ℝ)*(upper3) + (2985589/50000000000000 : ℝ)*(upper5) + (292550899545961/25000000000000 : ℝ)*(major0) + (292550899545961/25000000000000 : ℝ)*(major1) + (292550899545961/25000000000000 : ℝ)*(major2) + (1574571081430393/100000000000000 : ℝ)*(sp0) + (78728617482421/5000000000000 : ℝ)*(sp1) + (393643095341887/25000000000000 : ℝ)*(sp2) + (191458350897063/25000000000000 : ℝ)*(sp3) + (330401929/20000000000000 : ℝ)*(sp4) + (987020727/100000000000000 : ℝ)*(sp7) + (153166881529897/20000000000000 : ℝ)*(f.failure) + (393643179099883/25000000000000 : ℝ)*(f.sum) + (139946747096837/32735000000000000000000000000 : ℝ)*base66 + (182749082627889801/65470000000000000000000000000000 : ℝ)*base68 + (569979873583300199/65470000000000000000000000000000 : ℝ)*base69 + (127675075594350199/65470000000000000000000000000000 : ℝ)*base71 + (307927316831537/32735000000000000000000000000 : ℝ)*base74 + (37322986685249801/65470000000000000000000000000000 : ℝ)*base76 + (44450906590950199/65470000000000000000000000000000 : ℝ)*base77 + (13364494470729801/65470000000000000000000000000000 : ℝ)*base80 + (24161403470683/32735000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7867989/1000000000000000000000 : ℝ)*base90 + (7867989/1000000000000000000000 : ℝ)*base92 + (7867989/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (599832233064339934658924247/130940000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (155403563/20000000000000 : ℝ)*(base19) + (770707329/100000000000000 : ℝ)*(base23) + (15481217/50000000000000 : ℝ)*(upper2) + (30069423/20000000000000 : ℝ)*(upper3) + (96451477/100000000000000 : ℝ)*(upper5) + (1201810203499589/100000000000000 : ℝ)*(major0) + (1201810203499589/100000000000000 : ℝ)*(major1) + (1201810203499589/100000000000000 : ℝ)*(major2) + (4705175513/100000000000000 : ℝ)*(sp1) + (437938599/12500000000000 : ℝ)*(sp2) + (101068815497273/6250000000000 : ℝ)*(sp4) + (10106847286019/625000000000 : ℝ)*(sp5) + (1617096773740247/100000000000000 : ℝ)*(sp6) + (786519206343799/100000000000000 : ℝ)*(sp7) + (786519206343799/100000000000000 : ℝ)*(f.failure) + (101068815497273/6250000000000 : ℝ)*(f.sum) + (239574963572253/130940000000000000000000000000 : ℝ)*base66 + (377083295223372251/261880000000000000000000000000000 : ℝ)*base67 + (184572724039052251/261880000000000000000000000000000 : ℝ)*base69 + (957525118065092251/261880000000000000000000000000000 : ℝ)*base71 + (182833122679313/130940000000000000000000000000 : ℝ)*base74 + (945693319649387749/261880000000000000000000000000000 : ℝ)*base76 + (386906261825907749/261880000000000000000000000000000 : ℝ)*base78 + (716758937470212251/261880000000000000000000000000000 : ℝ)*base79 + (546506890838947/130940000000000000000000000000 : ℝ)*base81 + (34841163/5000000000000000000000 : ℝ)*base90 + (34841163/5000000000000000000000 : ℝ)*base92 + (34841163/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1293_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (6807/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (13/1250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6419/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9921/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1293_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1293_s2_0 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2074971933/10000000000 : ℝ)*x 0 + (27469713/50000000 : ℝ)*x 1 + (5172145561/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2074971933/10000000000 : ℝ)^4253 ≤ (2520281263617/20000000000000 : ℝ)^3229 := by
    have hnat : (2074971933 : ℕ)^4253*20000000000000^3229 ≤ 2520281263617^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074971933 10000000000 2520281263617 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (27469713/50000000 : ℝ)^4253 ≤ (709928518601/1562500000000 : ℝ)^3229 := by
    have hnat : (27469713 : ℕ)^4253*1562500000000^3229 ≤ 709928518601^3229*50000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      27469713 50000000 709928518601 1562500000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172145561/10000000000 : ℝ)^4253 ≤ (20981584236459/50000000000000 : ℝ)^3229 := by
    have hnat : (5172145561 : ℕ)^4253*50000000000000^3229 ≤ 20981584236459^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172145561 10000000000 20981584236459 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2074971933/10000000000 : ℝ), (27469713/50000000 : ℝ), (5172145561/10000000000 : ℝ)] ![(2520281263617/20000000000000 : ℝ), (709928518601/1562500000000 : ℝ), (20981584236459/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2074971933/10000000000 : ℝ)|^4253 ≤ (2520281263617/20000000000000 : ℝ)^3229
        have hw : |(-2074971933/10000000000 : ℝ)|=(2074971933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(27469713/50000000 : ℝ)|^4253 ≤ (709928518601/1562500000000 : ℝ)^3229
        have hw : |(27469713/50000000 : ℝ)|=(27469713/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172145561/10000000000 : ℝ)|^4253 ≤ (20981584236459/50000000000000 : ℝ)^3229
        have hw : |(5172145561/10000000000 : ℝ)|=(5172145561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s2_1 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1342377171/2500000000 : ℝ)*x 0 + (-3586757/16000000 : ℝ)*x 1 + (5172145707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342377171/2500000000 : ℝ)^4253 ≤ (22042444959927/50000000000000 : ℝ)^3229 := by
    have hnat : (1342377171 : ℕ)^4253*50000000000000^3229 ≤ 22042444959927^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342377171 2500000000 22042444959927 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3586757/16000000 : ℝ)^4253 ≤ (6975970016739/50000000000000 : ℝ)^3229 := by
    have hnat : (3586757 : ℕ)^4253*50000000000000^3229 ≤ 6975970016739^3229*16000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3586757 16000000 6975970016739 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5172145707/10000000000 : ℝ)^4253 ≤ (41963170033109/100000000000000 : ℝ)^3229 := by
    have hnat : (5172145707 : ℕ)^4253*100000000000000^3229 ≤ 41963170033109^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5172145707 10000000000 41963170033109 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342377171/2500000000 : ℝ), (-3586757/16000000 : ℝ), (5172145707/10000000000 : ℝ)] ![(22042444959927/50000000000000 : ℝ), (6975970016739/50000000000000 : ℝ), (41963170033109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342377171/2500000000 : ℝ)|^4253 ≤ (22042444959927/50000000000000 : ℝ)^3229
        have hw : |(1342377171/2500000000 : ℝ)|=(1342377171/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-3586757/16000000 : ℝ)|^4253 ≤ (6975970016739/50000000000000 : ℝ)^3229
        have hw : |(-3586757/16000000 : ℝ)|=(3586757/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5172145707/10000000000 : ℝ)|^4253 ≤ (41963170033109/100000000000000 : ℝ)^3229
        have hw : |(5172145707/10000000000 : ℝ)|=(5172145707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s2_2 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684754351/5000000000 : ℝ)*x 0 + (161629549/312500000 : ℝ)*x 1 + (-2241723283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684754351/5000000000 : ℝ)^4253 ≤ (8816978022901/20000000000000 : ℝ)^3229 := by
    have hnat : (2684754351 : ℕ)^4253*20000000000000^3229 ≤ 8816978022901^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684754351 5000000000 8816978022901 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161629549/312500000 : ℝ)^4253 ≤ (20981584273861/50000000000000 : ℝ)^3229 := by
    have hnat : (161629549 : ℕ)^4253*50000000000000^3229 ≤ 20981584273861^3229*312500000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161629549 312500000 20981584273861 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2241723283/10000000000 : ℝ)^4253 ≤ (13951941328679/100000000000000 : ℝ)^3229 := by
    have hnat : (2241723283 : ℕ)^4253*100000000000000^3229 ≤ 13951941328679^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2241723283 10000000000 13951941328679 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684754351/5000000000 : ℝ), (161629549/312500000 : ℝ), (-2241723283/10000000000 : ℝ)] ![(8816978022901/20000000000000 : ℝ), (20981584273861/50000000000000 : ℝ), (13951941328679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684754351/5000000000 : ℝ)|^4253 ≤ (8816978022901/20000000000000 : ℝ)^3229
        have hw : |(2684754351/5000000000 : ℝ)|=(2684754351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161629549/312500000 : ℝ)|^4253 ≤ (20981584273861/50000000000000 : ℝ)^3229
        have hw : |(161629549/312500000 : ℝ)|=(161629549/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2241723283/10000000000 : ℝ)|^4253 ≤ (13951941328679/100000000000000 : ℝ)^3229
        have hw : |(-2241723283/10000000000 : ℝ)|=(2241723283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s2_3 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165986647/5000000000 : ℝ)*x 0 + (4013188951/10000000000 : ℝ)*x 1 + (4674818377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165986647/5000000000 : ℝ)^4253 ≤ (33225334799051/100000000000000 : ℝ)^3229 := by
    have hnat : (2165986647 : ℕ)^4253*100000000000000^3229 ≤ 33225334799051^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165986647 5000000000 33225334799051 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4013188951/10000000000 : ℝ)^4253 ≤ (15021587770289/50000000000000 : ℝ)^3229 := by
    have hnat : (4013188951 : ℕ)^4253*50000000000000^3229 ≤ 15021587770289^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013188951 10000000000 15021587770289 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4674818377/10000000000 : ℝ)^4253 ≤ (7346297927893/20000000000000 : ℝ)^3229 := by
    have hnat : (4674818377 : ℕ)^4253*20000000000000^3229 ≤ 7346297927893^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4674818377 10000000000 7346297927893 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165986647/5000000000 : ℝ), (4013188951/10000000000 : ℝ), (4674818377/10000000000 : ℝ)] ![(33225334799051/100000000000000 : ℝ), (15021587770289/50000000000000 : ℝ), (7346297927893/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165986647/5000000000 : ℝ)|^4253 ≤ (33225334799051/100000000000000 : ℝ)^3229
        have hw : |(2165986647/5000000000 : ℝ)|=(2165986647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4013188951/10000000000 : ℝ)|^4253 ≤ (15021587770289/50000000000000 : ℝ)^3229
        have hw : |(4013188951/10000000000 : ℝ)|=(4013188951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4674818377/10000000000 : ℝ)|^4253 ≤ (7346297927893/20000000000000 : ℝ)^3229
        have hw : |(4674818377/10000000000 : ℝ)|=(4674818377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s2_4 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-259381721/1250000000 : ℝ)*x 0 + (5174279179/10000000000 : ℝ)*x 1 + (1372947267/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (259381721/1250000000 : ℝ)^4253 ≤ (1575257614747/12500000000000 : ℝ)^3229 := by
    have hnat : (259381721 : ℕ)^4253*12500000000000^3229 ≤ 1575257614747^3229*1250000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259381721 1250000000 1575257614747 12500000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5174279179/10000000000 : ℝ)^4253 ≤ (41985970315437/100000000000000 : ℝ)^3229 := by
    have hnat : (5174279179 : ℕ)^4253*100000000000000^3229 ≤ 41985970315437^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174279179 10000000000 41985970315437 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372947267/2500000000 : ℝ)^4253 ≤ (22705984373879/50000000000000 : ℝ)^3229 := by
    have hnat : (1372947267 : ℕ)^4253*50000000000000^3229 ≤ 22705984373879^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372947267 2500000000 22705984373879 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-259381721/1250000000 : ℝ), (5174279179/10000000000 : ℝ), (1372947267/2500000000 : ℝ)] ![(1575257614747/12500000000000 : ℝ), (41985970315437/100000000000000 : ℝ), (22705984373879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-259381721/1250000000 : ℝ)|^4253 ≤ (1575257614747/12500000000000 : ℝ)^3229
        have hw : |(-259381721/1250000000 : ℝ)|=(259381721/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5174279179/10000000000 : ℝ)|^4253 ≤ (41985970315437/100000000000000 : ℝ)^3229
        have hw : |(5174279179/10000000000 : ℝ)|=(5174279179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372947267/2500000000 : ℝ)|^4253 ≤ (22705984373879/50000000000000 : ℝ)^3229
        have hw : |(1372947267/2500000000 : ℝ)|=(1372947267/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s2_5 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5287022457/10000000000 : ℝ)*x 0 + (-1922079153/10000000000 : ℝ)*x 1 + (5491789203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287022457/10000000000 : ℝ)^4253 ≤ (43195072111019/100000000000000 : ℝ)^3229 := by
    have hnat : (5287022457 : ℕ)^4253*100000000000000^3229 ≤ 43195072111019^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287022457 10000000000 43195072111019 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1922079153/10000000000 : ℝ)^4253 ≤ (5696478827527/50000000000000 : ℝ)^3229 := by
    have hnat : (1922079153 : ℕ)^4253*50000000000000^3229 ≤ 5696478827527^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1922079153 10000000000 5696478827527 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5491789203/10000000000 : ℝ)^4253 ≤ (22705985109049/50000000000000 : ℝ)^3229 := by
    have hnat : (5491789203 : ℕ)^4253*50000000000000^3229 ≤ 22705985109049^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491789203 10000000000 22705985109049 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287022457/10000000000 : ℝ), (-1922079153/10000000000 : ℝ), (5491789203/10000000000 : ℝ)] ![(43195072111019/100000000000000 : ℝ), (5696478827527/50000000000000 : ℝ), (22705985109049/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287022457/10000000000 : ℝ)|^4253 ≤ (43195072111019/100000000000000 : ℝ)^3229
        have hw : |(5287022457/10000000000 : ℝ)|=(5287022457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1922079153/10000000000 : ℝ)|^4253 ≤ (5696478827527/50000000000000 : ℝ)^3229
        have hw : |(-1922079153/10000000000 : ℝ)|=(1922079153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5491789203/10000000000 : ℝ)|^4253 ≤ (22705985109049/50000000000000 : ℝ)^3229
        have hw : |(5491789203/10000000000 : ℝ)|=(5491789203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s2_6 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (264351131/500000000 : ℝ)*x 0 + (1372947269/2500000000 : ℝ)*x 1 + (-961039553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (264351131/500000000 : ℝ)^4253 ≤ (43195073865053/100000000000000 : ℝ)^3229 := by
    have hnat : (264351131 : ℕ)^4253*100000000000000^3229 ≤ 43195073865053^3229*500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264351131 500000000 43195073865053 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1372947269/2500000000 : ℝ)^4253 ≤ (45411968834889/100000000000000 : ℝ)^3229 := by
    have hnat : (1372947269 : ℕ)^4253*100000000000000^3229 ≤ 45411968834889^3229*2500000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372947269 2500000000 45411968834889 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (961039553/5000000000 : ℝ)^4253 ≤ (5696478644059/50000000000000 : ℝ)^3229 := by
    have hnat : (961039553 : ℕ)^4253*50000000000000^3229 ≤ 5696478644059^3229*5000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      961039553 5000000000 5696478644059 50000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(264351131/500000000 : ℝ), (1372947269/2500000000 : ℝ), (-961039553/5000000000 : ℝ)] ![(43195073865053/100000000000000 : ℝ), (45411968834889/100000000000000 : ℝ), (5696478644059/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(264351131/500000000 : ℝ)|^4253 ≤ (43195073865053/100000000000000 : ℝ)^3229
        have hw : |(264351131/500000000 : ℝ)|=(264351131/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1372947269/2500000000 : ℝ)|^4253 ≤ (45411968834889/100000000000000 : ℝ)^3229
        have hw : |(1372947269/2500000000 : ℝ)|=(1372947269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-961039553/5000000000 : ℝ)|^4253 ≤ (5696478644059/50000000000000 : ℝ)^3229
        have hw : |(-961039553/5000000000 : ℝ)|=(961039553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1293_s2_7 (p : ℝ) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4332141129/10000000000 : ℝ)*x 0 + (4670429953/10000000000 : ℝ)*x 1 + (4017621559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4332141129/10000000000 : ℝ)^4253 ≤ (33227030292569/100000000000000 : ℝ)^3229 := by
    have hnat : (4332141129 : ℕ)^4253*100000000000000^3229 ≤ 33227030292569^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332141129 10000000000 33227030292569 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4670429953/10000000000 : ℝ)^4253 ≤ (7337216062707/20000000000000 : ℝ)^3229 := by
    have hnat : (4670429953 : ℕ)^4253*20000000000000^3229 ≤ 7337216062707^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4670429953 10000000000 7337216062707 20000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4017621559/10000000000 : ℝ)^4253 ≤ (30086889377249/100000000000000 : ℝ)^3229 := by
    have hnat : (4017621559 : ℕ)^4253*100000000000000^3229 ≤ 30086889377249^3229*10000000000^4253 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4017621559 10000000000 30086889377249 100000000000000 4253 3229 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4253/1024 : ℝ)) 4253 3229 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4332141129/10000000000 : ℝ), (4670429953/10000000000 : ℝ), (4017621559/10000000000 : ℝ)] ![(33227030292569/100000000000000 : ℝ), (7337216062707/20000000000000 : ℝ), (30086889377249/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4332141129/10000000000 : ℝ)|^4253 ≤ (33227030292569/100000000000000 : ℝ)^3229
        have hw : |(4332141129/10000000000 : ℝ)|=(4332141129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4670429953/10000000000 : ℝ)|^4253 ≤ (7337216062707/20000000000000 : ℝ)^3229
        have hw : |(4670429953/10000000000 : ℝ)|=(4670429953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4017621559/10000000000 : ℝ)|^4253 ≤ (30086889377249/100000000000000 : ℝ)^3229
        have hw : |(4017621559/10000000000 : ℝ)|=(4017621559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1293_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9921/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1189/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16313/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9921/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9921/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6419/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9921/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9921/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6419/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9921/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9921/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6419/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6419/100000 : ℝ) ^ (1063/256 : ℝ) ≤ (1117363835080757/100000000000000000000 : ℝ) := by
    have hpowers : (6419/100000 : ℝ)^1063 ≤ (1117363835080757/100000000000000000000 : ℝ)^256 := by
      have hnat : (6419 : ℕ)^1063*100000000000000000000^256 ≤ 1117363835080757^256*100000^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6419 100000 1117363835080757 100000000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6419/100000 : ℝ)) (X := (1117363835080757/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hpowhi : (9921/50000 : ℝ) ^ (1063/256 : ℝ) ≤ (60576380216835217/50000000000000000000 : ℝ) := by
    have hpowers : (9921/50000 : ℝ)^1063 ≤ (60576380216835217/50000000000000000000 : ℝ)^256 := by
      have hnat : (9921 : ℕ)^1063*50000000000000000000^256 ≤ 60576380216835217^256*50000^1063 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9921 50000 60576380216835217 50000000000000000000 1063 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9921/50000 : ℝ)) (X := (60576380216835217/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001117363835080757/50000000000000000000 : ℝ) ≤ (10000053818008537/10000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (50001117363835080757/50000000000000000000 : ℝ)^256 ≤ (10000053818008537/10000000000000000 : ℝ)^1063 := by
      have hnat : (50001117363835080757 : ℕ)^256*10000000000000000^1063 ≤ 10000053818008537^1063*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001117363835080757 50000000000000000000 10000053818008537 10000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000053818008537/10000000000000000 : ℝ)) (X := (50001117363835080757/50000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100122270124268751191/100000000000000000000 : ℝ) ≤ (10002943239390203/10000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (100122270124268751191/100000000000000000000 : ℝ)^256 ≤ (10002943239390203/10000000000000000 : ℝ)^1063 := by
      have hnat : (100122270124268751191 : ℕ)^256*10000000000000000^1063 ≤ 10002943239390203^1063*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100122270124268751191 100000000000000000000 10002943239390203 10000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002943239390203/10000000000000000 : ℝ)) (X := (100122270124268751191/100000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25060576380216835217/25000000000000000000 : ℝ) ≤ (10005832660771869/10000000000000000 : ℝ) ^ (1063/256 : ℝ) := by
    have hpowers : (25060576380216835217/25000000000000000000 : ℝ)^256 ≤ (10005832660771869/10000000000000000 : ℝ)^1063 := by
      have hnat : (25060576380216835217 : ℕ)^256*10000000000000000^1063 ≤ 10005832660771869^1063*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25060576380216835217 25000000000000000000 10005832660771869 10000000000000000 256 1063 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10005832660771869/10000000000000000 : ℝ)) (X := (25060576380216835217/25000000000000000000 : ℝ)) (by norm_num) 1063 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1117363835080757/100000000000000000000 : ℝ) ≤ ((134193628007430764043/134230000000000000000 : ℝ)+2*(1444710690833/671150000000000 : ℝ)*(6419/100000 : ℝ))^(1063/256 : ℝ) := by
    rw [show (134193628007430764043/134230000000000000000 : ℝ)+2*(1444710690833/671150000000000 : ℝ)*(6419/100000 : ℝ)=(10000053818008537/10000000000000000 : ℝ) by norm_num, show 1+2*(1117363835080757/100000000000000000000 : ℝ)=(50001117363835080757/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(60576380216835217/50000000000000000000 : ℝ)+(1117363835080757/100000000000000000000 : ℝ) ≤ ((134193628007430764043/134230000000000000000 : ℝ)+(1444710690833/671150000000000 : ℝ)*((9921/50000 : ℝ)+(6419/100000 : ℝ)))^(1063/256 : ℝ) := by
    rw [show (134193628007430764043/134230000000000000000 : ℝ)+(1444710690833/671150000000000 : ℝ)*((9921/50000 : ℝ)+(6419/100000 : ℝ))=(10002943239390203/10000000000000000 : ℝ) by norm_num, show 1+(60576380216835217/50000000000000000000 : ℝ)+(1117363835080757/100000000000000000000 : ℝ)=(100122270124268751191/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(60576380216835217/50000000000000000000 : ℝ) ≤ ((134193628007430764043/134230000000000000000 : ℝ)+2*(1444710690833/671150000000000 : ℝ)*(9921/50000 : ℝ))^(1063/256 : ℝ) := by
    rw [show (134193628007430764043/134230000000000000000 : ℝ)+2*(1444710690833/671150000000000 : ℝ)*(9921/50000 : ℝ)=(10005832660771869/10000000000000000 : ℝ) by norm_num, show 1+2*(60576380216835217/50000000000000000000 : ℝ)=(25060576380216835217/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (134193628007430764043/134230000000000000000 : ℝ)*(X 1 0+X 2 0)+(1444710690833/671150000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (6419/100000 : ℝ)) (hi := (9921/50000 : ℝ)) (c := (134193628007430764043/134230000000000000000 : ℝ)) (alpha := (1444710690833/671150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (134193628007430764043/134230000000000000000 : ℝ)*(X 0 1+X 2 1)+(1444710690833/671150000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (6419/100000 : ℝ)) (hi := (9921/50000 : ℝ)) (c := (134193628007430764043/134230000000000000000 : ℝ)) (alpha := (1444710690833/671150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (134193628007430764043/134230000000000000000 : ℝ)*(X 0 2+X 1 2)+(1444710690833/671150000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1063/256 : ℝ)) (lo := (6419/100000 : ℝ)) (hi := (9921/50000 : ℝ)) (c := (134193628007430764043/134230000000000000000 : ℝ)) (alpha := (1444710690833/671150000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2074971933/10000000000 : ℝ)*X 0 0+(27469713/50000000 : ℝ)*X 0 1+(5172145561/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1342377171/2500000000 : ℝ)*X 1 0+(-3586757/16000000 : ℝ)*X 1 1+(5172145707/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2684754351/5000000000 : ℝ)*X 2 0+(161629549/312500000 : ℝ)*X 2 1+(-2241723283/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2165986647/5000000000 : ℝ)*X 0 0+(4013188951/10000000000 : ℝ)*X 0 1+(4674818377/10000000000 : ℝ)*X 0 2+(2165986647/5000000000 : ℝ)*X 1 0+(4013188951/10000000000 : ℝ)*X 1 1+(4674818377/10000000000 : ℝ)*X 1 2+(2165986647/5000000000 : ℝ)*X 2 0+(4013188951/10000000000 : ℝ)*X 2 1+(4674818377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-259381721/1250000000 : ℝ)*X 0 0+(5174279179/10000000000 : ℝ)*X 0 1+(1372947267/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287022457/10000000000 : ℝ)*X 1 0+(-1922079153/10000000000 : ℝ)*X 1 1+(5491789203/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((264351131/500000000 : ℝ)*X 2 0+(1372947269/2500000000 : ℝ)*X 2 1+(-961039553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4332141129/10000000000 : ℝ)*X 0 0+(4670429953/10000000000 : ℝ)*X 0 1+(4017621559/10000000000 : ℝ)*X 0 2+(4332141129/10000000000 : ℝ)*X 1 0+(4670429953/10000000000 : ℝ)*X 1 1+(4017621559/10000000000 : ℝ)*X 1 2+(4332141129/10000000000 : ℝ)*X 2 0+(4670429953/10000000000 : ℝ)*X 2 1+(4017621559/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1293_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3940996327485702032397240057/838937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1865339387/100000000000000 : ℝ)*(base19) + (204334871/12500000000000 : ℝ)*(base23) + (2588939/2000000000000 : ℝ)*(lower2) + (555735979/100000000000000 : ℝ)*(upper3) + (247528461/100000000000000 : ℝ)*(upper5) + (577378663406233/25000000000000 : ℝ)*(major0) + (577378663406233/25000000000000 : ℝ)*(major1) + (577378663406233/25000000000000 : ℝ)*(major2) + (155378280596167/5000000000000 : ℝ)*(sp0) + (1553787976862441/50000000000000 : ℝ)*(sp1) + (31075761843853/1000000000000 : ℝ)*(sp2) + (1511434023093473/100000000000000 : ℝ)*(sp3) + (12207140929/100000000000000 : ℝ)*(sp4) + (17308505309/100000000000000 : ℝ)*(sp7) + (755725665799391/50000000000000 : ℝ)*(f.failure) + (776894454766067/25000000000000 : ℝ)*(f.sum) + (352354682438147/67115000000000000000000000000 : ℝ)*base65 + (16157380783251969981/3355750000000000000000000000000000 : ℝ)*base68 + (14326246576696719981/3355750000000000000000000000000000 : ℝ)*base70 + (23565200988816969981/3355750000000000000000000000000000 : ℝ)*base72 + (157040713112981/33557500000000000000000000000 : ℝ)*base73 + (21120041855453219981/3355750000000000000000000000000000 : ℝ)*base76 + (13935287435439030019/3355750000000000000000000000000000 : ℝ)*base77 + (18156230280778719981/3355750000000000000000000000000000 : ℝ)*base80 + (12117701221577/4194687500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (17457133/2500000000000000000000 : ℝ)*base89 + (17457133/2500000000000000000000 : ℝ)*base91 + (17457133/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63365135404978312749700018983/6711500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1796305773/100000000000000 : ℝ)*(base19) + (538104663/25000000000000 : ℝ)*(base23) + (52467511/20000000000000 : ℝ)*(upper3) + (9909783/10000000000000 : ℝ)*(lower4) + (28549509/20000000000000 : ℝ)*(upper5) + (2340674741125491/100000000000000 : ℝ)*(major0) + (2340674741125491/100000000000000 : ℝ)*(major1) + (2340674741125491/100000000000000 : ℝ)*(major2) + (9228926623/50000000000000 : ℝ)*(sp1) + (23045683707/100000000000000 : ℝ)*(sp2) + (1574752629398123/50000000000000 : ℝ)*(sp4) + (787371251159307/25000000000000 : ℝ)*(sp5) + (24605312974171/781250000000 : ℝ)*(sp6) + (153184390874547/10000000000000 : ℝ)*(sp7) + (153184390874547/10000000000000 : ℝ)*(f.failure) + (1574752629398123/50000000000000 : ℝ)*(f.sum) + (50369306083319/16778750000000000000000000000 : ℝ)*base65 + (97379360473362120113/13423000000000000000000000000000000 : ℝ)*base67 + (172083704350940120113/13423000000000000000000000000000000 : ℝ)*base69 + (71110171669604120113/13423000000000000000000000000000000 : ℝ)*base71 + (97813721204633/33557500000000000000000000000 : ℝ)*base73 + (94566879659746120113/13423000000000000000000000000000000 : ℝ)*base75 + (56894578231482120113/13423000000000000000000000000000000 : ℝ)*base77 + (23458013152672120113/13423000000000000000000000000000000 : ℝ)*base79 + (314206744886091/67115000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1830039/500000000000000000000 : ℝ)*base90 + (1830039/500000000000000000000 : ℝ)*base92 + (1830039/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1293_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9921/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6419/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1189/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1293_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1293_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1189/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1293_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1293_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1293_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1063/256 : ℝ) ≤ p) (hpb : p ≤ (4253/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76400563/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1189/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16313/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1293_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
