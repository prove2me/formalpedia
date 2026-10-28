-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1216_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:08:58.537677+00:00
-- url     : https://prove2.me/submissions/d4217c9f-1c47-4004-9832-cccdd681a818

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
theorem support_rectangle_w1216_s0_0 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1868609123/10000000000 : ℝ)*x 0 + (6037384483/10000000000 : ℝ)*x 1 + (2394879679/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1868609123/10000000000 : ℝ)^8409 ≤ (10888677249891/100000000000000 : ℝ)^6361 := by
    have hnat : (1868609123 : ℕ)^8409*100000000000000^6361 ≤ 10888677249891^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868609123 10000000000 10888677249891 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6037384483/10000000000 : ℝ)^8409 ≤ (51320454784663/100000000000000 : ℝ)^6361 := by
    have hnat : (6037384483 : ℕ)^8409*100000000000000^6361 ≤ 51320454784663^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6037384483 10000000000 51320454784663 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2394879679/5000000000 : ℝ)^8409 ≤ (4723858493309/12500000000000 : ℝ)^6361 := by
    have hnat : (2394879679 : ℕ)^8409*12500000000000^6361 ≤ 4723858493309^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2394879679 5000000000 4723858493309 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1868609123/10000000000 : ℝ), (6037384483/10000000000 : ℝ), (2394879679/5000000000 : ℝ)] ![(10888677249891/100000000000000 : ℝ), (51320454784663/100000000000000 : ℝ), (4723858493309/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1868609123/10000000000 : ℝ)|^8409 ≤ (10888677249891/100000000000000 : ℝ)^6361
        have hw : |(-1868609123/10000000000 : ℝ)|=(1868609123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6037384483/10000000000 : ℝ)|^8409 ≤ (51320454784663/100000000000000 : ℝ)^6361
        have hw : |(6037384483/10000000000 : ℝ)|=(6037384483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2394879679/5000000000 : ℝ)|^8409 ≤ (4723858493309/12500000000000 : ℝ)^6361
        have hw : |(2394879679/5000000000 : ℝ)|=(2394879679/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s0_1 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1378156079/2500000000 : ℝ)*x 0 + (-1291276947/5000000000 : ℝ)*x 1 + (4789759327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1378156079/2500000000 : ℝ)^8409 ≤ (11376944738769/25000000000000 : ℝ)^6361 := by
    have hnat : (1378156079 : ℕ)^8409*25000000000000^6361 ≤ 11376944738769^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1378156079 2500000000 11376944738769 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1291276947/5000000000 : ℝ)^8409 ≤ (835067670821/5000000000000 : ℝ)^6361 := by
    have hnat : (1291276947 : ℕ)^8409*5000000000000^6361 ≤ 835067670821^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291276947 5000000000 835067670821 5000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4789759327/10000000000 : ℝ)^8409 ≤ (37790867623137/100000000000000 : ℝ)^6361 := by
    have hnat : (4789759327 : ℕ)^8409*100000000000000^6361 ≤ 37790867623137^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4789759327 10000000000 37790867623137 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1378156079/2500000000 : ℝ), (-1291276947/5000000000 : ℝ), (4789759327/10000000000 : ℝ)] ![(11376944738769/25000000000000 : ℝ), (835067670821/5000000000000 : ℝ), (37790867623137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1378156079/2500000000 : ℝ)|^8409 ≤ (11376944738769/25000000000000 : ℝ)^6361
        have hw : |(1378156079/2500000000 : ℝ)|=(1378156079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1291276947/5000000000 : ℝ)|^8409 ≤ (835067670821/5000000000000 : ℝ)^6361
        have hw : |(-1291276947/5000000000 : ℝ)|=(1291276947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4789759327/10000000000 : ℝ)|^8409 ≤ (37790867623137/100000000000000 : ℝ)^6361
        have hw : |(4789759327/10000000000 : ℝ)|=(4789759327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s0_2 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1102524859/2000000000 : ℝ)*x 0 + (598719919/1250000000 : ℝ)*x 1 + (-258255389/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1102524859/2000000000 : ℝ)^8409 ≤ (22753889362951/50000000000000 : ℝ)^6361 := by
    have hnat : (1102524859 : ℕ)^8409*50000000000000^6361 ≤ 22753889362951^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1102524859 2000000000 22753889362951 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (598719919/1250000000 : ℝ)^8409 ≤ (37790867883891/100000000000000 : ℝ)^6361 := by
    have hnat : (598719919 : ℕ)^8409*100000000000000^6361 ≤ 37790867883891^6361*1250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      598719919 1250000000 37790867883891 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (258255389/1000000000 : ℝ)^8409 ≤ (16701353382223/100000000000000 : ℝ)^6361 := by
    have hnat : (258255389 : ℕ)^8409*100000000000000^6361 ≤ 16701353382223^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258255389 1000000000 16701353382223 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1102524859/2000000000 : ℝ), (598719919/1250000000 : ℝ), (-258255389/1000000000 : ℝ)] ![(22753889362951/50000000000000 : ℝ), (37790867883891/100000000000000 : ℝ), (16701353382223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1102524859/2000000000 : ℝ)|^8409 ≤ (22753889362951/50000000000000 : ℝ)^6361
        have hw : |(1102524859/2000000000 : ℝ)|=(1102524859/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(598719919/1250000000 : ℝ)|^8409 ≤ (37790867883891/100000000000000 : ℝ)^6361
        have hw : |(598719919/1250000000 : ℝ)|=(598719919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-258255389/1000000000 : ℝ)|^8409 ≤ (16701353382223/100000000000000 : ℝ)^6361
        have hw : |(-258255389/1000000000 : ℝ)|=(258255389/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s0_3 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4195071239/10000000000 : ℝ)*x 0 + (311789543/1000000000 : ℝ)*x 1 + (2818045591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4195071239/10000000000 : ℝ)^8409 ≤ (3964475820683/12500000000000 : ℝ)^6361 := by
    have hnat : (4195071239 : ℕ)^8409*12500000000000^6361 ≤ 3964475820683^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195071239 10000000000 3964475820683 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (311789543/1000000000 : ℝ)^8409 ≤ (10712090253461/50000000000000 : ℝ)^6361 := by
    have hnat : (311789543 : ℕ)^8409*50000000000000^6361 ≤ 10712090253461^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      311789543 1000000000 10712090253461 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2818045591/5000000000 : ℝ)^8409 ≤ (234300064547/500000000000 : ℝ)^6361 := by
    have hnat : (2818045591 : ℕ)^8409*500000000000^6361 ≤ 234300064547^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2818045591 5000000000 234300064547 500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4195071239/10000000000 : ℝ), (311789543/1000000000 : ℝ), (2818045591/5000000000 : ℝ)] ![(3964475820683/12500000000000 : ℝ), (10712090253461/50000000000000 : ℝ), (234300064547/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4195071239/10000000000 : ℝ)|^8409 ≤ (3964475820683/12500000000000 : ℝ)^6361
        have hw : |(4195071239/10000000000 : ℝ)|=(4195071239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(311789543/1000000000 : ℝ)|^8409 ≤ (10712090253461/50000000000000 : ℝ)^6361
        have hw : |(311789543/1000000000 : ℝ)|=(311789543/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2818045591/5000000000 : ℝ)|^8409 ≤ (234300064547/500000000000 : ℝ)^6361
        have hw : |(2818045591/5000000000 : ℝ)|=(2818045591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s0_4 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1873540943/10000000000 : ℝ)*x 0 + (37671131/78125000 : ℝ)*x 1 + (6004103791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1873540943/10000000000 : ℝ)^8409 ≤ (5463342283193/50000000000000 : ℝ)^6361 := by
    have hnat : (1873540943 : ℕ)^8409*50000000000000^6361 ≤ 5463342283193^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1873540943 10000000000 5463342283193 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37671131/78125000 : ℝ)^8409 ≤ (19063256148859/50000000000000 : ℝ)^6361 := by
    have hnat : (37671131 : ℕ)^8409*50000000000000^6361 ≤ 19063256148859^6361*78125000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37671131 78125000 19063256148859 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6004103791/10000000000 : ℝ)^8409 ≤ (2037872124767/4000000000000 : ℝ)^6361 := by
    have hnat : (6004103791 : ℕ)^8409*4000000000000^6361 ≤ 2037872124767^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6004103791 10000000000 2037872124767 4000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1873540943/10000000000 : ℝ), (37671131/78125000 : ℝ), (6004103791/10000000000 : ℝ)] ![(5463342283193/50000000000000 : ℝ), (19063256148859/50000000000000 : ℝ), (2037872124767/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1873540943/10000000000 : ℝ)|^8409 ≤ (5463342283193/50000000000000 : ℝ)^6361
        have hw : |(-1873540943/10000000000 : ℝ)|=(1873540943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(37671131/78125000 : ℝ)|^8409 ≤ (19063256148859/50000000000000 : ℝ)^6361
        have hw : |(37671131/78125000 : ℝ)|=(37671131/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6004103791/10000000000 : ℝ)|^8409 ≤ (2037872124767/4000000000000 : ℝ)^6361
        have hw : |(6004103791/10000000000 : ℝ)|=(6004103791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s0_5 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (323329727/625000000 : ℝ)*x 0 + (-273641547/2000000000 : ℝ)*x 1 + (6004105577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323329727/625000000 : ℝ)^8409 ≤ (10460418149467/25000000000000 : ℝ)^6361 := by
    have hnat : (323329727 : ℕ)^8409*25000000000000^6361 ≤ 10460418149467^6361*625000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323329727 625000000 10460418149467 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (273641547/2000000000 : ℝ)^8409 ≤ (7211504239363/100000000000000 : ℝ)^6361 := by
    have hnat : (273641547 : ℕ)^8409*100000000000000^6361 ≤ 7211504239363^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273641547 2000000000 7211504239363 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6004105577/10000000000 : ℝ)^8409 ≤ (12736705788311/25000000000000 : ℝ)^6361 := by
    have hnat : (6004105577 : ℕ)^8409*25000000000000^6361 ≤ 12736705788311^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6004105577 10000000000 12736705788311 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(323329727/625000000 : ℝ), (-273641547/2000000000 : ℝ), (6004105577/10000000000 : ℝ)] ![(10460418149467/25000000000000 : ℝ), (7211504239363/100000000000000 : ℝ), (12736705788311/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(323329727/625000000 : ℝ)|^8409 ≤ (10460418149467/25000000000000 : ℝ)^6361
        have hw : |(323329727/625000000 : ℝ)|=(323329727/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-273641547/2000000000 : ℝ)|^8409 ≤ (7211504239363/100000000000000 : ℝ)^6361
        have hw : |(-273641547/2000000000 : ℝ)|=(273641547/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6004105577/10000000000 : ℝ)|^8409 ≤ (12736705788311/25000000000000 : ℝ)^6361
        have hw : |(6004105577/10000000000 : ℝ)|=(6004105577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s0_6 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (517327653/1000000000 : ℝ)*x 0 + (3002052129/5000000000 : ℝ)*x 1 + (-8551303/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517327653/1000000000 : ℝ)^8409 ≤ (130755256873/312500000000 : ℝ)^6361 := by
    have hnat : (517327653 : ℕ)^8409*312500000000^6361 ≤ 130755256873^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517327653 1000000000 130755256873 312500000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3002052129/5000000000 : ℝ)^8409 ≤ (25473404178823/50000000000000 : ℝ)^6361 := by
    have hnat : (3002052129 : ℕ)^8409*50000000000000^6361 ≤ 25473404178823^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3002052129 5000000000 25473404178823 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8551303/62500000 : ℝ)^8409 ≤ (360575471517/5000000000000 : ℝ)^6361 := by
    have hnat : (8551303 : ℕ)^8409*5000000000000^6361 ≤ 360575471517^6361*62500000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8551303 62500000 360575471517 5000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517327653/1000000000 : ℝ), (3002052129/5000000000 : ℝ), (-8551303/62500000 : ℝ)] ![(130755256873/312500000000 : ℝ), (25473404178823/50000000000000 : ℝ), (360575471517/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517327653/1000000000 : ℝ)|^8409 ≤ (130755256873/312500000000 : ℝ)^6361
        have hw : |(517327653/1000000000 : ℝ)|=(517327653/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3002052129/5000000000 : ℝ)|^8409 ≤ (25473404178823/50000000000000 : ℝ)^6361
        have hw : |(3002052129/5000000000 : ℝ)|=(3002052129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8551303/62500000 : ℝ)|^8409 ≤ (360575471517/5000000000000 : ℝ)^6361
        have hw : |(-8551303/62500000 : ℝ)|=(8551303/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s0_7 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (105125617/250000000 : ℝ)*x 0 + (5571213249/10000000000 : ℝ)*x 1 + (3185063891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105125617/250000000 : ℝ)^8409 ≤ (31815322902571/100000000000000 : ℝ)^6361 := by
    have hnat : (105125617 : ℕ)^8409*100000000000000^6361 ≤ 31815322902571^6361*250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105125617 250000000 31815322902571 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5571213249/10000000000 : ℝ)^8409 ≤ (23074127157957/50000000000000 : ℝ)^6361 := by
    have hnat : (5571213249 : ℕ)^8409*50000000000000^6361 ≤ 23074127157957^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5571213249 10000000000 23074127157957 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3185063891/10000000000 : ℝ)^8409 ≤ (11018211388393/50000000000000 : ℝ)^6361 := by
    have hnat : (3185063891 : ℕ)^8409*50000000000000^6361 ≤ 11018211388393^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3185063891 10000000000 11018211388393 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105125617/250000000 : ℝ), (5571213249/10000000000 : ℝ), (3185063891/10000000000 : ℝ)] ![(31815322902571/100000000000000 : ℝ), (23074127157957/50000000000000 : ℝ), (11018211388393/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105125617/250000000 : ℝ)|^8409 ≤ (31815322902571/100000000000000 : ℝ)^6361
        have hw : |(105125617/250000000 : ℝ)|=(105125617/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5571213249/10000000000 : ℝ)|^8409 ≤ (23074127157957/50000000000000 : ℝ)^6361
        have hw : |(5571213249/10000000000 : ℝ)|=(5571213249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3185063891/10000000000 : ℝ)|^8409 ≤ (11018211388393/50000000000000 : ℝ)^6361
        have hw : |(3185063891/10000000000 : ℝ)|=(3185063891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1216_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (357/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13767/50000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (1051/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1051 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1051*1^256 ≤ 0^256*1^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1051/256 : ℝ) ≤ (1162089920636161911/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1051 ≤ (1162089920636161911/50000000000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1051*50000000000000000000^256 ≤ 1162089920636161911^256*5^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1162089920636161911 50000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1162089920636161911/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1051 := by
      have hnat : (1 : ℕ)^256*1^1051 ≤ 1^1051*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (51162089920636161911/50000000000000000000 : ℝ) ≤ (5028060415878797/5000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (51162089920636161911/50000000000000000000 : ℝ)^256 ≤ (5028060415878797/5000000000000000 : ℝ)^1051 := by
      have hnat : (51162089920636161911 : ℕ)^256*5000000000000000^1051 ≤ 5028060415878797^1051*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51162089920636161911 50000000000000000000 5028060415878797 5000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5028060415878797/5000000000000000 : ℝ)) (X := (51162089920636161911/50000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (26162089920636161911/25000000000000000000 : ℝ) ≤ (2528060415878797/2500000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (26162089920636161911/25000000000000000000 : ℝ)^256 ≤ (2528060415878797/2500000000000000 : ℝ)^1051 := by
      have hnat : (26162089920636161911 : ℕ)^256*2500000000000000^1051 ≤ 2528060415878797^1051*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26162089920636161911 25000000000000000000 2528060415878797 2500000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2528060415878797/2500000000000000 : ℝ)) (X := (26162089920636161911/25000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(28060415878797/2000000000000000 : ℝ)*(0 : ℝ))^(1051/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(28060415878797/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1162089920636161911/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(28060415878797/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1051/256 : ℝ) := by
    rw [show (1 : ℝ)+(28060415878797/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5028060415878797/5000000000000000 : ℝ) by norm_num, show 1+(1162089920636161911/50000000000000000000 : ℝ)+(0 : ℝ)=(51162089920636161911/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1162089920636161911/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(28060415878797/2000000000000000 : ℝ)*(2/5 : ℝ))^(1051/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(28060415878797/2000000000000000 : ℝ)*(2/5 : ℝ)=(2528060415878797/2500000000000000 : ℝ) by norm_num, show 1+2*(1162089920636161911/50000000000000000000 : ℝ)=(26162089920636161911/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(28060415878797/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28060415878797/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(28060415878797/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28060415878797/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(28060415878797/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (28060415878797/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1868609123/10000000000 : ℝ)*X 0 0+(6037384483/10000000000 : ℝ)*X 0 1+(2394879679/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1378156079/2500000000 : ℝ)*X 1 0+(-1291276947/5000000000 : ℝ)*X 1 1+(4789759327/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1102524859/2000000000 : ℝ)*X 2 0+(598719919/1250000000 : ℝ)*X 2 1+(-258255389/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4195071239/10000000000 : ℝ)*X 0 0+(311789543/1000000000 : ℝ)*X 0 1+(2818045591/5000000000 : ℝ)*X 0 2+(4195071239/10000000000 : ℝ)*X 1 0+(311789543/1000000000 : ℝ)*X 1 1+(2818045591/5000000000 : ℝ)*X 1 2+(4195071239/10000000000 : ℝ)*X 2 0+(311789543/1000000000 : ℝ)*X 2 1+(2818045591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1873540943/10000000000 : ℝ)*X 0 0+(37671131/78125000 : ℝ)*X 0 1+(6004103791/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((323329727/625000000 : ℝ)*X 1 0+(-273641547/2000000000 : ℝ)*X 1 1+(6004105577/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((517327653/1000000000 : ℝ)*X 2 0+(3002052129/5000000000 : ℝ)*X 2 1+(-8551303/62500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((105125617/250000000 : ℝ)*X 0 0+(5571213249/10000000000 : ℝ)*X 0 1+(3185063891/10000000000 : ℝ)*X 0 2+(105125617/250000000 : ℝ)*X 1 0+(5571213249/10000000000 : ℝ)*X 1 1+(3185063891/10000000000 : ℝ)*X 1 2+(105125617/250000000 : ℝ)*X 2 0+(5571213249/10000000000 : ℝ)*X 2 1+(3185063891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38999845913049171139623/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (69997471/100000000000000 : ℝ)*(base1) + (762559007/50000000000000 : ℝ)*(base19) + (283520313/20000000000000 : ℝ)*(base23) + (104463071/100000000000000 : ℝ)*(base24) + (348301901/100000000000000 : ℝ)*(upper3) + (74915343308349/12500000000000 : ℝ)*(major0) + (74915343308349/12500000000000 : ℝ)*(major1) + (74915343308349/12500000000000 : ℝ)*(major2) + (16030559451861/2000000000000 : ℝ)*(sp0) + (801529756333081/100000000000000 : ℝ)*(sp1) + (400764879693229/50000000000000 : ℝ)*(sp2) + (397111271749629/100000000000000 : ℝ)*(sp3) + (675771103/20000000000000 : ℝ)*(sp4) + (2661736207/100000000000000 : ℝ)*(sp7) + (397114003483307/100000000000000 : ℝ)*(f.failure) + (400765640725547/50000000000000 : ℝ)*(f.sum) + (13843640976153/12500000000000000000000000000 : ℝ)*base65 + (83609665101153/25000000000000000000000000000 : ℝ)*base67 + (234415877676153/25000000000000000000000000000 : ℝ)*base69 + (94178015001153/25000000000000000000000000000 : ℝ)*base71 + (16768999688653/12500000000000000000000000000 : ℝ)*base73 + (73856447126153/25000000000000000000000000000 : ℝ)*base75 + (210453027151153/25000000000000000000000000000 : ℝ)*base77 + (96549251451153/25000000000000000000000000000 : ℝ)*base79 + (13852540988653/12500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (538201/1000000000000000000000 : ℝ)*base90 + (538201/1000000000000000000000 : ℝ)*base92 + (538201/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (122331935683625067532083/20000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1288217/25000000000000 : ℝ)*(base1) + (1704629643/100000000000000 : ℝ)*(base19) + (937679563/50000000000000 : ℝ)*(base23) + (2786141/781250000000 : ℝ)*(upper3) + (17701157/25000000000000 : ℝ)*(upper5) + (632482941970987/100000000000000 : ℝ)*(major0) + (632482941970987/100000000000000 : ℝ)*(major1) + (632482941970987/100000000000000 : ℝ)*(major2) + (121594803/3125000000000 : ℝ)*(sp1) + (265960507/6250000000000 : ℝ)*(sp2) + (211469895983817/25000000000000 : ℝ)*(sp4) + (42293699155953/5000000000000 : ℝ)*(sp5) + (845873448055163/100000000000000 : ℝ)*(sp6) + (419086096120139/100000000000000 : ℝ)*(sp7) + (419086101273007/100000000000000 : ℝ)*(f.failure) + (528674736739/62500000000 : ℝ)*(f.sum) + (217099602862639/100000000000000000000000000000 : ℝ)*base65 + (1152118995462639/200000000000000000000000000000 : ℝ)*base67 + (280294515062639/200000000000000000000000000000 : ℝ)*base69 + (1697589207262639/200000000000000000000000000000 : ℝ)*base71 + (396676853762639/100000000000000000000000000000 : ℝ)*base73 + (1522118670262639/200000000000000000000000000000 : ℝ)*base75 + (122587692462639/200000000000000000000000000000 : ℝ)*base77 + (1181722935337361/200000000000000000000000000000 : ℝ)*base80 + (387648589562639/100000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (3095301/1000000000000000000000 : ℝ)*base90 + (3095301/1000000000000000000000 : ℝ)*base92 + (3095301/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1216_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (357/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13767/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1216_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1216_s1_0 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2067908769/10000000000 : ℝ)*x 0 + (1420547133/2500000000 : ℝ)*x 1 + (5017380321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067908769/10000000000 : ℝ)^8409 ≤ (12449689431411/100000000000000 : ℝ)^6361 := by
    have hnat : (2067908769 : ℕ)^8409*100000000000000^6361 ≤ 12449689431411^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067908769 10000000000 12449689431411 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1420547133/2500000000 : ℝ)^8409 ≤ (947346838429/2000000000000 : ℝ)^6361 := by
    have hnat : (1420547133 : ℕ)^8409*2000000000000^6361 ≤ 947346838429^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1420547133 2500000000 947346838429 2000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5017380321/10000000000 : ℝ)^8409 ≤ (8036593726939/20000000000000 : ℝ)^6361 := by
    have hnat : (5017380321 : ℕ)^8409*20000000000000^6361 ≤ 8036593726939^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5017380321 10000000000 8036593726939 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2067908769/10000000000 : ℝ), (1420547133/2500000000 : ℝ), (5017380321/10000000000 : ℝ)] ![(12449689431411/100000000000000 : ℝ), (947346838429/2000000000000 : ℝ), (8036593726939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2067908769/10000000000 : ℝ)|^8409 ≤ (12449689431411/100000000000000 : ℝ)^6361
        have hw : |(-2067908769/10000000000 : ℝ)|=(2067908769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1420547133/2500000000 : ℝ)|^8409 ≤ (947346838429/2000000000000 : ℝ)^6361
        have hw : |(1420547133/2500000000 : ℝ)|=(1420547133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5017380321/10000000000 : ℝ)|^8409 ≤ (8036593726939/20000000000000 : ℝ)^6361
        have hw : |(5017380321/10000000000 : ℝ)|=(5017380321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s1_1 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (541507399/1000000000 : ℝ)*x 0 + (-2425353001/10000000000 : ℝ)*x 1 + (1254345069/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541507399/1000000000 : ℝ)^8409 ≤ (8889250417337/20000000000000 : ℝ)^6361 := by
    have hnat : (541507399 : ℕ)^8409*20000000000000^6361 ≤ 8889250417337^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541507399 1000000000 8889250417337 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2425353001/10000000000 : ℝ)^8409 ≤ (3842694937953/25000000000000 : ℝ)^6361 := by
    have hnat : (2425353001 : ℕ)^8409*25000000000000^6361 ≤ 3842694937953^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2425353001 10000000000 3842694937953 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1254345069/2500000000 : ℝ)^8409 ≤ (10045742039567/25000000000000 : ℝ)^6361 := by
    have hnat : (1254345069 : ℕ)^8409*25000000000000^6361 ≤ 10045742039567^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1254345069 2500000000 10045742039567 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541507399/1000000000 : ℝ), (-2425353001/10000000000 : ℝ), (1254345069/2500000000 : ℝ)] ![(8889250417337/20000000000000 : ℝ), (3842694937953/25000000000000 : ℝ), (10045742039567/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541507399/1000000000 : ℝ)|^8409 ≤ (8889250417337/20000000000000 : ℝ)^6361
        have hw : |(541507399/1000000000 : ℝ)|=(541507399/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2425353001/10000000000 : ℝ)|^8409 ≤ (3842694937953/25000000000000 : ℝ)^6361
        have hw : |(-2425353001/10000000000 : ℝ)|=(2425353001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1254345069/2500000000 : ℝ)|^8409 ≤ (10045742039567/25000000000000 : ℝ)^6361
        have hw : |(1254345069/2500000000 : ℝ)|=(1254345069/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s1_2 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (541507397/1000000000 : ℝ)*x 0 + (1003476063/2000000000 : ℝ)*x 1 + (-151584561/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (541507397/1000000000 : ℝ)^8409 ≤ (1777850074787/4000000000000 : ℝ)^6361 := by
    have hnat : (541507397 : ℕ)^8409*4000000000000^6361 ≤ 1777850074787^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541507397 1000000000 1777850074787 4000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003476063/2000000000 : ℝ)^8409 ≤ (10045742142793/25000000000000 : ℝ)^6361 := by
    have hnat : (1003476063 : ℕ)^8409*25000000000000^6361 ≤ 10045742142793^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003476063 2000000000 10045742142793 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (151584561/625000000 : ℝ)^8409 ≤ (7685389771181/50000000000000 : ℝ)^6361 := by
    have hnat : (151584561 : ℕ)^8409*50000000000000^6361 ≤ 7685389771181^6361*625000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151584561 625000000 7685389771181 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(541507397/1000000000 : ℝ), (1003476063/2000000000 : ℝ), (-151584561/625000000 : ℝ)] ![(1777850074787/4000000000000 : ℝ), (10045742142793/25000000000000 : ℝ), (7685389771181/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(541507397/1000000000 : ℝ)|^8409 ≤ (1777850074787/4000000000000 : ℝ)^6361
        have hw : |(541507397/1000000000 : ℝ)|=(541507397/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003476063/2000000000 : ℝ)|^8409 ≤ (10045742142793/25000000000000 : ℝ)^6361
        have hw : |(1003476063/2000000000 : ℝ)|=(1003476063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-151584561/625000000 : ℝ)|^8409 ≤ (7685389771181/50000000000000 : ℝ)^6361
        have hw : |(-151584561/625000000 : ℝ)|=(151584561/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s1_3 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1077776431/2500000000 : ℝ)*x 0 + (922681087/2500000000 : ℝ)*x 1 + (5032568073/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077776431/2500000000 : ℝ)^8409 ≤ (4110078731331/12500000000000 : ℝ)^6361 := by
    have hnat : (1077776431 : ℕ)^8409*12500000000000^6361 ≤ 4110078731331^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077776431 2500000000 4110078731331 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (922681087/2500000000 : ℝ)^8409 ≤ (26775526372511/100000000000000 : ℝ)^6361 := by
    have hnat : (922681087 : ℕ)^8409*100000000000000^6361 ≤ 26775526372511^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      922681087 2500000000 26775526372511 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5032568073/10000000000 : ℝ)^8409 ≤ (1613753750177/4000000000000 : ℝ)^6361 := by
    have hnat : (5032568073 : ℕ)^8409*4000000000000^6361 ≤ 1613753750177^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5032568073 10000000000 1613753750177 4000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077776431/2500000000 : ℝ), (922681087/2500000000 : ℝ), (5032568073/10000000000 : ℝ)] ![(4110078731331/12500000000000 : ℝ), (26775526372511/100000000000000 : ℝ), (1613753750177/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077776431/2500000000 : ℝ)|^8409 ≤ (4110078731331/12500000000000 : ℝ)^6361
        have hw : |(1077776431/2500000000 : ℝ)|=(1077776431/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(922681087/2500000000 : ℝ)|^8409 ≤ (26775526372511/100000000000000 : ℝ)^6361
        have hw : |(922681087/2500000000 : ℝ)|=(922681087/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5032568073/10000000000 : ℝ)|^8409 ≤ (1613753750177/4000000000000 : ℝ)^6361
        have hw : |(5032568073/10000000000 : ℝ)|=(5032568073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s1_4 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1034306891/5000000000 : ℝ)*x 0 + (2513100259/5000000000 : ℝ)*x 1 + (5673200817/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1034306891/5000000000 : ℝ)^8409 ≤ (6227650388767/50000000000000 : ℝ)^6361 := by
    have hnat : (1034306891 : ℕ)^8409*50000000000000^6361 ≤ 6227650388767^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034306891 5000000000 6227650388767 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2513100259/5000000000 : ℝ)^8409 ≤ (10069094212513/25000000000000 : ℝ)^6361 := by
    have hnat : (2513100259 : ℕ)^8409*25000000000000^6361 ≤ 10069094212513^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513100259 5000000000 10069094212513 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5673200817/10000000000 : ℝ)^8409 ≤ (11817080590667/25000000000000 : ℝ)^6361 := by
    have hnat : (5673200817 : ℕ)^8409*25000000000000^6361 ≤ 11817080590667^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5673200817 10000000000 11817080590667 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1034306891/5000000000 : ℝ), (2513100259/5000000000 : ℝ), (5673200817/10000000000 : ℝ)] ![(6227650388767/50000000000000 : ℝ), (10069094212513/25000000000000 : ℝ), (11817080590667/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1034306891/5000000000 : ℝ)|^8409 ≤ (6227650388767/50000000000000 : ℝ)^6361
        have hw : |(-1034306891/5000000000 : ℝ)|=(1034306891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2513100259/5000000000 : ℝ)|^8409 ≤ (10069094212513/25000000000000 : ℝ)^6361
        have hw : |(2513100259/5000000000 : ℝ)|=(2513100259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5673200817/10000000000 : ℝ)|^8409 ≤ (11817080590667/25000000000000 : ℝ)^6361
        have hw : |(5673200817/10000000000 : ℝ)|=(5673200817/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s1_5 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (655501401/1250000000 : ℝ)*x 0 + (-1769536557/10000000000 : ℝ)*x 1 + (11080461/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655501401/1250000000 : ℝ)^8409 ≤ (8519928593831/20000000000000 : ℝ)^6361 := by
    have hnat : (655501401 : ℕ)^8409*20000000000000^6361 ≤ 8519928593831^6361*1250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655501401 1250000000 8519928593831 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1769536557/10000000000 : ℝ)^8409 ≤ (2533021838963/25000000000000 : ℝ)^6361 := by
    have hnat : (1769536557 : ℕ)^8409*25000000000000^6361 ≤ 2533021838963^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769536557 10000000000 2533021838963 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (11080461/19531250 : ℝ)^8409 ≤ (23634134829377/50000000000000 : ℝ)^6361 := by
    have hnat : (11080461 : ℕ)^8409*50000000000000^6361 ≤ 23634134829377^6361*19531250^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11080461 19531250 23634134829377 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655501401/1250000000 : ℝ), (-1769536557/10000000000 : ℝ), (11080461/19531250 : ℝ)] ![(8519928593831/20000000000000 : ℝ), (2533021838963/25000000000000 : ℝ), (23634134829377/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655501401/1250000000 : ℝ)|^8409 ≤ (8519928593831/20000000000000 : ℝ)^6361
        have hw : |(655501401/1250000000 : ℝ)|=(655501401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1769536557/10000000000 : ℝ)|^8409 ≤ (2533021838963/25000000000000 : ℝ)^6361
        have hw : |(-1769536557/10000000000 : ℝ)|=(1769536557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(11080461/19531250 : ℝ)|^8409 ≤ (23634134829377/50000000000000 : ℝ)^6361
        have hw : |(11080461/19531250 : ℝ)|=(11080461/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s1_6 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5244011359/10000000000 : ℝ)*x 0 + (1418299119/2500000000 : ℝ)*x 1 + (-1769535697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5244011359/10000000000 : ℝ)^8409 ≤ (21299822295367/50000000000000 : ℝ)^6361 := by
    have hnat : (5244011359 : ℕ)^8409*50000000000000^6361 ≤ 21299822295367^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244011359 10000000000 21299822295367 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1418299119/2500000000 : ℝ)^8409 ≤ (47268274549147/100000000000000 : ℝ)^6361 := by
    have hnat : (1418299119 : ℕ)^8409*100000000000000^6361 ≤ 47268274549147^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1418299119 2500000000 47268274549147 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1769535697/10000000000 : ℝ)^8409 ≤ (2026416169243/20000000000000 : ℝ)^6361 := by
    have hnat : (1769535697 : ℕ)^8409*20000000000000^6361 ≤ 2026416169243^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1769535697 10000000000 2026416169243 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5244011359/10000000000 : ℝ), (1418299119/2500000000 : ℝ), (-1769535697/10000000000 : ℝ)] ![(21299822295367/50000000000000 : ℝ), (47268274549147/100000000000000 : ℝ), (2026416169243/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5244011359/10000000000 : ℝ)|^8409 ≤ (21299822295367/50000000000000 : ℝ)^6361
        have hw : |(5244011359/10000000000 : ℝ)|=(5244011359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1418299119/2500000000 : ℝ)|^8409 ≤ (47268274549147/100000000000000 : ℝ)^6361
        have hw : |(1418299119/2500000000 : ℝ)|=(1418299119/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1769535697/10000000000 : ℝ)|^8409 ≤ (2026416169243/20000000000000 : ℝ)^6361
        have hw : |(-1769535697/10000000000 : ℝ)|=(1769535697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s1_7 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4312533361/10000000000 : ℝ)*x 0 + (626845153/1250000000 : ℝ)*x 1 + (74177487/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4312533361/10000000000 : ℝ)^8409 ≤ (16447512420137/50000000000000 : ℝ)^6361 := by
    have hnat : (4312533361 : ℕ)^8409*50000000000000^6361 ≤ 16447512420137^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4312533361 10000000000 16447512420137 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (626845153/1250000000 : ℝ)^8409 ≤ (401552418803/1000000000000 : ℝ)^6361 := by
    have hnat : (626845153 : ℕ)^8409*1000000000000^6361 ≤ 401552418803^6361*1250000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      626845153 1250000000 401552418803 1000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74177487/200000000 : ℝ)^8409 ≤ (5389946653389/20000000000000 : ℝ)^6361 := by
    have hnat : (74177487 : ℕ)^8409*20000000000000^6361 ≤ 5389946653389^6361*200000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74177487 200000000 5389946653389 20000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4312533361/10000000000 : ℝ), (626845153/1250000000 : ℝ), (74177487/200000000 : ℝ)] ![(16447512420137/50000000000000 : ℝ), (401552418803/1000000000000 : ℝ), (5389946653389/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4312533361/10000000000 : ℝ)|^8409 ≤ (16447512420137/50000000000000 : ℝ)^6361
        have hw : |(4312533361/10000000000 : ℝ)|=(4312533361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(626845153/1250000000 : ℝ)|^8409 ≤ (401552418803/1000000000000 : ℝ)^6361
        have hw : |(626845153/1250000000 : ℝ)|=(626845153/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(74177487/200000000 : ℝ)|^8409 ≤ (5389946653389/20000000000000 : ℝ)^6361
        have hw : |(74177487/200000000 : ℝ)|=(74177487/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1216_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13767/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (357/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (3027/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2011/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13767/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (357/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13767/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (357/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13767/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (357/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13767/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (357/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13767/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (357/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13767/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (357/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (357/50000 : ℝ) ^ (1051/256 : ℝ) ≤ (77160509151/50000000000000000000 : ℝ) := by
    have hpowers : (357/50000 : ℝ)^1051 ≤ (77160509151/50000000000000000000 : ℝ)^256 := by
      have hnat : (357 : ℕ)^1051*50000000000000000000^256 ≤ 77160509151^256*50000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        357 50000 77160509151 50000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (357/50000 : ℝ)) (X := (77160509151/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hpowhi : (13767/50000 : ℝ) ^ (1051/256 : ℝ) ≤ (31353134516310401/6250000000000000000 : ℝ) := by
    have hpowers : (13767/50000 : ℝ)^1051 ≤ (31353134516310401/6250000000000000000 : ℝ)^256 := by
      have hnat : (13767 : ℕ)^1051*6250000000000000000^256 ≤ 31353134516310401^256*50000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13767 50000 31353134516310401 6250000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13767/50000 : ℝ)) (X := (31353134516310401/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000077160509151/25000000000000000000 : ℝ) ≤ (10000000007517827/10000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (25000000077160509151/25000000000000000000 : ℝ)^256 ≤ (10000000007517827/10000000000000000 : ℝ)^1051 := by
      have hnat : (25000000077160509151 : ℕ)^256*10000000000000000^1051 ≤ 10000000007517827^1051*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000077160509151 25000000000000000000 10000000007517827 10000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000007517827/10000000000000000 : ℝ)) (X := (25000000077160509151/25000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50250825153290992359/50000000000000000000 : ℝ) ≤ (5006097979826909/5000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (50250825153290992359/50000000000000000000 : ℝ)^256 ≤ (5006097979826909/5000000000000000 : ℝ)^1051 := by
      have hnat : (50250825153290992359 : ℕ)^256*5000000000000000^1051 ≤ 5006097979826909^1051*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50250825153290992359 50000000000000000000 5006097979826909 5000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5006097979826909/5000000000000000 : ℝ)) (X := (50250825153290992359/50000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (3156353134516310401/3125000000000000000 : ℝ) ≤ (10024391911789809/10000000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (3156353134516310401/3125000000000000000 : ℝ)^256 ≤ (10024391911789809/10000000000000000 : ℝ)^1051 := by
      have hnat : (3156353134516310401 : ℕ)^256*10000000000000000^1051 ≤ 10024391911789809^1051*3125000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3156353134516310401 3125000000000000000 10024391911789809 10000000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10024391911789809/10000000000000000 : ℝ)) (X := (3156353134516310401/3125000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(77160509151/50000000000000000000 : ℝ) ≤ ((698392146828067513/698437500000000000 : ℝ)+2*(12195952135991/2682000000000000 : ℝ)*(357/50000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (698392146828067513/698437500000000000 : ℝ)+2*(12195952135991/2682000000000000 : ℝ)*(357/50000 : ℝ)=(10000000007517827/10000000000000000 : ℝ) by norm_num, show 1+2*(77160509151/50000000000000000000 : ℝ)=(25000000077160509151/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31353134516310401/6250000000000000000 : ℝ)+(77160509151/50000000000000000000 : ℝ) ≤ ((698392146828067513/698437500000000000 : ℝ)+(12195952135991/2682000000000000 : ℝ)*((13767/50000 : ℝ)+(357/50000 : ℝ)))^(1051/256 : ℝ) := by
    rw [show (698392146828067513/698437500000000000 : ℝ)+(12195952135991/2682000000000000 : ℝ)*((13767/50000 : ℝ)+(357/50000 : ℝ))=(5006097979826909/5000000000000000 : ℝ) by norm_num, show 1+(31353134516310401/6250000000000000000 : ℝ)+(77160509151/50000000000000000000 : ℝ)=(50250825153290992359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31353134516310401/6250000000000000000 : ℝ) ≤ ((698392146828067513/698437500000000000 : ℝ)+2*(12195952135991/2682000000000000 : ℝ)*(13767/50000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (698392146828067513/698437500000000000 : ℝ)+2*(12195952135991/2682000000000000 : ℝ)*(13767/50000 : ℝ)=(10024391911789809/10000000000000000 : ℝ) by norm_num, show 1+2*(31353134516310401/6250000000000000000 : ℝ)=(3156353134516310401/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (698392146828067513/698437500000000000 : ℝ)*(X 1 0+X 2 0)+(12195952135991/2682000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (357/50000 : ℝ)) (hi := (13767/50000 : ℝ)) (c := (698392146828067513/698437500000000000 : ℝ)) (alpha := (12195952135991/2682000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (698392146828067513/698437500000000000 : ℝ)*(X 0 1+X 2 1)+(12195952135991/2682000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (357/50000 : ℝ)) (hi := (13767/50000 : ℝ)) (c := (698392146828067513/698437500000000000 : ℝ)) (alpha := (12195952135991/2682000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (698392146828067513/698437500000000000 : ℝ)*(X 0 2+X 1 2)+(12195952135991/2682000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (357/50000 : ℝ)) (hi := (13767/50000 : ℝ)) (c := (698392146828067513/698437500000000000 : ℝ)) (alpha := (12195952135991/2682000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2067908769/10000000000 : ℝ)*X 0 0+(1420547133/2500000000 : ℝ)*X 0 1+(5017380321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((541507399/1000000000 : ℝ)*X 1 0+(-2425353001/10000000000 : ℝ)*X 1 1+(1254345069/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((541507397/1000000000 : ℝ)*X 2 0+(1003476063/2000000000 : ℝ)*X 2 1+(-151584561/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1077776431/2500000000 : ℝ)*X 0 0+(922681087/2500000000 : ℝ)*X 0 1+(5032568073/10000000000 : ℝ)*X 0 2+(1077776431/2500000000 : ℝ)*X 1 0+(922681087/2500000000 : ℝ)*X 1 1+(5032568073/10000000000 : ℝ)*X 1 2+(1077776431/2500000000 : ℝ)*X 2 0+(922681087/2500000000 : ℝ)*X 2 1+(5032568073/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1034306891/5000000000 : ℝ)*X 0 0+(2513100259/5000000000 : ℝ)*X 0 1+(5673200817/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((655501401/1250000000 : ℝ)*X 1 0+(-1769536557/10000000000 : ℝ)*X 1 1+(11080461/19531250 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5244011359/10000000000 : ℝ)*X 2 0+(1418299119/2500000000 : ℝ)*X 2 1+(-1769535697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4312533361/10000000000 : ℝ)*X 0 0+(626845153/1250000000 : ℝ)*X 0 1+(74177487/200000000 : ℝ)*X 0 2+(4312533361/10000000000 : ℝ)*X 1 0+(626845153/1250000000 : ℝ)*X 1 1+(74177487/200000000 : ℝ)*X 1 2+(4312533361/10000000000 : ℝ)*X 2 0+(626845153/1250000000 : ℝ)*X 2 1+(74177487/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24794982204020076015133/11175000000000000000000000000 : ℝ) := by norm_num
    linear_combination (33798229/100000000000000 : ℝ)*(base1) + (252884923/50000000000000 : ℝ)*(base19) + (125053563/25000000000000 : ℝ)*(base23) + (11181009/20000000000000 : ℝ)*(upper3) + (63510399/100000000000000 : ℝ)*(upper5) + (281180562519863/25000000000000 : ℝ)*(major0) + (281180562519863/25000000000000 : ℝ)*(major1) + (281180562519863/25000000000000 : ℝ)*(major2) + (94012231548579/6250000000000 : ℝ)*(sp0) + (1504197793582171/100000000000000 : ℝ)*(sp1) + (752098899568883/50000000000000 : ℝ)*(sp2) + (372622339954179/50000000000000 : ℝ)*(sp3) + (2628372983/100000000000000 : ℝ)*(sp4) + (176642577/12500000000000 : ℝ)*(sp7) + (372623063423601/50000000000000 : ℝ)*(f.failure) + (752099149676009/50000000000000 : ℝ)*(f.sum) + (6376263447917/33525000000000000000000000000 : ℝ)*base66 + (32352433637419253/209531250000000000000000000000000 : ℝ)*base67 + (1927662884212424497/209531250000000000000000000000000 : ℝ)*base70 + (23206887392419253/209531250000000000000000000000000 : ℝ)*base71 + (9616764269351/4190625000000000000000000000 : ℝ)*base73 + (263507995899919253/209531250000000000000000000000000 : ℝ)*base75 + (396006209002893247/209531250000000000000000000000000 : ℝ)*base78 + (1085399279326330747/209531250000000000000000000000000 : ℝ)*base80 + (197284720316717/33525000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (922843/500000000000000000000 : ℝ)*base90 + (922843/500000000000000000000 : ℝ)*base92 + (922843/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (57436325433115186184064143/8730468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (206987617/50000000000000 : ℝ)*(base19) + (1368451557/100000000000000 : ℝ)*(base23) + (7167937/100000000000000 : ℝ)*(lower2) + (14056383/10000000000000 : ℝ)*(lower3) + (80150257/20000000000000 : ℝ)*(lower4) + (577842279568201/50000000000000 : ℝ)*(major0) + (577842279568201/50000000000000 : ℝ)*(major1) + (577842279568201/50000000000000 : ℝ)*(major2) + (3201258239/50000000000000 : ℝ)*(sp0) + (4887477169/100000000000000 : ℝ)*(sp2) + (1545600601475981/100000000000000 : ℝ)*(sp4) + (772803295008613/50000000000000 : ℝ)*(sp5) + (1545600748063733/100000000000000 : ℝ)*(sp6) + (765761894985787/100000000000000 : ℝ)*(sp7) + (765761894985787/100000000000000 : ℝ)*(f.failure) + (1545607003992459/100000000000000 : ℝ)*(f.sum) + (104257798842041/67050000000000000000000000000 : ℝ)*base65 + (1207336476178921231/419062500000000000000000000000000 : ℝ)*base67 + (437745953540483731/419062500000000000000000000000000 : ℝ)*base69 + (464130233306108731/419062500000000000000000000000000 : ℝ)*base71 + (150159020399891/67050000000000000000000000000 : ℝ)*base73 + (3310492079614828769/419062500000000000000000000000000 : ℝ)*base76 + (2193992965328296231/419062500000000000000000000000000 : ℝ)*base77 + (18543977907555141269/419062500000000000000000000000000 : ℝ)*base80 + (578412260393059/67050000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (6984841/1000000000000000000000 : ℝ)*base90 + (6984841/1000000000000000000000 : ℝ)*base92 + (6984841/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1216_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13767/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (357/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3027/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2011/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1216_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1216_s2_0 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2117265347/10000000000 : ℝ)*x 0 + (5497284131/10000000000 : ℝ)*x 1 + (5170831877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2117265347/10000000000 : ℝ)^8409 ≤ (3211002116779/25000000000000 : ℝ)^6361 := by
    have hnat : (2117265347 : ℕ)^8409*25000000000000^6361 ≤ 3211002116779^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117265347 10000000000 3211002116779 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5497284131/10000000000 : ℝ)^8409 ≤ (22670222884259/50000000000000 : ℝ)^6361 := by
    have hnat : (5497284131 : ℕ)^8409*50000000000000^6361 ≤ 22670222884259^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5497284131 10000000000 22670222884259 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170831877/10000000000 : ℝ)^8409 ≤ (41815545750479/100000000000000 : ℝ)^6361 := by
    have hnat : (5170831877 : ℕ)^8409*100000000000000^6361 ≤ 41815545750479^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170831877 10000000000 41815545750479 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2117265347/10000000000 : ℝ), (5497284131/10000000000 : ℝ), (5170831877/10000000000 : ℝ)] ![(3211002116779/25000000000000 : ℝ), (22670222884259/50000000000000 : ℝ), (41815545750479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2117265347/10000000000 : ℝ)|^8409 ≤ (3211002116779/25000000000000 : ℝ)^6361
        have hw : |(-2117265347/10000000000 : ℝ)|=(2117265347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5497284131/10000000000 : ℝ)|^8409 ≤ (22670222884259/50000000000000 : ℝ)^6361
        have hw : |(5497284131/10000000000 : ℝ)|=(5497284131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170831877/10000000000 : ℝ)|^8409 ≤ (41815545750479/100000000000000 : ℝ)^6361
        have hw : |(5170831877/10000000000 : ℝ)|=(5170831877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s2_1 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370750223/10000000000 : ℝ)*x 0 + (-71453767/312500000 : ℝ)*x 1 + (5170831811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370750223/10000000000 : ℝ)^8409 ≤ (343483999939/781250000000 : ℝ)^6361 := by
    have hnat : (5370750223 : ℕ)^8409*781250000000^6361 ≤ 343483999939^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370750223 10000000000 343483999939 781250000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (71453767/312500000 : ℝ)^8409 ≤ (14218502944553/100000000000000 : ℝ)^6361 := by
    have hnat : (71453767 : ℕ)^8409*100000000000000^6361 ≤ 14218502944553^6361*312500000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      71453767 312500000 14218502944553 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5170831811/10000000000 : ℝ)^8409 ≤ (41815545044909/100000000000000 : ℝ)^6361 := by
    have hnat : (5170831811 : ℕ)^8409*100000000000000^6361 ≤ 41815545044909^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170831811 10000000000 41815545044909 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370750223/10000000000 : ℝ), (-71453767/312500000 : ℝ), (5170831811/10000000000 : ℝ)] ![(343483999939/781250000000 : ℝ), (14218502944553/100000000000000 : ℝ), (41815545044909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370750223/10000000000 : ℝ)|^8409 ≤ (343483999939/781250000000 : ℝ)^6361
        have hw : |(5370750223/10000000000 : ℝ)|=(5370750223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-71453767/312500000 : ℝ)|^8409 ≤ (14218502944553/100000000000000 : ℝ)^6361
        have hw : |(-71453767/312500000 : ℝ)|=(71453767/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5170831811/10000000000 : ℝ)|^8409 ≤ (41815545044909/100000000000000 : ℝ)^6361
        have hw : |(5170831811/10000000000 : ℝ)|=(5170831811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s2_2 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5370750023/10000000000 : ℝ)*x 0 + (5170831989/10000000000 : ℝ)*x 1 + (-8931721/39062500 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5370750023/10000000000 : ℝ)^8409 ≤ (10991487456957/25000000000000 : ℝ)^6361 := by
    have hnat : (5370750023 : ℕ)^8409*25000000000000^6361 ≤ 10991487456957^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5370750023 10000000000 10991487456957 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5170831989/10000000000 : ℝ)^8409 ≤ (4181554694781/10000000000000 : ℝ)^6361 := by
    have hnat : (5170831989 : ℕ)^8409*10000000000000^6361 ≤ 4181554694781^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170831989 10000000000 4181554694781 10000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (8931721/39062500 : ℝ)^8409 ≤ (14218503207609/100000000000000 : ℝ)^6361 := by
    have hnat : (8931721 : ℕ)^8409*100000000000000^6361 ≤ 14218503207609^6361*39062500^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8931721 39062500 14218503207609 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5370750023/10000000000 : ℝ), (5170831989/10000000000 : ℝ), (-8931721/39062500 : ℝ)] ![(10991487456957/25000000000000 : ℝ), (4181554694781/10000000000000 : ℝ), (14218503207609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5370750023/10000000000 : ℝ)|^8409 ≤ (10991487456957/25000000000000 : ℝ)^6361
        have hw : |(5370750023/10000000000 : ℝ)|=(5370750023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5170831989/10000000000 : ℝ)|^8409 ≤ (4181554694781/10000000000000 : ℝ)^6361
        have hw : |(5170831989/10000000000 : ℝ)|=(5170831989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-8931721/39062500 : ℝ)|^8409 ≤ (14218503207609/100000000000000 : ℝ)^6361
        have hw : |(-8931721/39062500 : ℝ)|=(8931721/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s2_3 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (869028297/2000000000 : ℝ)*x 0 + (402785593/1000000000 : ℝ)*x 1 + (2343382317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (869028297/2000000000 : ℝ)^8409 ≤ (265793859999/800000000000 : ℝ)^6361 := by
    have hnat : (869028297 : ℕ)^8409*800000000000^6361 ≤ 265793859999^6361*2000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      869028297 2000000000 265793859999 800000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (402785593/1000000000 : ℝ)^8409 ≤ (3756927123151/12500000000000 : ℝ)^6361 := by
    have hnat : (402785593 : ℕ)^8409*12500000000000^6361 ≤ 3756927123151^6361*1000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      402785593 1000000000 3756927123151 12500000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2343382317/5000000000 : ℝ)^8409 ≤ (1836017524917/5000000000000 : ℝ)^6361 := by
    have hnat : (2343382317 : ℕ)^8409*5000000000000^6361 ≤ 1836017524917^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2343382317 5000000000 1836017524917 5000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(869028297/2000000000 : ℝ), (402785593/1000000000 : ℝ), (2343382317/5000000000 : ℝ)] ![(265793859999/800000000000 : ℝ), (3756927123151/12500000000000 : ℝ), (1836017524917/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(869028297/2000000000 : ℝ)|^8409 ≤ (265793859999/800000000000 : ℝ)^6361
        have hw : |(869028297/2000000000 : ℝ)|=(869028297/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(402785593/1000000000 : ℝ)|^8409 ≤ (3756927123151/12500000000000 : ℝ)^6361
        have hw : |(402785593/1000000000 : ℝ)|=(402785593/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2343382317/5000000000 : ℝ)|^8409 ≤ (1836017524917/5000000000000 : ℝ)^6361
        have hw : |(2343382317/5000000000 : ℝ)|=(2343382317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s2_4 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-529337341/2500000000 : ℝ)*x 0 + (1293242179/2500000000 : ℝ)*x 1 + (5495126927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529337341/2500000000 : ℝ)^8409 ≤ (12844682241033/100000000000000 : ℝ)^6361 := by
    have hnat : (529337341 : ℕ)^8409*100000000000000^6361 ≤ 12844682241033^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529337341 2500000000 12844682241033 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1293242179/2500000000 : ℝ)^8409 ≤ (20919195528727/50000000000000 : ℝ)^6361 := by
    have hnat : (1293242179 : ℕ)^8409*50000000000000^6361 ≤ 20919195528727^6361*2500000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293242179 2500000000 20919195528727 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5495126927/10000000000 : ℝ)^8409 ≤ (22658463344053/50000000000000 : ℝ)^6361 := by
    have hnat : (5495126927 : ℕ)^8409*50000000000000^6361 ≤ 22658463344053^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495126927 10000000000 22658463344053 50000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-529337341/2500000000 : ℝ), (1293242179/2500000000 : ℝ), (5495126927/10000000000 : ℝ)] ![(12844682241033/100000000000000 : ℝ), (20919195528727/50000000000000 : ℝ), (22658463344053/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-529337341/2500000000 : ℝ)|^8409 ≤ (12844682241033/100000000000000 : ℝ)^6361
        have hw : |(-529337341/2500000000 : ℝ)|=(529337341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1293242179/2500000000 : ℝ)|^8409 ≤ (20919195528727/50000000000000 : ℝ)^6361
        have hw : |(1293242179/2500000000 : ℝ)|=(1293242179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5495126927/10000000000 : ℝ)|^8409 ≤ (22658463344053/50000000000000 : ℝ)^6361
        have hw : |(5495126927/10000000000 : ℝ)|=(5495126927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s2_5 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287518949/10000000000 : ℝ)*x 0 + (-1962225279/10000000000 : ℝ)*x 1 + (5495126959/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287518949/10000000000 : ℝ)^8409 ≤ (43067492733583/100000000000000 : ℝ)^6361 := by
    have hnat : (5287518949 : ℕ)^8409*100000000000000^6361 ≤ 43067492733583^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287518949 10000000000 43067492733583 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1962225279/10000000000 : ℝ)^8409 ≤ (11615580212329/100000000000000 : ℝ)^6361 := by
    have hnat : (1962225279 : ℕ)^8409*100000000000000^6361 ≤ 11615580212329^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962225279 10000000000 11615580212329 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5495126959/10000000000 : ℝ)^8409 ≤ (45316927036967/100000000000000 : ℝ)^6361 := by
    have hnat : (5495126959 : ℕ)^8409*100000000000000^6361 ≤ 45316927036967^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5495126959 10000000000 45316927036967 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287518949/10000000000 : ℝ), (-1962225279/10000000000 : ℝ), (5495126959/10000000000 : ℝ)] ![(43067492733583/100000000000000 : ℝ), (11615580212329/100000000000000 : ℝ), (45316927036967/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287518949/10000000000 : ℝ)|^8409 ≤ (43067492733583/100000000000000 : ℝ)^6361
        have hw : |(5287518949/10000000000 : ℝ)|=(5287518949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1962225279/10000000000 : ℝ)|^8409 ≤ (11615580212329/100000000000000 : ℝ)^6361
        have hw : |(-1962225279/10000000000 : ℝ)|=(1962225279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5495126959/10000000000 : ℝ)|^8409 ≤ (45316927036967/100000000000000 : ℝ)^6361
        have hw : |(5495126959/10000000000 : ℝ)|=(5495126959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s2_6 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5287519131/10000000000 : ℝ)*x 0 + (2747563499/5000000000 : ℝ)*x 1 + (-78488999/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5287519131/10000000000 : ℝ)^8409 ≤ (10766873673319/25000000000000 : ℝ)^6361 := by
    have hnat : (5287519131 : ℕ)^8409*25000000000000^6361 ≤ 10766873673319^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5287519131 10000000000 10766873673319 25000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2747563499/5000000000 : ℝ)^8409 ≤ (2265846373107/5000000000000 : ℝ)^6361 := by
    have hnat : (2747563499 : ℕ)^8409*5000000000000^6361 ≤ 2265846373107^6361*5000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2747563499 5000000000 2265846373107 5000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (78488999/400000000 : ℝ)^8409 ≤ (11615577833383/100000000000000 : ℝ)^6361 := by
    have hnat : (78488999 : ℕ)^8409*100000000000000^6361 ≤ 11615577833383^6361*400000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78488999 400000000 11615577833383 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5287519131/10000000000 : ℝ), (2747563499/5000000000 : ℝ), (-78488999/400000000 : ℝ)] ![(10766873673319/25000000000000 : ℝ), (2265846373107/5000000000000 : ℝ), (11615577833383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5287519131/10000000000 : ℝ)|^8409 ≤ (10766873673319/25000000000000 : ℝ)^6361
        have hw : |(5287519131/10000000000 : ℝ)|=(5287519131/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2747563499/5000000000 : ℝ)|^8409 ≤ (2265846373107/5000000000000 : ℝ)^6361
        have hw : |(2747563499/5000000000 : ℝ)|=(2747563499/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-78488999/400000000 : ℝ)|^8409 ≤ (11615577833383/100000000000000 : ℝ)^6361
        have hw : |(-78488999/400000000 : ℝ)|=(78488999/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1216_s2_7 (p : ℝ) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4345310557/10000000000 : ℝ)*x 0 + (4682451769/10000000000 : ℝ)*x 1 + (252013107/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4345310557/10000000000 : ℝ)^8409 ≤ (33225941509081/100000000000000 : ℝ)^6361 := by
    have hnat : (4345310557 : ℕ)^8409*100000000000000^6361 ≤ 33225941509081^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4345310557 10000000000 33225941509081 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4682451769/10000000000 : ℝ)^8409 ≤ (1146115214237/3125000000000 : ℝ)^6361 := by
    have hnat : (4682451769 : ℕ)^8409*3125000000000^6361 ≤ 1146115214237^6361*10000000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4682451769 10000000000 1146115214237 3125000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (252013107/625000000 : ℝ)^8409 ≤ (30098371618061/100000000000000 : ℝ)^6361 := by
    have hnat : (252013107 : ℕ)^8409*100000000000000^6361 ≤ 30098371618061^6361*625000000^8409 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      252013107 625000000 30098371618061 100000000000000 8409 6361 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8409/2048 : ℝ)) 8409 6361 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4345310557/10000000000 : ℝ), (4682451769/10000000000 : ℝ), (252013107/625000000 : ℝ)] ![(33225941509081/100000000000000 : ℝ), (1146115214237/3125000000000 : ℝ), (30098371618061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4345310557/10000000000 : ℝ)|^8409 ≤ (33225941509081/100000000000000 : ℝ)^6361
        have hw : |(4345310557/10000000000 : ℝ)|=(4345310557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4682451769/10000000000 : ℝ)|^8409 ≤ (1146115214237/3125000000000 : ℝ)^6361
        have hw : |(4682451769/10000000000 : ℝ)|=(4682451769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(252013107/625000000 : ℝ)|^8409 ≤ (30098371618061/100000000000000 : ℝ)^6361
        have hw : |(252013107/625000000 : ℝ)|=(252013107/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1216_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2011/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3027/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (587/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4073/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2011/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3027/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2011/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3027/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2011/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3027/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2011/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3027/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2011/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3027/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2011/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3027/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3027/50000 : ℝ) ^ (1051/256 : ℝ) ≤ (999339842605299/100000000000000000000 : ℝ) := by
    have hpowers : (3027/50000 : ℝ)^1051 ≤ (999339842605299/100000000000000000000 : ℝ)^256 := by
      have hnat : (3027 : ℕ)^1051*100000000000000000000^256 ≤ 999339842605299^256*50000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3027 50000 999339842605299 100000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3027/50000 : ℝ)) (X := (999339842605299/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2011/10000 : ℝ) ^ (1051/256 : ℝ) ≤ (69047829077896471/50000000000000000000 : ℝ) := by
    have hpowers : (2011/10000 : ℝ)^1051 ≤ (69047829077896471/50000000000000000000 : ℝ)^256 := by
      have hnat : (2011 : ℕ)^1051*50000000000000000000^256 ≤ 69047829077896471^256*10000^1051 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2011 10000 69047829077896471 50000000000000000000 1051 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2011/10000 : ℝ)) (X := (69047829077896471/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000999339842605299/50000000000000000000 : ℝ) ≤ (2500012170745283/2500000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (50000999339842605299/50000000000000000000 : ℝ)^256 ≤ (2500012170745283/2500000000000000 : ℝ)^1051 := by
      have hnat : (50000999339842605299 : ℕ)^256*2500000000000000^1051 ≤ 2500012170745283^1051*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000999339842605299 50000000000000000000 2500012170745283 2500000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500012170745283/2500000000000000 : ℝ)) (X := (50000999339842605299/50000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100139094997998398241/100000000000000000000 : ℝ) ≤ (1250423282613657/1250000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (100139094997998398241/100000000000000000000 : ℝ)^256 ≤ (1250423282613657/1250000000000000 : ℝ)^1051 := by
      have hnat : (100139094997998398241 : ℕ)^256*1250000000000000^1051 ≤ 1250423282613657^1051*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100139094997998398241 100000000000000000000 1250423282613657 1250000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250423282613657/1250000000000000 : ℝ)) (X := (100139094997998398241/100000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (25069047829077896471/25000000000000000000 : ℝ) ≤ (500336191941869/500000000000000 : ℝ) ^ (1051/256 : ℝ) := by
    have hpowers : (25069047829077896471/25000000000000000000 : ℝ)^256 ≤ (500336191941869/500000000000000 : ℝ)^1051 := by
      have hnat : (25069047829077896471 : ℕ)^256*500000000000000^1051 ≤ 500336191941869^1051*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25069047829077896471 25000000000000000000 500336191941869 500000000000000 256 1051 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500336191941869/500000000000000 : ℝ)) (X := (25069047829077896471/25000000000000000000 : ℝ)) (by norm_num) 1051 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(999339842605299/100000000000000000000 : ℝ) ≤ ((70260136447214533/70280000000000000 : ℝ)+2*(834394482031/351400000000000 : ℝ)*(3027/50000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (70260136447214533/70280000000000000 : ℝ)+2*(834394482031/351400000000000 : ℝ)*(3027/50000 : ℝ)=(2500012170745283/2500000000000000 : ℝ) by norm_num, show 1+2*(999339842605299/100000000000000000000 : ℝ)=(50000999339842605299/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(69047829077896471/50000000000000000000 : ℝ)+(999339842605299/100000000000000000000 : ℝ) ≤ ((70260136447214533/70280000000000000 : ℝ)+(834394482031/351400000000000 : ℝ)*((2011/10000 : ℝ)+(3027/50000 : ℝ)))^(1051/256 : ℝ) := by
    rw [show (70260136447214533/70280000000000000 : ℝ)+(834394482031/351400000000000 : ℝ)*((2011/10000 : ℝ)+(3027/50000 : ℝ))=(1250423282613657/1250000000000000 : ℝ) by norm_num, show 1+(69047829077896471/50000000000000000000 : ℝ)+(999339842605299/100000000000000000000 : ℝ)=(100139094997998398241/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(69047829077896471/50000000000000000000 : ℝ) ≤ ((70260136447214533/70280000000000000 : ℝ)+2*(834394482031/351400000000000 : ℝ)*(2011/10000 : ℝ))^(1051/256 : ℝ) := by
    rw [show (70260136447214533/70280000000000000 : ℝ)+2*(834394482031/351400000000000 : ℝ)*(2011/10000 : ℝ)=(500336191941869/500000000000000 : ℝ) by norm_num, show 1+2*(69047829077896471/50000000000000000000 : ℝ)=(25069047829077896471/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (70260136447214533/70280000000000000 : ℝ)*(X 1 0+X 2 0)+(834394482031/351400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (3027/50000 : ℝ)) (hi := (2011/10000 : ℝ)) (c := (70260136447214533/70280000000000000 : ℝ)) (alpha := (834394482031/351400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (70260136447214533/70280000000000000 : ℝ)*(X 0 1+X 2 1)+(834394482031/351400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (3027/50000 : ℝ)) (hi := (2011/10000 : ℝ)) (c := (70260136447214533/70280000000000000 : ℝ)) (alpha := (834394482031/351400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (70260136447214533/70280000000000000 : ℝ)*(X 0 2+X 1 2)+(834394482031/351400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1051/256 : ℝ)) (lo := (3027/50000 : ℝ)) (hi := (2011/10000 : ℝ)) (c := (70260136447214533/70280000000000000 : ℝ)) (alpha := (834394482031/351400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2117265347/10000000000 : ℝ)*X 0 0+(5497284131/10000000000 : ℝ)*X 0 1+(5170831877/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5370750223/10000000000 : ℝ)*X 1 0+(-71453767/312500000 : ℝ)*X 1 1+(5170831811/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5370750023/10000000000 : ℝ)*X 2 0+(5170831989/10000000000 : ℝ)*X 2 1+(-8931721/39062500 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((869028297/2000000000 : ℝ)*X 0 0+(402785593/1000000000 : ℝ)*X 0 1+(2343382317/5000000000 : ℝ)*X 0 2+(869028297/2000000000 : ℝ)*X 1 0+(402785593/1000000000 : ℝ)*X 1 1+(2343382317/5000000000 : ℝ)*X 1 2+(869028297/2000000000 : ℝ)*X 2 0+(402785593/1000000000 : ℝ)*X 2 1+(2343382317/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-529337341/2500000000 : ℝ)*X 0 0+(1293242179/2500000000 : ℝ)*X 0 1+(5495126927/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5287518949/10000000000 : ℝ)*X 1 0+(-1962225279/10000000000 : ℝ)*X 1 1+(5495126959/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5287519131/10000000000 : ℝ)*X 2 0+(2747563499/5000000000 : ℝ)*X 2 1+(-78488999/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4345310557/10000000000 : ℝ)*X 0 0+(4682451769/10000000000 : ℝ)*X 0 1+(252013107/625000000 : ℝ)*X 0 2+(4345310557/10000000000 : ℝ)*X 1 0+(4682451769/10000000000 : ℝ)*X 1 1+(252013107/625000000 : ℝ)*X 1 2+(4345310557/10000000000 : ℝ)*X 2 0+(4682451769/10000000000 : ℝ)*X 2 1+(252013107/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1216_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6685979717311977755836389/878500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (387772631/25000000000000 : ℝ)*(base19) + (1329286321/100000000000000 : ℝ)*(base23) + (28930089/50000000000000 : ℝ)*(lower2) + (49164353/20000000000000 : ℝ)*(upper3) + (108630089/100000000000000 : ℝ)*(upper5) + (1145236296142889/50000000000000 : ℝ)*(major0) + (1145236296142889/50000000000000 : ℝ)*(major1) + (1145236296142889/50000000000000 : ℝ)*(major2) + (306325238086953/10000000000000 : ℝ)*(sp0) + (1531632861940789/50000000000000 : ℝ)*(sp1) + (3063265945685781/100000000000000 : ℝ)*(sp2) + (379417163648889/25000000000000 : ℝ)*(sp3) + (3723525643/25000000000000 : ℝ)*(sp4) + (450065733/5000000000000 : ℝ)*(sp7) + (189709706988777/12500000000000 : ℝ)*(f.failure) + (1531633637486051/50000000000000 : ℝ)*(f.sum) + (13825179979389/8785000000000000000000000000 : ℝ)*base65 + (1787174775927091/502000000000000000000000000000 : ℝ)*base67 + (420551885824909/502000000000000000000000000000 : ℝ)*base70 + (3673915886783091/502000000000000000000000000000 : ℝ)*base71 + (13546018805979/8785000000000000000000000000 : ℝ)*base73 + (5442751034767091/502000000000000000000000000000 : ℝ)*base75 + (1873025490145091/502000000000000000000000000000 : ℝ)*base77 + (1869662197573091/502000000000000000000000000000 : ℝ)*base79 + (22107661052321/8785000000000000000000000000 : ℝ)*base82 + (533411/125000000000000000000 : ℝ)*base90 + (533411/125000000000000000000 : ℝ)*base92 + (533411/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6429011845961938736499081/1757000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (43170913/4000000000000 : ℝ)*(base19) + (1360913907/100000000000000 : ℝ)*(base23) + (47999807/100000000000000 : ℝ)*(upper2) + (6311199/4000000000000 : ℝ)*(upper3) + (73624051/100000000000000 : ℝ)*(upper5) + (1160488313288827/50000000000000 : ℝ)*(major0) + (1160488313288827/50000000000000 : ℝ)*(major1) + (1160488313288827/50000000000000 : ℝ)*(major2) + (10433450369/100000000000000 : ℝ)*(sp1) + (7885500979/50000000000000 : ℝ)*(sp2) + (3104063362100421/100000000000000 : ℝ)*(sp4) + (1552025924688613/50000000000000 : ℝ)*(sp5) + (776011557546139/25000000000000 : ℝ)*(sp6) + (1537889769085383/100000000000000 : ℝ)*(sp7) + (1537889769085383/100000000000000 : ℝ)*(f.failure) + (3104063362100421/100000000000000 : ℝ)*(f.sum) + (25142404046671/4392500000000000000000000000 : ℝ)*base65 + (4089051856638313/502000000000000000000000000000 : ℝ)*base67 + (5383130548638313/502000000000000000000000000000 : ℝ)*base69 + (4162994383880313/502000000000000000000000000000 : ℝ)*base71 + (3851498170477/2196250000000000000000000000 : ℝ)*base74 + (8519130710186313/502000000000000000000000000000 : ℝ)*base75 + (6230206233162313/502000000000000000000000000000 : ℝ)*base77 + (3424982203810313/502000000000000000000000000000 : ℝ)*base79 + (14545146620057/8785000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (10435469/1000000000000000000000 : ℝ)*base90 + (10435469/1000000000000000000000 : ℝ)*base92 + (10435469/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1216_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2011/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3027/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (587/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1216_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1216_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (587/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1216_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1216_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1216_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1051/256 : ℝ) ≤ p) (hpb : p ≤ (8409/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15091957/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (587/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4073/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1216_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
