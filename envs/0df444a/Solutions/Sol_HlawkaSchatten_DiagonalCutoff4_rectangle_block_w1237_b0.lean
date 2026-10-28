-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1237_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:17:18.384536+00:00
-- url     : https://prove2.me/submissions/322e1034-d51a-42f0-ae04-5a82caa1ed09

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
theorem support_rectangle_w1237_s0_0 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1862103873/10000000000 : ℝ)*x 0 + (6032632827/10000000000 : ℝ)*x 1 + (2396184207/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1862103873/10000000000 : ℝ)^4215 ≤ (2714477909191/25000000000000 : ℝ)^3191 := by
    have hnat : (1862103873 : ℕ)^4215*25000000000000^3191 ≤ 2714477909191^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1862103873 10000000000 2714477909191 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6032632827/10000000000 : ℝ)^4215 ≤ (25647261633747/50000000000000 : ℝ)^3191 := by
    have hnat : (6032632827 : ℕ)^4215*50000000000000^3191 ≤ 25647261633747^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6032632827 10000000000 25647261633747 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2396184207/5000000000 : ℝ)^4215 ≤ (37847565083969/100000000000000 : ℝ)^3191 := by
    have hnat : (2396184207 : ℕ)^4215*100000000000000^3191 ≤ 37847565083969^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2396184207 5000000000 37847565083969 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1862103873/10000000000 : ℝ), (6032632827/10000000000 : ℝ), (2396184207/5000000000 : ℝ)] ![(2714477909191/25000000000000 : ℝ), (25647261633747/50000000000000 : ℝ), (37847565083969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1862103873/10000000000 : ℝ)|^4215 ≤ (2714477909191/25000000000000 : ℝ)^3191
        have hw : |(-1862103873/10000000000 : ℝ)|=(1862103873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6032632827/10000000000 : ℝ)|^4215 ≤ (25647261633747/50000000000000 : ℝ)^3191
        have hw : |(6032632827/10000000000 : ℝ)|=(6032632827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2396184207/5000000000 : ℝ)|^4215 ≤ (37847565083969/100000000000000 : ℝ)^3191
        have hw : |(2396184207/5000000000 : ℝ)|=(2396184207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s0_1 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2755720587/5000000000 : ℝ)*x 0 + (-514253541/2000000000 : ℝ)*x 1 + (958473673/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2755720587/5000000000 : ℝ)^4215 ≤ (22761795597117/50000000000000 : ℝ)^3191 := by
    have hnat : (2755720587 : ℕ)^4215*50000000000000^3191 ≤ 22761795597117^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2755720587 5000000000 22761795597117 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (514253541/2000000000 : ℝ)^4215 ≤ (8314422110723/50000000000000 : ℝ)^3191 := by
    have hnat : (514253541 : ℕ)^4215*50000000000000^3191 ≤ 8314422110723^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514253541 2000000000 8314422110723 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958473673/2000000000 : ℝ)^4215 ≤ (9461891143203/25000000000000 : ℝ)^3191 := by
    have hnat : (958473673 : ℕ)^4215*25000000000000^3191 ≤ 9461891143203^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958473673 2000000000 9461891143203 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2755720587/5000000000 : ℝ), (-514253541/2000000000 : ℝ), (958473673/2000000000 : ℝ)] ![(22761795597117/50000000000000 : ℝ), (8314422110723/50000000000000 : ℝ), (9461891143203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2755720587/5000000000 : ℝ)|^4215 ≤ (22761795597117/50000000000000 : ℝ)^3191
        have hw : |(2755720587/5000000000 : ℝ)|=(2755720587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-514253541/2000000000 : ℝ)|^4215 ≤ (8314422110723/50000000000000 : ℝ)^3191
        have hw : |(-514253541/2000000000 : ℝ)|=(514253541/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958473673/2000000000 : ℝ)|^4215 ≤ (9461891143203/25000000000000 : ℝ)^3191
        have hw : |(958473673/2000000000 : ℝ)|=(958473673/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s0_2 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5511441107/10000000000 : ℝ)*x 0 + (4792368433/10000000000 : ℝ)*x 1 + (-2571267707/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5511441107/10000000000 : ℝ)^4215 ≤ (9104718092647/20000000000000 : ℝ)^3191 := by
    have hnat : (5511441107 : ℕ)^4215*20000000000000^3191 ≤ 9104718092647^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511441107 10000000000 9104718092647 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4792368433/10000000000 : ℝ)^4215 ≤ (37847565282173/100000000000000 : ℝ)^3191 := by
    have hnat : (4792368433 : ℕ)^4215*100000000000000^3191 ≤ 37847565282173^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792368433 10000000000 37847565282173 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2571267707/10000000000 : ℝ)^4215 ≤ (16628844238531/100000000000000 : ℝ)^3191 := by
    have hnat : (2571267707 : ℕ)^4215*100000000000000^3191 ≤ 16628844238531^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571267707 10000000000 16628844238531 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5511441107/10000000000 : ℝ), (4792368433/10000000000 : ℝ), (-2571267707/10000000000 : ℝ)] ![(9104718092647/20000000000000 : ℝ), (37847565282173/100000000000000 : ℝ), (16628844238531/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5511441107/10000000000 : ℝ)|^4215 ≤ (9104718092647/20000000000000 : ℝ)^3191
        have hw : |(5511441107/10000000000 : ℝ)|=(5511441107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4792368433/10000000000 : ℝ)|^4215 ≤ (37847565282173/100000000000000 : ℝ)^3191
        have hw : |(4792368433/10000000000 : ℝ)|=(4792368433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2571267707/10000000000 : ℝ)|^4215 ≤ (16628844238531/100000000000000 : ℝ)^3191
        have hw : |(-2571267707/10000000000 : ℝ)|=(2571267707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s0_3 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2096707279/5000000000 : ℝ)*x 0 + (3117079689/10000000000 : ℝ)*x 1 + (703826829/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2096707279/5000000000 : ℝ)^4215 ≤ (15864224657463/50000000000000 : ℝ)^3191 := by
    have hnat : (2096707279 : ℕ)^4215*50000000000000^3191 ≤ 15864224657463^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2096707279 5000000000 15864224657463 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3117079689/10000000000 : ℝ)^4215 ≤ (21443235883621/100000000000000 : ℝ)^3191 := by
    have hnat : (3117079689 : ℕ)^4215*100000000000000^3191 ≤ 21443235883621^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117079689 10000000000 21443235883621 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (703826829/1250000000 : ℝ)^4215 ≤ (23414157392691/50000000000000 : ℝ)^3191 := by
    have hnat : (703826829 : ℕ)^4215*50000000000000^3191 ≤ 23414157392691^3191*1250000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      703826829 1250000000 23414157392691 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2096707279/5000000000 : ℝ), (3117079689/10000000000 : ℝ), (703826829/1250000000 : ℝ)] ![(15864224657463/50000000000000 : ℝ), (21443235883621/100000000000000 : ℝ), (23414157392691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2096707279/5000000000 : ℝ)|^4215 ≤ (15864224657463/50000000000000 : ℝ)^3191
        have hw : |(2096707279/5000000000 : ℝ)|=(2096707279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3117079689/10000000000 : ℝ)|^4215 ≤ (21443235883621/100000000000000 : ℝ)^3191
        have hw : |(3117079689/10000000000 : ℝ)|=(3117079689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(703826829/1250000000 : ℝ)|^4215 ≤ (23414157392691/50000000000000 : ℝ)^3191
        have hw : |(703826829/1250000000 : ℝ)|=(703826829/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s0_4 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-933487801/5000000000 : ℝ)*x 0 + (4824311171/10000000000 : ℝ)*x 1 + (5999561201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (933487801/5000000000 : ℝ)^4215 ≤ (10895450270203/100000000000000 : ℝ)^3191 := by
    have hnat : (933487801 : ℕ)^4215*100000000000000^3191 ≤ 10895450270203^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      933487801 5000000000 10895450270203 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4824311171/10000000000 : ℝ)^4215 ≤ (19090570403089/50000000000000 : ℝ)^3191 := by
    have hnat : (4824311171 : ℕ)^4215*50000000000000^3191 ≤ 19090570403089^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4824311171 10000000000 19090570403089 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5999561201/10000000000 : ℝ)^4215 ≤ (50923408896169/100000000000000 : ℝ)^3191 := by
    have hnat : (5999561201 : ℕ)^4215*100000000000000^3191 ≤ 50923408896169^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5999561201 10000000000 50923408896169 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-933487801/5000000000 : ℝ), (4824311171/10000000000 : ℝ), (5999561201/10000000000 : ℝ)] ![(10895450270203/100000000000000 : ℝ), (19090570403089/50000000000000 : ℝ), (50923408896169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-933487801/5000000000 : ℝ)|^4215 ≤ (10895450270203/100000000000000 : ℝ)^3191
        have hw : |(-933487801/5000000000 : ℝ)|=(933487801/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4824311171/10000000000 : ℝ)|^4215 ≤ (19090570403089/50000000000000 : ℝ)^3191
        have hw : |(4824311171/10000000000 : ℝ)|=(4824311171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5999561201/10000000000 : ℝ)|^4215 ≤ (50923408896169/100000000000000 : ℝ)^3191
        have hw : |(5999561201/10000000000 : ℝ)|=(5999561201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s0_5 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5174003917/10000000000 : ℝ)*x 0 + (-1364072737/10000000000 : ℝ)*x 1 + (1499890857/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5174003917/10000000000 : ℝ)^4215 ≤ (41878684571733/100000000000000 : ℝ)^3191 := by
    have hnat : (5174003917 : ℕ)^4215*100000000000000^3191 ≤ 41878684571733^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5174003917 10000000000 41878684571733 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364072737/10000000000 : ℝ)^4215 ≤ (7197881556767/100000000000000 : ℝ)^3191 := by
    have hnat : (1364072737 : ℕ)^4215*100000000000000^3191 ≤ 7197881556767^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364072737 10000000000 7197881556767 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1499890857/2500000000 : ℝ)^4215 ≤ (50923433864471/100000000000000 : ℝ)^3191 := by
    have hnat : (1499890857 : ℕ)^4215*100000000000000^3191 ≤ 50923433864471^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1499890857 2500000000 50923433864471 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5174003917/10000000000 : ℝ), (-1364072737/10000000000 : ℝ), (1499890857/2500000000 : ℝ)] ![(41878684571733/100000000000000 : ℝ), (7197881556767/100000000000000 : ℝ), (50923433864471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5174003917/10000000000 : ℝ)|^4215 ≤ (41878684571733/100000000000000 : ℝ)^3191
        have hw : |(5174003917/10000000000 : ℝ)|=(5174003917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1364072737/10000000000 : ℝ)|^4215 ≤ (7197881556767/100000000000000 : ℝ)^3191
        have hw : |(-1364072737/10000000000 : ℝ)|=(1364072737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1499890857/2500000000 : ℝ)|^4215 ≤ (50923433864471/100000000000000 : ℝ)^3191
        have hw : |(1499890857/2500000000 : ℝ)|=(1499890857/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s0_6 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2587002387/5000000000 : ℝ)*x 0 + (2999780839/5000000000 : ℝ)*x 1 + (-1364074237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587002387/5000000000 : ℝ)^4215 ≤ (8375738746863/20000000000000 : ℝ)^3191 := by
    have hnat : (2587002387 : ℕ)^4215*20000000000000^3191 ≤ 8375738746863^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587002387 5000000000 8375738746863 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2999780839/5000000000 : ℝ)^4215 ≤ (50923414244117/100000000000000 : ℝ)^3191 := by
    have hnat : (2999780839 : ℕ)^4215*100000000000000^3191 ≤ 50923414244117^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2999780839 5000000000 50923414244117 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1364074237/10000000000 : ℝ)^4215 ≤ (7197892011893/100000000000000 : ℝ)^3191 := by
    have hnat : (1364074237 : ℕ)^4215*100000000000000^3191 ≤ 7197892011893^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364074237 10000000000 7197892011893 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587002387/5000000000 : ℝ), (2999780839/5000000000 : ℝ), (-1364074237/10000000000 : ℝ)] ![(8375738746863/20000000000000 : ℝ), (50923414244117/100000000000000 : ℝ), (7197892011893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587002387/5000000000 : ℝ)|^4215 ≤ (8375738746863/20000000000000 : ℝ)^3191
        have hw : |(2587002387/5000000000 : ℝ)|=(2587002387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2999780839/5000000000 : ℝ)|^4215 ≤ (50923414244117/100000000000000 : ℝ)^3191
        have hw : |(2999780839/5000000000 : ℝ)|=(2999780839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1364074237/10000000000 : ℝ)|^4215 ≤ (7197892011893/100000000000000 : ℝ)^3191
        have hw : |(-1364074237/10000000000 : ℝ)|=(1364074237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s0_7 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (42032883/100000000 : ℝ)*x 0 + (5565884113/10000000000 : ℝ)*x 1 + (1592048667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (42032883/100000000 : ℝ)^4215 ≤ (15913583794579/50000000000000 : ℝ)^3191 := by
    have hnat : (42032883 : ℕ)^4215*50000000000000^3191 ≤ 15913583794579^3191*100000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42032883 100000000 15913583794579 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5565884113/10000000000 : ℝ)^4215 ≤ (46118526771823/100000000000000 : ℝ)^3191 := by
    have hnat : (5565884113 : ℕ)^4215*100000000000000^3191 ≤ 46118526771823^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5565884113 10000000000 46118526771823 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1592048667/5000000000 : ℝ)^4215 ≤ (882172224573/4000000000000 : ℝ)^3191 := by
    have hnat : (1592048667 : ℕ)^4215*4000000000000^3191 ≤ 882172224573^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592048667 5000000000 882172224573 4000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(42032883/100000000 : ℝ), (5565884113/10000000000 : ℝ), (1592048667/5000000000 : ℝ)] ![(15913583794579/50000000000000 : ℝ), (46118526771823/100000000000000 : ℝ), (882172224573/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(42032883/100000000 : ℝ)|^4215 ≤ (15913583794579/50000000000000 : ℝ)^3191
        have hw : |(42032883/100000000 : ℝ)|=(42032883/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5565884113/10000000000 : ℝ)|^4215 ≤ (46118526771823/100000000000000 : ℝ)^3191
        have hw : |(5565884113/10000000000 : ℝ)|=(5565884113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1592048667/5000000000 : ℝ)|^4215 ≤ (882172224573/4000000000000 : ℝ)^3191
        have hw : |(1592048667/5000000000 : ℝ)|=(1592048667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1237_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (399/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5491/20000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8429/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8429 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8429*1^2048 ≤ 0^2048*1^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8429/2048 : ℝ) ≤ (1151222568289340697/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8429 ≤ (1151222568289340697/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8429*50000000000000000000^2048 ≤ 1151222568289340697^2048*5^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1151222568289340697 50000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1151222568289340697/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8429 := by
      have hnat : (1 : ℕ)^2048*1^8429 ≤ 1^8429*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (51151222568289340697/50000000000000000000 : ℝ) ≤ (10055461596231221/10000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (51151222568289340697/50000000000000000000 : ℝ)^2048 ≤ (10055461596231221/10000000000000000 : ℝ)^8429 := by
      have hnat : (51151222568289340697 : ℕ)^2048*10000000000000000^8429 ≤ 10055461596231221^8429*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51151222568289340697 50000000000000000000 10055461596231221 10000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10055461596231221/10000000000000000 : ℝ)) (X := (51151222568289340697/50000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (26151222568289340697/25000000000000000000 : ℝ) ≤ (5055461596231221/5000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (26151222568289340697/25000000000000000000 : ℝ)^2048 ≤ (5055461596231221/5000000000000000 : ℝ)^8429 := by
      have hnat : (26151222568289340697 : ℕ)^2048*5000000000000000^8429 ≤ 5055461596231221^8429*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26151222568289340697 25000000000000000000 5055461596231221 5000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5055461596231221/5000000000000000 : ℝ)) (X := (26151222568289340697/25000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(55461596231221/4000000000000000 : ℝ)*(0 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55461596231221/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1151222568289340697/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(55461596231221/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8429/2048 : ℝ) := by
    rw [show (1 : ℝ)+(55461596231221/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10055461596231221/10000000000000000 : ℝ) by norm_num, show 1+(1151222568289340697/50000000000000000000 : ℝ)+(0 : ℝ)=(51151222568289340697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1151222568289340697/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(55461596231221/4000000000000000 : ℝ)*(2/5 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(55461596231221/4000000000000000 : ℝ)*(2/5 : ℝ)=(5055461596231221/5000000000000000 : ℝ) by norm_num, show 1+2*(1151222568289340697/50000000000000000000 : ℝ)=(26151222568289340697/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(55461596231221/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55461596231221/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(55461596231221/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55461596231221/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(55461596231221/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (55461596231221/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1862103873/10000000000 : ℝ)*X 0 0+(6032632827/10000000000 : ℝ)*X 0 1+(2396184207/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2755720587/5000000000 : ℝ)*X 1 0+(-514253541/2000000000 : ℝ)*X 1 1+(958473673/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5511441107/10000000000 : ℝ)*X 2 0+(4792368433/10000000000 : ℝ)*X 2 1+(-2571267707/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2096707279/5000000000 : ℝ)*X 0 0+(3117079689/10000000000 : ℝ)*X 0 1+(703826829/1250000000 : ℝ)*X 0 2+(2096707279/5000000000 : ℝ)*X 1 0+(3117079689/10000000000 : ℝ)*X 1 1+(703826829/1250000000 : ℝ)*X 1 2+(2096707279/5000000000 : ℝ)*X 2 0+(3117079689/10000000000 : ℝ)*X 2 1+(703826829/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-933487801/5000000000 : ℝ)*X 0 0+(4824311171/10000000000 : ℝ)*X 0 1+(5999561201/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5174003917/10000000000 : ℝ)*X 1 0+(-1364072737/10000000000 : ℝ)*X 1 1+(1499890857/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2587002387/5000000000 : ℝ)*X 2 0+(2999780839/5000000000 : ℝ)*X 2 1+(-1364074237/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((42032883/100000000 : ℝ)*X 0 0+(5565884113/10000000000 : ℝ)*X 0 1+(1592048667/5000000000 : ℝ)*X 0 2+(42032883/100000000 : ℝ)*X 1 0+(5565884113/10000000000 : ℝ)*X 1 1+(1592048667/5000000000 : ℝ)*X 1 2+(42032883/100000000 : ℝ)*X 2 0+(5565884113/10000000000 : ℝ)*X 2 1+(1592048667/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (600885992480018479998267/100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1461613/2000000000000 : ℝ)*(base1) + (292984197/20000000000000 : ℝ)*(base19) + (1357203777/100000000000000 : ℝ)*(base23) + (97915563/100000000000000 : ℝ)*(base24) + (20638983/6250000000000 : ℝ)*(upper3) + (602069106496891/100000000000000 : ℝ)*(major0) + (602069106496891/100000000000000 : ℝ)*(major1) + (602069106496891/100000000000000 : ℝ)*(major2) + (40314232554331/5000000000000 : ℝ)*(sp0) + (50392898387477/6250000000000 : ℝ)*(sp1) + (201571596000319/25000000000000 : ℝ)*(sp2) + (198923781083573/50000000000000 : ℝ)*(sp3) + (407639331/12500000000000 : ℝ)*(sp4) + (2538330031/100000000000000 : ℝ)*(sp7) + (99462543394457/25000000000000 : ℝ)*(f.failure) + (806287839120617/100000000000000 : ℝ)*(f.sum) + (763701071233911/200000000000000000000000000000 : ℝ)*base65 + (636829704366089/400000000000000000000000000000 : ℝ)*base68 + (1049672867966089/400000000000000000000000000000 : ℝ)*base70 + (961932659233911/400000000000000000000000000000 : ℝ)*base71 + (618989246233911/200000000000000000000000000000 : ℝ)*base73 + (561587631233911/400000000000000000000000000000 : ℝ)*base75 + (2327370833633911/400000000000000000000000000000 : ℝ)*base77 + (3345765111633911/400000000000000000000000000000 : ℝ)*base79 + (233413345166089/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base88 + (3612141/2500000000000000000000 : ℝ)*base89 + (3612141/2500000000000000000000 : ℝ)*base91 + (3612141/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (144955580639224377677577/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113951941/100000000000000 : ℝ)*(base1) + (289070397/20000000000000 : ℝ)*(base19) + (790496573/50000000000000 : ℝ)*(base23) + (328091097/100000000000000 : ℝ)*(upper3) + (10570419/50000000000000 : ℝ)*(upper5) + (158841851001479/25000000000000 : ℝ)*(major0) + (158841851001479/25000000000000 : ℝ)*(major1) + (158841851001479/25000000000000 : ℝ)*(major2) + (1537604777/50000000000000 : ℝ)*(sp1) + (748507657/25000000000000 : ℝ)*(sp2) + (850880879286487/100000000000000 : ℝ)*(sp4) + (850876244773007/100000000000000 : ℝ)*(sp5) + (850876190310771/100000000000000 : ℝ)*(sp6) + (419853735451231/100000000000000 : ℝ)*(sp7) + (419853849403171/100000000000000 : ℝ)*(f.failure) + (425440382667273/50000000000000 : ℝ)*(f.sum) + (8949459324141/50000000000000000000000000000 : ℝ)*base66 + (729933041024141/100000000000000000000000000000 : ℝ)*base68 + (207039992875859/100000000000000000000000000000 : ℝ)*base69 + (11723314524141/100000000000000000000000000000 : ℝ)*base72 + (284635571724141/50000000000000000000000000000 : ℝ)*base74 + (274504360975859/100000000000000000000000000000 : ℝ)*base75 + (299656571975859/100000000000000000000000000000 : ℝ)*base77 + (877951620475859/100000000000000000000000000000 : ℝ)*base79 + (35873174574141/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (48426177/10000000000000000000000 : ℝ)*base90 + (48426177/10000000000000000000000 : ℝ)*base92 + (48426177/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1237_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (399/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5491/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1237_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1237_s1_0 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-411975517/2000000000 : ℝ)*x 0 + (5676865341/10000000000 : ℝ)*x 1 + (5021538461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411975517/2000000000 : ℝ)^4215 ≤ (1550819995907/12500000000000 : ℝ)^3191 := by
    have hnat : (411975517 : ℕ)^4215*12500000000000^3191 ≤ 1550819995907^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411975517 2000000000 1550819995907 12500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5676865341/10000000000 : ℝ)^4215 ≤ (23668537326231/50000000000000 : ℝ)^3191 := by
    have hnat : (5676865341 : ℕ)^4215*50000000000000^3191 ≤ 23668537326231^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5676865341 10000000000 23668537326231 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5021538461/10000000000 : ℝ)^4215 ≤ (8051273071419/20000000000000 : ℝ)^3191 := by
    have hnat : (5021538461 : ℕ)^4215*20000000000000^3191 ≤ 8051273071419^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5021538461 10000000000 8051273071419 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411975517/2000000000 : ℝ), (5676865341/10000000000 : ℝ), (5021538461/10000000000 : ℝ)] ![(1550819995907/12500000000000 : ℝ), (23668537326231/50000000000000 : ℝ), (8051273071419/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411975517/2000000000 : ℝ)|^4215 ≤ (1550819995907/12500000000000 : ℝ)^3191
        have hw : |(-411975517/2000000000 : ℝ)|=(411975517/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5676865341/10000000000 : ℝ)|^4215 ≤ (23668537326231/50000000000000 : ℝ)^3191
        have hw : |(5676865341/10000000000 : ℝ)|=(5676865341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5021538461/10000000000 : ℝ)|^4215 ≤ (8051273071419/20000000000000 : ℝ)^3191
        have hw : |(5021538461/10000000000 : ℝ)|=(5021538461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s1_1 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5413930609/10000000000 : ℝ)*x 0 + (-2411865889/10000000000 : ℝ)*x 1 + (1004307723/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5413930609/10000000000 : ℝ)^4215 ≤ (22231370349583/50000000000000 : ℝ)^3191 := by
    have hnat : (5413930609 : ℕ)^4215*50000000000000^3191 ≤ 22231370349583^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413930609 10000000000 22231370349583 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2411865889/10000000000 : ℝ)^4215 ≤ (1528089230847/10000000000000 : ℝ)^3191 := by
    have hnat : (2411865889 : ℕ)^4215*10000000000000^3191 ≤ 1528089230847^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2411865889 10000000000 1528089230847 10000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004307723/2000000000 : ℝ)^4215 ≤ (10064091746963/25000000000000 : ℝ)^3191 := by
    have hnat : (1004307723 : ℕ)^4215*25000000000000^3191 ≤ 10064091746963^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004307723 2000000000 10064091746963 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5413930609/10000000000 : ℝ), (-2411865889/10000000000 : ℝ), (1004307723/2000000000 : ℝ)] ![(22231370349583/50000000000000 : ℝ), (1528089230847/10000000000000 : ℝ), (10064091746963/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5413930609/10000000000 : ℝ)|^4215 ≤ (22231370349583/50000000000000 : ℝ)^3191
        have hw : |(5413930609/10000000000 : ℝ)|=(5413930609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2411865889/10000000000 : ℝ)|^4215 ≤ (1528089230847/10000000000000 : ℝ)^3191
        have hw : |(-2411865889/10000000000 : ℝ)|=(2411865889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004307723/2000000000 : ℝ)|^4215 ≤ (10064091746963/25000000000000 : ℝ)^3191
        have hw : |(1004307723/2000000000 : ℝ)|=(1004307723/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s1_2 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1353482689/2500000000 : ℝ)*x 0 + (5021538513/10000000000 : ℝ)*x 1 + (-1205932913/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1353482689/2500000000 : ℝ)^4215 ≤ (44462742293839/100000000000000 : ℝ)^3191 := by
    have hnat : (1353482689 : ℕ)^4215*100000000000000^3191 ≤ 44462742293839^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353482689 2500000000 44462742293839 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5021538513/10000000000 : ℝ)^4215 ≤ (40256365907741/100000000000000 : ℝ)^3191 := by
    have hnat : (5021538513 : ℕ)^4215*100000000000000^3191 ≤ 40256365907741^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5021538513 10000000000 40256365907741 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1205932913/5000000000 : ℝ)^4215 ≤ (955055736327/6250000000000 : ℝ)^3191 := by
    have hnat : (1205932913 : ℕ)^4215*6250000000000^3191 ≤ 955055736327^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205932913 5000000000 955055736327 6250000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1353482689/2500000000 : ℝ), (5021538513/10000000000 : ℝ), (-1205932913/5000000000 : ℝ)] ![(44462742293839/100000000000000 : ℝ), (40256365907741/100000000000000 : ℝ), (955055736327/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1353482689/2500000000 : ℝ)|^4215 ≤ (44462742293839/100000000000000 : ℝ)^3191
        have hw : |(1353482689/2500000000 : ℝ)|=(1353482689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5021538513/10000000000 : ℝ)|^4215 ≤ (40256365907741/100000000000000 : ℝ)^3191
        have hw : |(5021538513/10000000000 : ℝ)|=(5021538513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1205932913/5000000000 : ℝ)|^4215 ≤ (955055736327/6250000000000 : ℝ)^3191
        have hw : |(-1205932913/5000000000 : ℝ)|=(1205932913/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s1_3 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (172371553/400000000 : ℝ)*x 0 + (738907743/2000000000 : ℝ)*x 1 + (5022632779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (172371553/400000000 : ℝ)^4215 ≤ (32891632798957/100000000000000 : ℝ)^3191 := by
    have hnat : (172371553 : ℕ)^4215*100000000000000^3191 ≤ 32891632798957^3191*400000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172371553 400000000 32891632798957 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (738907743/2000000000 : ℝ)^4215 ≤ (6710103330959/25000000000000 : ℝ)^3191 := by
    have hnat : (738907743 : ℕ)^4215*25000000000000^3191 ≤ 6710103330959^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      738907743 2000000000 6710103330959 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5022632779/10000000000 : ℝ)^4215 ≤ (40267953858289/100000000000000 : ℝ)^3191 := by
    have hnat : (5022632779 : ℕ)^4215*100000000000000^3191 ≤ 40267953858289^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5022632779 10000000000 40267953858289 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(172371553/400000000 : ℝ), (738907743/2000000000 : ℝ), (5022632779/10000000000 : ℝ)] ![(32891632798957/100000000000000 : ℝ), (6710103330959/25000000000000 : ℝ), (40267953858289/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(172371553/400000000 : ℝ)|^4215 ≤ (32891632798957/100000000000000 : ℝ)^3191
        have hw : |(172371553/400000000 : ℝ)|=(172371553/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(738907743/2000000000 : ℝ)|^4215 ≤ (6710103330959/25000000000000 : ℝ)^3191
        have hw : |(738907743/2000000000 : ℝ)|=(738907743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5022632779/10000000000 : ℝ)|^4215 ≤ (40267953858289/100000000000000 : ℝ)^3191
        have hw : |(5022632779/10000000000 : ℝ)|=(5022632779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s1_4 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2060560489/10000000000 : ℝ)*x 0 + (2515081989/5000000000 : ℝ)*x 1 + (5668074997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2060560489/10000000000 : ℝ)^4215 ≤ (6205996632457/50000000000000 : ℝ)^3191 := by
    have hnat : (2060560489 : ℕ)^4215*50000000000000^3191 ≤ 6205996632457^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060560489 10000000000 6205996632457 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2515081989/5000000000 : ℝ)^4215 ≤ (10086932244851/25000000000000 : ℝ)^3191 := by
    have hnat : (2515081989 : ℕ)^4215*25000000000000^3191 ≤ 10086932244851^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2515081989 5000000000 10086932244851 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5668074997/10000000000 : ℝ)^4215 ≤ (5905034717163/12500000000000 : ℝ)^3191 := by
    have hnat : (5668074997 : ℕ)^4215*12500000000000^3191 ≤ 5905034717163^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5668074997 10000000000 5905034717163 12500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2060560489/10000000000 : ℝ), (2515081989/5000000000 : ℝ), (5668074997/10000000000 : ℝ)] ![(6205996632457/50000000000000 : ℝ), (10086932244851/25000000000000 : ℝ), (5905034717163/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2060560489/10000000000 : ℝ)|^4215 ≤ (6205996632457/50000000000000 : ℝ)^3191
        have hw : |(-2060560489/10000000000 : ℝ)|=(2060560489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2515081989/5000000000 : ℝ)|^4215 ≤ (10086932244851/25000000000000 : ℝ)^3191
        have hw : |(2515081989/5000000000 : ℝ)|=(2515081989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5668074997/10000000000 : ℝ)|^4215 ≤ (5905034717163/12500000000000 : ℝ)^3191
        have hw : |(5668074997/10000000000 : ℝ)|=(5668074997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s1_5 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2622569533/5000000000 : ℝ)*x 0 + (-1765328893/10000000000 : ℝ)*x 1 + (283403759/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2622569533/5000000000 : ℝ)^4215 ≤ (42640895776361/100000000000000 : ℝ)^3191 := by
    have hnat : (2622569533 : ℕ)^4215*100000000000000^3191 ≤ 42640895776361^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622569533 5000000000 42640895776361 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1765328893/10000000000 : ℝ)^4215 ≤ (5059412230499/50000000000000 : ℝ)^3191 := by
    have hnat : (1765328893 : ℕ)^4215*50000000000000^3191 ≤ 5059412230499^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1765328893 10000000000 5059412230499 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283403759/500000000 : ℝ)^4215 ≤ (944805595039/2000000000000 : ℝ)^3191 := by
    have hnat : (283403759 : ℕ)^4215*2000000000000^3191 ≤ 944805595039^3191*500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283403759 500000000 944805595039 2000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2622569533/5000000000 : ℝ), (-1765328893/10000000000 : ℝ), (283403759/500000000 : ℝ)] ![(42640895776361/100000000000000 : ℝ), (5059412230499/50000000000000 : ℝ), (944805595039/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2622569533/5000000000 : ℝ)|^4215 ≤ (42640895776361/100000000000000 : ℝ)^3191
        have hw : |(2622569533/5000000000 : ℝ)|=(2622569533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1765328893/10000000000 : ℝ)|^4215 ≤ (5059412230499/50000000000000 : ℝ)^3191
        have hw : |(-1765328893/10000000000 : ℝ)|=(1765328893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(283403759/500000000 : ℝ)|^4215 ≤ (944805595039/2000000000000 : ℝ)^3191
        have hw : |(283403759/500000000 : ℝ)|=(283403759/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s1_6 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1311284853/2500000000 : ℝ)*x 0 + (708509493/1250000000 : ℝ)*x 1 + (-441331823/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1311284853/2500000000 : ℝ)^4215 ≤ (10660224872963/25000000000000 : ℝ)^3191 := by
    have hnat : (1311284853 : ℕ)^4215*25000000000000^3191 ≤ 10660224872963^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311284853 2500000000 10660224872963 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (708509493/1250000000 : ℝ)^4215 ≤ (47240288162821/100000000000000 : ℝ)^3191 := by
    have hnat : (708509493 : ℕ)^4215*100000000000000^3191 ≤ 47240288162821^3191*1250000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708509493 1250000000 47240288162821 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (441331823/2500000000 : ℝ)^4215 ≤ (632425771201/6250000000000 : ℝ)^3191 := by
    have hnat : (441331823 : ℕ)^4215*6250000000000^3191 ≤ 632425771201^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441331823 2500000000 632425771201 6250000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1311284853/2500000000 : ℝ), (708509493/1250000000 : ℝ), (-441331823/2500000000 : ℝ)] ![(10660224872963/25000000000000 : ℝ), (47240288162821/100000000000000 : ℝ), (632425771201/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1311284853/2500000000 : ℝ)|^4215 ≤ (10660224872963/25000000000000 : ℝ)^3191
        have hw : |(1311284853/2500000000 : ℝ)|=(1311284853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(708509493/1250000000 : ℝ)|^4215 ≤ (47240288162821/100000000000000 : ℝ)^3191
        have hw : |(708509493/1250000000 : ℝ)|=(708509493/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-441331823/2500000000 : ℝ)|^4215 ≤ (632425771201/6250000000000 : ℝ)^3191
        have hw : |(-441331823/2500000000 : ℝ)|=(441331823/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s1_7 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4310671159/10000000000 : ℝ)*x 0 + (5005152949/10000000000 : ℝ)*x 1 + (3712351953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4310671159/10000000000 : ℝ)^4215 ≤ (32905570333143/100000000000000 : ℝ)^3191 := by
    have hnat : (4310671159 : ℕ)^4215*100000000000000^3191 ≤ 32905570333143^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4310671159 10000000000 32905570333143 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5005152949/10000000000 : ℝ)^4215 ≤ (40082944650357/100000000000000 : ℝ)^3191 := by
    have hnat : (5005152949 : ℕ)^4215*100000000000000^3191 ≤ 40082944650357^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5005152949 10000000000 40082944650357 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3712351953/10000000000 : ℝ)^4215 ≤ (13505742498819/50000000000000 : ℝ)^3191 := by
    have hnat : (3712351953 : ℕ)^4215*50000000000000^3191 ≤ 13505742498819^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3712351953 10000000000 13505742498819 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4310671159/10000000000 : ℝ), (5005152949/10000000000 : ℝ), (3712351953/10000000000 : ℝ)] ![(32905570333143/100000000000000 : ℝ), (40082944650357/100000000000000 : ℝ), (13505742498819/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4310671159/10000000000 : ℝ)|^4215 ≤ (32905570333143/100000000000000 : ℝ)^3191
        have hw : |(4310671159/10000000000 : ℝ)|=(4310671159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5005152949/10000000000 : ℝ)|^4215 ≤ (40082944650357/100000000000000 : ℝ)^3191
        have hw : |(5005152949/10000000000 : ℝ)|=(5005152949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3712351953/10000000000 : ℝ)|^4215 ≤ (13505742498819/50000000000000 : ℝ)^3191
        have hw : |(3712351953/10000000000 : ℝ)|=(3712351953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1237_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5491/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (399/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1233/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1001/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5491/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (399/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5491/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (399/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5491/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (399/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5491/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (399/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5491/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (399/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5491/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (399/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (399/50000 : ℝ) ^ (8429/2048 : ℝ) ≤ (231859965649/100000000000000000000 : ℝ) := by
    have hpowers : (399/50000 : ℝ)^8429 ≤ (231859965649/100000000000000000000 : ℝ)^2048 := by
      have hnat : (399 : ℕ)^8429*100000000000000000000^2048 ≤ 231859965649^2048*50000^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        399 50000 231859965649 100000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (399/50000 : ℝ)) (X := (231859965649/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5491/20000 : ℝ) ^ (8429/2048 : ℝ) ≤ (489239569093836649/100000000000000000000 : ℝ) := by
    have hpowers : (5491/20000 : ℝ)^8429 ≤ (489239569093836649/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5491 : ℕ)^8429*100000000000000000000^2048 ≤ 489239569093836649^2048*20000^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5491 20000 489239569093836649 100000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5491/20000 : ℝ)) (X := (489239569093836649/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000231859965649/50000000000000000000 : ℝ) ≤ (2500000002816759/2500000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (50000000231859965649/50000000000000000000 : ℝ)^2048 ≤ (2500000002816759/2500000000000000 : ℝ)^8429 := by
      have hnat : (50000000231859965649 : ℕ)^2048*2500000000000000^8429 ≤ 2500000002816759^8429*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000231859965649 50000000000000000000 2500000002816759 2500000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500000002816759/2500000000000000 : ℝ)) (X := (50000000231859965649/50000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50244619900476901149/50000000000000000000 : ℝ) ≤ (2502966285832853/2500000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (50244619900476901149/50000000000000000000 : ℝ)^2048 ≤ (2502966285832853/2500000000000000 : ℝ)^8429 := by
      have hnat : (50244619900476901149 : ℕ)^2048*2500000000000000^8429 ≤ 2502966285832853^8429*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50244619900476901149 50000000000000000000 2502966285832853 2500000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502966285832853/2500000000000000 : ℝ)) (X := (50244619900476901149/50000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50489239569093836649/50000000000000000000 : ℝ) ≤ (2505932568848947/2500000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (50489239569093836649/50000000000000000000 : ℝ)^2048 ≤ (2505932568848947/2500000000000000 : ℝ)^8429 := by
      have hnat : (50489239569093836649 : ℕ)^2048*2500000000000000^8429 ≤ 2505932568848947^8429*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50489239569093836649 50000000000000000000 2505932568848947 2500000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505932568848947/2500000000000000 : ℝ)) (X := (50489239569093836649/50000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(231859965649/100000000000000000000 : ℝ) ≤ ((3507250836178560981/3507500000000000000 : ℝ)+2*(1483141508047/333212500000000 : ℝ)*(399/50000 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (3507250836178560981/3507500000000000000 : ℝ)+2*(1483141508047/333212500000000 : ℝ)*(399/50000 : ℝ)=(2500000002816759/2500000000000000 : ℝ) by norm_num, show 1+2*(231859965649/100000000000000000000 : ℝ)=(50000000231859965649/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(489239569093836649/100000000000000000000 : ℝ)+(231859965649/100000000000000000000 : ℝ) ≤ ((3507250836178560981/3507500000000000000 : ℝ)+(1483141508047/333212500000000 : ℝ)*((5491/20000 : ℝ)+(399/50000 : ℝ)))^(8429/2048 : ℝ) := by
    rw [show (3507250836178560981/3507500000000000000 : ℝ)+(1483141508047/333212500000000 : ℝ)*((5491/20000 : ℝ)+(399/50000 : ℝ))=(2502966285832853/2500000000000000 : ℝ) by norm_num, show 1+(489239569093836649/100000000000000000000 : ℝ)+(231859965649/100000000000000000000 : ℝ)=(50244619900476901149/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(489239569093836649/100000000000000000000 : ℝ) ≤ ((3507250836178560981/3507500000000000000 : ℝ)+2*(1483141508047/333212500000000 : ℝ)*(5491/20000 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (3507250836178560981/3507500000000000000 : ℝ)+2*(1483141508047/333212500000000 : ℝ)*(5491/20000 : ℝ)=(2505932568848947/2500000000000000 : ℝ) by norm_num, show 1+2*(489239569093836649/100000000000000000000 : ℝ)=(50489239569093836649/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3507250836178560981/3507500000000000000 : ℝ)*(X 1 0+X 2 0)+(1483141508047/333212500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (399/50000 : ℝ)) (hi := (5491/20000 : ℝ)) (c := (3507250836178560981/3507500000000000000 : ℝ)) (alpha := (1483141508047/333212500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3507250836178560981/3507500000000000000 : ℝ)*(X 0 1+X 2 1)+(1483141508047/333212500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (399/50000 : ℝ)) (hi := (5491/20000 : ℝ)) (c := (3507250836178560981/3507500000000000000 : ℝ)) (alpha := (1483141508047/333212500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3507250836178560981/3507500000000000000 : ℝ)*(X 0 2+X 1 2)+(1483141508047/333212500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (399/50000 : ℝ)) (hi := (5491/20000 : ℝ)) (c := (3507250836178560981/3507500000000000000 : ℝ)) (alpha := (1483141508047/333212500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-411975517/2000000000 : ℝ)*X 0 0+(5676865341/10000000000 : ℝ)*X 0 1+(5021538461/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5413930609/10000000000 : ℝ)*X 1 0+(-2411865889/10000000000 : ℝ)*X 1 1+(1004307723/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1353482689/2500000000 : ℝ)*X 2 0+(5021538513/10000000000 : ℝ)*X 2 1+(-1205932913/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((172371553/400000000 : ℝ)*X 0 0+(738907743/2000000000 : ℝ)*X 0 1+(5022632779/10000000000 : ℝ)*X 0 2+(172371553/400000000 : ℝ)*X 1 0+(738907743/2000000000 : ℝ)*X 1 1+(5022632779/10000000000 : ℝ)*X 1 2+(172371553/400000000 : ℝ)*X 2 0+(738907743/2000000000 : ℝ)*X 2 1+(5022632779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2060560489/10000000000 : ℝ)*X 0 0+(2515081989/5000000000 : ℝ)*X 0 1+(5668074997/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2622569533/5000000000 : ℝ)*X 1 0+(-1765328893/10000000000 : ℝ)*X 1 1+(283403759/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1311284853/2500000000 : ℝ)*X 2 0+(708509493/1250000000 : ℝ)*X 2 1+(-441331823/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4310671159/10000000000 : ℝ)*X 0 0+(5005152949/10000000000 : ℝ)*X 0 1+(3712351953/10000000000 : ℝ)*X 0 2+(4310671159/10000000000 : ℝ)*X 1 0+(5005152949/10000000000 : ℝ)*X 1 1+(3712351953/10000000000 : ℝ)*X 1 2+(4310671159/10000000000 : ℝ)*X 2 0+(5005152949/10000000000 : ℝ)*X 2 1+(3712351953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10763493086019486801314710821/3332125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8545081/25000000000000 : ℝ)*(base1) + (375279753/50000000000000 : ℝ)*(base19) + (197998187/25000000000000 : ℝ)*(base23) + (313293/390625000000 : ℝ)*(upper3) + (11420847/10000000000000 : ℝ)*(upper5) + (1139464090359429/100000000000000 : ℝ)*(major0) + (1139464090359429/100000000000000 : ℝ)*(major1) + (1139464090359429/100000000000000 : ℝ)*(major2) + (1525960095726411/100000000000000 : ℝ)*(sp0) + (381490986985923/25000000000000 : ℝ)*(sp1) + (30519278130209/2000000000000 : ℝ)*(sp2) + (376480525770867/50000000000000 : ℝ)*(sp3) + (4636957111/100000000000000 : ℝ)*(sp4) + (1144409817/50000000000000 : ℝ)*(sp7) + (188240843635423/25000000000000 : ℝ)*(f.failure) + (762982349251599/50000000000000 : ℝ)*(f.sum) + (7418223613667/66642500000000000000000000000 : ℝ)*base65 + (39796705297308307131/6664250000000000000000000000000000 : ℝ)*base67 + (26227026482999057131/6664250000000000000000000000000000 : ℝ)*base69 + (17654564074172557131/6664250000000000000000000000000000 : ℝ)*base71 + (39183741733153/16660625000000000000000000000 : ℝ)*base73 + (15342843816650557131/6664250000000000000000000000000000 : ℝ)*base75 + (36560163162621557131/6664250000000000000000000000000000 : ℝ)*base77 + (13109102121649057131/6664250000000000000000000000000000 : ℝ)*base79 + (11947751693153/16660625000000000000000000000 : ℝ)*base81 + (13895701/2500000000000000000000 : ℝ)*base90 + (13895701/2500000000000000000000 : ℝ)*base92 + (13895701/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5494796520522278478566607243/1666062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (84859279/6250000000000 : ℝ)*(base19) + (1847701717/100000000000000 : ℝ)*(base23) + (52606637/50000000000000 : ℝ)*(upper2) + (231252629/100000000000000 : ℝ)*(upper3) + (21076021/25000000000000 : ℝ)*(upper5) + (1170565161770521/100000000000000 : ℝ)*(major0) + (1170565161770521/100000000000000 : ℝ)*(major1) + (1170565161770521/100000000000000 : ℝ)*(major2) + (1192820871/20000000000000 : ℝ)*(sp1) + (2348504787/20000000000000 : ℝ)*(sp2) + (195951887607047/12500000000000 : ℝ)*(sp4) + (783803889501779/50000000000000 : ℝ)*(sp5) + (391900377657681/25000000000000 : ℝ)*(sp6) + (9668938909361/1250000000000 : ℝ)*(sp7) + (9668938909361/1250000000000 : ℝ)*(f.failure) + (195951887607047/12500000000000 : ℝ)*(f.sum) + (1688558992373/4165156250000000000000000000 : ℝ)*base65 + (18620225407319580919/6664250000000000000000000000000000 : ℝ)*base67 + (30019940418757580919/6664250000000000000000000000000000 : ℝ)*base69 + (1291308784215830919/6664250000000000000000000000000000 : ℝ)*base71 + (13165100443939/133285000000000000000000000000 : ℝ)*base74 + (14364150467167669081/6664250000000000000000000000000000 : ℝ)*base76 + (49476234581184580919/6664250000000000000000000000000000 : ℝ)*base77 + (39334791100911830919/6664250000000000000000000000000000 : ℝ)*base79 + (177300555236937/66642500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (318293/125000000000000000000 : ℝ)*base89 + (318293/125000000000000000000 : ℝ)*base91 + (318293/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1237_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5491/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (399/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1233/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1001/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1237_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1237_s2_0 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108171737/10000000000 : ℝ)*x 0 + (274682187/500000000 : ℝ)*x 1 + (1293491339/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108171737/10000000000 : ℝ)^4215 ≤ (6396106787539/50000000000000 : ℝ)^3191 := by
    have hnat : (2108171737 : ℕ)^4215*50000000000000^3191 ≤ 6396106787539^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108171737 10000000000 6396106787539 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (274682187/500000000 : ℝ)^4215 ≤ (1813180564347/4000000000000 : ℝ)^3191 := by
    have hnat : (274682187 : ℕ)^4215*4000000000000^3191 ≤ 1813180564347^3191*500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      274682187 500000000 1813180564347 4000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293491339/2500000000 : ℝ)^4215 ≤ (41878272298801/100000000000000 : ℝ)^3191 := by
    have hnat : (1293491339 : ℕ)^4215*100000000000000^3191 ≤ 41878272298801^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293491339 2500000000 41878272298801 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108171737/10000000000 : ℝ), (274682187/500000000 : ℝ), (1293491339/2500000000 : ℝ)] ![(6396106787539/50000000000000 : ℝ), (1813180564347/4000000000000 : ℝ), (41878272298801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108171737/10000000000 : ℝ)|^4215 ≤ (6396106787539/50000000000000 : ℝ)^3191
        have hw : |(-2108171737/10000000000 : ℝ)|=(2108171737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(274682187/500000000 : ℝ)|^4215 ≤ (1813180564347/4000000000000 : ℝ)^3191
        have hw : |(274682187/500000000 : ℝ)|=(274682187/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293491339/2500000000 : ℝ)|^4215 ≤ (41878272298801/100000000000000 : ℝ)^3191
        have hw : |(1293491339/2500000000 : ℝ)|=(1293491339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s2_1 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5369889641/10000000000 : ℝ)*x 0 + (-1136895871/5000000000 : ℝ)*x 1 + (1293491333/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369889641/10000000000 : ℝ)^4215 ≤ (21992801956283/50000000000000 : ℝ)^3191 := by
    have hnat : (5369889641 : ℕ)^4215*50000000000000^3191 ≤ 21992801956283^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369889641 10000000000 21992801956283 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1136895871/5000000000 : ℝ)^4215 ≤ (1767015503039/12500000000000 : ℝ)^3191 := by
    have hnat : (1136895871 : ℕ)^4215*12500000000000^3191 ≤ 1767015503039^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1136895871 5000000000 1767015503039 12500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1293491333/2500000000 : ℝ)^4215 ≤ (20939136021103/50000000000000 : ℝ)^3191 := by
    have hnat : (1293491333 : ℕ)^4215*50000000000000^3191 ≤ 20939136021103^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1293491333 2500000000 20939136021103 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369889641/10000000000 : ℝ), (-1136895871/5000000000 : ℝ), (1293491333/2500000000 : ℝ)] ![(21992801956283/50000000000000 : ℝ), (1767015503039/12500000000000 : ℝ), (20939136021103/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369889641/10000000000 : ℝ)|^4215 ≤ (21992801956283/50000000000000 : ℝ)^3191
        have hw : |(5369889641/10000000000 : ℝ)|=(5369889641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1136895871/5000000000 : ℝ)|^4215 ≤ (1767015503039/12500000000000 : ℝ)^3191
        have hw : |(-1136895871/5000000000 : ℝ)|=(1136895871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1293491333/2500000000 : ℝ)|^4215 ≤ (20939136021103/50000000000000 : ℝ)^3191
        have hw : |(1293491333/2500000000 : ℝ)|=(1293491333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s2_2 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (214795579/400000000 : ℝ)*x 0 + (161686421/312500000 : ℝ)*x 1 + (-2273791779/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214795579/400000000 : ℝ)^4215 ≤ (10996400529123/25000000000000 : ℝ)^3191 := by
    have hnat : (214795579 : ℕ)^4215*25000000000000^3191 ≤ 10996400529123^3191*400000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214795579 400000000 10996400529123 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161686421/312500000 : ℝ)^4215 ≤ (41878273539007/100000000000000 : ℝ)^3191 := by
    have hnat : (161686421 : ℕ)^4215*100000000000000^3191 ≤ 41878273539007^3191*312500000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161686421 312500000 41878273539007 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273791779/10000000000 : ℝ)^4215 ≤ (14136124328157/100000000000000 : ℝ)^3191 := by
    have hnat : (2273791779 : ℕ)^4215*100000000000000^3191 ≤ 14136124328157^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273791779 10000000000 14136124328157 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(214795579/400000000 : ℝ), (161686421/312500000 : ℝ), (-2273791779/10000000000 : ℝ)] ![(10996400529123/25000000000000 : ℝ), (41878273539007/100000000000000 : ℝ), (14136124328157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(214795579/400000000 : ℝ)|^4215 ≤ (10996400529123/25000000000000 : ℝ)^3191
        have hw : |(214795579/400000000 : ℝ)|=(214795579/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(161686421/312500000 : ℝ)|^4215 ≤ (41878273539007/100000000000000 : ℝ)^3191
        have hw : |(161686421/312500000 : ℝ)|=(161686421/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2273791779/10000000000 : ℝ)|^4215 ≤ (14136124328157/100000000000000 : ℝ)^3191
        have hw : |(-2273791779/10000000000 : ℝ)|=(2273791779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s2_3 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1085659311/2500000000 : ℝ)*x 0 + (201521023/500000000 : ℝ)*x 1 + (116957117/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085659311/2500000000 : ℝ)^4215 ≤ (6645654268309/20000000000000 : ℝ)^3191 := by
    have hnat : (1085659311 : ℕ)^4215*20000000000000^3191 ≤ 6645654268309^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085659311 2500000000 6645654268309 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (201521023/500000000 : ℝ)^4215 ≤ (1881855615113/6250000000000 : ℝ)^3191 := by
    have hnat : (201521023 : ℕ)^4215*6250000000000^3191 ≤ 1881855615113^3191*500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      201521023 500000000 1881855615113 6250000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (116957117/250000000 : ℝ)^4215 ≤ (36662038812067/100000000000000 : ℝ)^3191 := by
    have hnat : (116957117 : ℕ)^4215*100000000000000^3191 ≤ 36662038812067^3191*250000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      116957117 250000000 36662038812067 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085659311/2500000000 : ℝ), (201521023/500000000 : ℝ), (116957117/250000000 : ℝ)] ![(6645654268309/20000000000000 : ℝ), (1881855615113/6250000000000 : ℝ), (36662038812067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085659311/2500000000 : ℝ)|^4215 ≤ (6645654268309/20000000000000 : ℝ)^3191
        have hw : |(1085659311/2500000000 : ℝ)|=(1085659311/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(201521023/500000000 : ℝ)|^4215 ≤ (1881855615113/6250000000000 : ℝ)^3191
        have hw : |(201521023/500000000 : ℝ)|=(201521023/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(116957117/250000000 : ℝ)|^4215 ≤ (36662038812067/100000000000000 : ℝ)^3191
        have hw : |(116957117/250000000 : ℝ)|=(116957117/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s2_4 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2108251203/10000000000 : ℝ)*x 0 + (2588013773/5000000000 : ℝ)*x 1 + (109831243/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2108251203/10000000000 : ℝ)^4215 ≤ (3198212627283/25000000000000 : ℝ)^3191 := by
    have hnat : (2108251203 : ℕ)^4215*25000000000000^3191 ≤ 3198212627283^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2108251203 10000000000 3198212627283 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588013773/5000000000 : ℝ)^4215 ≤ (10475080369937/25000000000000 : ℝ)^3191 := by
    have hnat : (2588013773 : ℕ)^4215*25000000000000^3191 ≤ 10475080369937^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588013773 5000000000 10475080369937 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (109831243/200000000 : ℝ)^4215 ≤ (45306827993499/100000000000000 : ℝ)^3191 := by
    have hnat : (109831243 : ℕ)^4215*100000000000000^3191 ≤ 45306827993499^3191*200000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109831243 200000000 45306827993499 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2108251203/10000000000 : ℝ), (2588013773/5000000000 : ℝ), (109831243/200000000 : ℝ)] ![(3198212627283/25000000000000 : ℝ), (10475080369937/25000000000000 : ℝ), (45306827993499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2108251203/10000000000 : ℝ)|^4215 ≤ (3198212627283/25000000000000 : ℝ)^3191
        have hw : |(-2108251203/10000000000 : ℝ)|=(2108251203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588013773/5000000000 : ℝ)|^4215 ≤ (10475080369937/25000000000000 : ℝ)^3191
        have hw : |(2588013773/5000000000 : ℝ)|=(2588013773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(109831243/200000000 : ℝ)|^4215 ≤ (45306827993499/100000000000000 : ℝ)^3191
        have hw : |(109831243/200000000 : ℝ)|=(109831243/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s2_5 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (82629339/156250000 : ℝ)*x 0 + (-978097359/5000000000 : ℝ)*x 1 + (5491562193/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82629339/156250000 : ℝ)^4215 ≤ (43104746356791/100000000000000 : ℝ)^3191 := by
    have hnat : (82629339 : ℕ)^4215*100000000000000^3191 ≤ 43104746356791^3191*156250000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82629339 156250000 43104746356791 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (978097359/5000000000 : ℝ)^4215 ≤ (1448553144887/12500000000000 : ℝ)^3191 := by
    have hnat : (978097359 : ℕ)^4215*12500000000000^3191 ≤ 1448553144887^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978097359 5000000000 1448553144887 12500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5491562193/10000000000 : ℝ)^4215 ≤ (5663353557763/12500000000000 : ℝ)^3191 := by
    have hnat : (5491562193 : ℕ)^4215*12500000000000^3191 ≤ 5663353557763^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5491562193 10000000000 5663353557763 12500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82629339/156250000 : ℝ), (-978097359/5000000000 : ℝ), (5491562193/10000000000 : ℝ)] ![(43104746356791/100000000000000 : ℝ), (1448553144887/12500000000000 : ℝ), (5663353557763/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82629339/156250000 : ℝ)|^4215 ≤ (43104746356791/100000000000000 : ℝ)^3191
        have hw : |(82629339/156250000 : ℝ)|=(82629339/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-978097359/5000000000 : ℝ)|^4215 ≤ (1448553144887/12500000000000 : ℝ)^3191
        have hw : |(-978097359/5000000000 : ℝ)|=(978097359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5491562193/10000000000 : ℝ)|^4215 ≤ (5663353557763/12500000000000 : ℝ)^3191
        have hw : |(5491562193/10000000000 : ℝ)|=(5491562193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s2_6 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1322069467/2500000000 : ℝ)*x 0 + (2745781133/5000000000 : ℝ)*x 1 + (-97809719/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322069467/2500000000 : ℝ)^4215 ≤ (43104748208659/100000000000000 : ℝ)^3191 := by
    have hnat : (1322069467 : ℕ)^4215*100000000000000^3191 ≤ 43104748208659^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322069467 2500000000 43104748208659 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745781133/5000000000 : ℝ)^4215 ≤ (45306829257643/100000000000000 : ℝ)^3191 := by
    have hnat : (2745781133 : ℕ)^4215*100000000000000^3191 ≤ 45306829257643^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745781133 5000000000 45306829257643 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (97809719/500000000 : ℝ)^4215 ≤ (5794211257127/50000000000000 : ℝ)^3191 := by
    have hnat : (97809719 : ℕ)^4215*50000000000000^3191 ≤ 5794211257127^3191*500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      97809719 500000000 5794211257127 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322069467/2500000000 : ℝ), (2745781133/5000000000 : ℝ), (-97809719/500000000 : ℝ)] ![(43104748208659/100000000000000 : ℝ), (45306829257643/100000000000000 : ℝ), (5794211257127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322069467/2500000000 : ℝ)|^4215 ≤ (43104748208659/100000000000000 : ℝ)^3191
        have hw : |(1322069467/2500000000 : ℝ)|=(1322069467/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745781133/5000000000 : ℝ)|^4215 ≤ (45306829257643/100000000000000 : ℝ)^3191
        have hw : |(2745781133/5000000000 : ℝ)|=(2745781133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-97809719/500000000 : ℝ)|^4215 ≤ (5794211257127/50000000000000 : ℝ)^3191
        have hw : |(-97809719/500000000 : ℝ)|=(97809719/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s2_7 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2171398873/5000000000 : ℝ)*x 0 + (2337052817/5000000000 : ℝ)*x 1 + (2017319267/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2171398873/5000000000 : ℝ)^4215 ≤ (33229893554981/100000000000000 : ℝ)^3191 := by
    have hnat : (2171398873 : ℕ)^4215*100000000000000^3191 ≤ 33229893554981^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2171398873 5000000000 33229893554981 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2337052817/5000000000 : ℝ)^4215 ≤ (36618785872393/100000000000000 : ℝ)^3191 := by
    have hnat : (2337052817 : ℕ)^4215*100000000000000^3191 ≤ 36618785872393^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337052817 5000000000 36618785872393 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2017319267/5000000000 : ℝ)^4215 ≤ (30151320550157/100000000000000 : ℝ)^3191 := by
    have hnat : (2017319267 : ℕ)^4215*100000000000000^3191 ≤ 30151320550157^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017319267 5000000000 30151320550157 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2171398873/5000000000 : ℝ), (2337052817/5000000000 : ℝ), (2017319267/5000000000 : ℝ)] ![(33229893554981/100000000000000 : ℝ), (36618785872393/100000000000000 : ℝ), (30151320550157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2171398873/5000000000 : ℝ)|^4215 ≤ (33229893554981/100000000000000 : ℝ)^3191
        have hw : |(2171398873/5000000000 : ℝ)|=(2171398873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2337052817/5000000000 : ℝ)|^4215 ≤ (36618785872393/100000000000000 : ℝ)^3191
        have hw : |(2337052817/5000000000 : ℝ)|=(2337052817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2017319267/5000000000 : ℝ)|^4215 ≤ (30151320550157/100000000000000 : ℝ)^3191
        have hw : |(2017319267/5000000000 : ℝ)|=(2017319267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1237_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1001/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1233/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (9479/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4059/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1001/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1233/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1001/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1233/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1001/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1233/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1001/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1233/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1001/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1233/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1001/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1233/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1233/20000 : ℝ) ^ (8429/2048 : ℝ) ≤ (1046405866079697/100000000000000000000 : ℝ) := by
    have hpowers : (1233/20000 : ℝ)^8429 ≤ (1046405866079697/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1233 : ℕ)^8429*100000000000000000000^2048 ≤ 1046405866079697^2048*20000^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1233 20000 1046405866079697 100000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1233/20000 : ℝ)) (X := (1046405866079697/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (1001/5000 : ℝ) ^ (8429/2048 : ℝ) ≤ (833489008425219/625000000000000000 : ℝ) := by
    have hpowers : (1001/5000 : ℝ)^8429 ≤ (833489008425219/625000000000000000 : ℝ)^2048 := by
      have hnat : (1001 : ℕ)^8429*625000000000000000^2048 ≤ 833489008425219^2048*5000^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1001 5000 833489008425219 625000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1001/5000 : ℝ)) (X := (833489008425219/625000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001046405866079697/50000000000000000000 : ℝ) ≤ (10000050848789599/10000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (50001046405866079697/50000000000000000000 : ℝ)^2048 ≤ (10000050848789599/10000000000000000 : ℝ)^8429 := by
      have hnat : (50001046405866079697 : ℕ)^2048*10000000000000000^8429 ≤ 10000050848789599^8429*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001046405866079697 50000000000000000000 10000050848789599 10000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000050848789599/10000000000000000 : ℝ)) (X := (50001046405866079697/50000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100134404647214114737/100000000000000000000 : ℝ) ≤ (10003263979014539/10000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (100134404647214114737/100000000000000000000 : ℝ)^2048 ≤ (10003263979014539/10000000000000000 : ℝ)^8429 := by
      have hnat : (100134404647214114737 : ℕ)^2048*10000000000000000^8429 ≤ 10003263979014539^8429*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100134404647214114737 100000000000000000000 10003263979014539 10000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003263979014539/10000000000000000 : ℝ)) (X := (100134404647214114737/100000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (313333489008425219/312500000000000000 : ℝ) ≤ (10006477109239479/10000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (313333489008425219/312500000000000000 : ℝ)^2048 ≤ (10006477109239479/10000000000000000 : ℝ)^8429 := by
      have hnat : (313333489008425219 : ℕ)^2048*10000000000000000^8429 ≤ 10006477109239479^8429*312500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        313333489008425219 312500000000000000 10006477109239479 10000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006477109239479/10000000000000000 : ℝ)) (X := (313333489008425219/312500000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1046405866079697/100000000000000000000 : ℝ) ≤ ((27702217322861276789/27710000000000000000 : ℝ)+2*(160656511247/69275000000000 : ℝ)*(1233/20000 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (27702217322861276789/27710000000000000000 : ℝ)+2*(160656511247/69275000000000 : ℝ)*(1233/20000 : ℝ)=(10000050848789599/10000000000000000 : ℝ) by norm_num, show 1+2*(1046405866079697/100000000000000000000 : ℝ)=(50001046405866079697/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(833489008425219/625000000000000000 : ℝ)+(1046405866079697/100000000000000000000 : ℝ) ≤ ((27702217322861276789/27710000000000000000 : ℝ)+(160656511247/69275000000000 : ℝ)*((1001/5000 : ℝ)+(1233/20000 : ℝ)))^(8429/2048 : ℝ) := by
    rw [show (27702217322861276789/27710000000000000000 : ℝ)+(160656511247/69275000000000 : ℝ)*((1001/5000 : ℝ)+(1233/20000 : ℝ))=(10003263979014539/10000000000000000 : ℝ) by norm_num, show 1+(833489008425219/625000000000000000 : ℝ)+(1046405866079697/100000000000000000000 : ℝ)=(100134404647214114737/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(833489008425219/625000000000000000 : ℝ) ≤ ((27702217322861276789/27710000000000000000 : ℝ)+2*(160656511247/69275000000000 : ℝ)*(1001/5000 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (27702217322861276789/27710000000000000000 : ℝ)+2*(160656511247/69275000000000 : ℝ)*(1001/5000 : ℝ)=(10006477109239479/10000000000000000 : ℝ) by norm_num, show 1+2*(833489008425219/625000000000000000 : ℝ)=(313333489008425219/312500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27702217322861276789/27710000000000000000 : ℝ)*(X 1 0+X 2 0)+(160656511247/69275000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (1233/20000 : ℝ)) (hi := (1001/5000 : ℝ)) (c := (27702217322861276789/27710000000000000000 : ℝ)) (alpha := (160656511247/69275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27702217322861276789/27710000000000000000 : ℝ)*(X 0 1+X 2 1)+(160656511247/69275000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (1233/20000 : ℝ)) (hi := (1001/5000 : ℝ)) (c := (27702217322861276789/27710000000000000000 : ℝ)) (alpha := (160656511247/69275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27702217322861276789/27710000000000000000 : ℝ)*(X 0 2+X 1 2)+(160656511247/69275000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (1233/20000 : ℝ)) (hi := (1001/5000 : ℝ)) (c := (27702217322861276789/27710000000000000000 : ℝ)) (alpha := (160656511247/69275000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2108171737/10000000000 : ℝ)*X 0 0+(274682187/500000000 : ℝ)*X 0 1+(1293491339/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5369889641/10000000000 : ℝ)*X 1 0+(-1136895871/5000000000 : ℝ)*X 1 1+(1293491333/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((214795579/400000000 : ℝ)*X 2 0+(161686421/312500000 : ℝ)*X 2 1+(-2273791779/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1085659311/2500000000 : ℝ)*X 0 0+(201521023/500000000 : ℝ)*X 0 1+(116957117/250000000 : ℝ)*X 0 2+(1085659311/2500000000 : ℝ)*X 1 0+(201521023/500000000 : ℝ)*X 1 1+(116957117/250000000 : ℝ)*X 1 2+(1085659311/2500000000 : ℝ)*X 2 0+(201521023/500000000 : ℝ)*X 2 1+(116957117/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2108251203/10000000000 : ℝ)*X 0 0+(2588013773/5000000000 : ℝ)*X 0 1+(109831243/200000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((82629339/156250000 : ℝ)*X 1 0+(-978097359/5000000000 : ℝ)*X 1 1+(5491562193/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1322069467/2500000000 : ℝ)*X 2 0+(2745781133/5000000000 : ℝ)*X 2 1+(-97809719/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2171398873/5000000000 : ℝ)*X 0 0+(2337052817/5000000000 : ℝ)*X 0 1+(2017319267/5000000000 : ℝ)*X 0 2+(2171398873/5000000000 : ℝ)*X 1 0+(2337052817/5000000000 : ℝ)*X 1 1+(2017319267/5000000000 : ℝ)*X 1 2+(2171398873/5000000000 : ℝ)*X 2 0+(2337052817/5000000000 : ℝ)*X 2 1+(2017319267/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8109681483745463860555417869/1385500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (280726597/25000000000000 : ℝ)*(base19) + (37804619/4000000000000 : ℝ)*(base23) + (43544187/100000000000000 : ℝ)*(lower2) + (188155507/100000000000000 : ℝ)*(upper3) + (36986079/50000000000000 : ℝ)*(upper5) + (2335856735025907/100000000000000 : ℝ)*(major0) + (2335856735025907/100000000000000 : ℝ)*(major1) + (2335856735025907/100000000000000 : ℝ)*(major2) + (782039239962403/25000000000000 : ℝ)*(sp0) + (312816673930157/10000000000000 : ℝ)*(sp1) + (1564083458546241/50000000000000 : ℝ)*(sp2) + (385884708951309/25000000000000 : ℝ)*(sp3) + (2180471669/20000000000000 : ℝ)*(sp4) + (1315386039/20000000000000 : ℝ)*(sp7) + (1543545412735431/100000000000000 : ℝ)*(f.failure) + (1564083931103979/50000000000000 : ℝ)*(f.sum) + (11676537874509/13855000000000000000000000000 : ℝ)*base66 + (2613251914815627377/2771000000000000000000000000000000 : ℝ)*base68 + (2333108356552372623/2771000000000000000000000000000000 : ℝ)*base69 + (8331872639479627377/2771000000000000000000000000000000 : ℝ)*base72 + (26988738859817/6927500000000000000000000000 : ℝ)*base74 + (15613238832925627377/2771000000000000000000000000000000 : ℝ)*base76 + (3830079936659627377/2771000000000000000000000000000000 : ℝ)*base78 + (8164327430350372623/2771000000000000000000000000000000 : ℝ)*base79 + (51459135001/54121093750000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (80049203/10000000000000000000000 : ℝ)*base89 + (80049203/10000000000000000000000 : ℝ)*base91 + (80049203/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2620124311405898488368282513/692750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (569623933/50000000000000 : ℝ)*(base19) + (722301789/50000000000000 : ℝ)*(base23) + (2809367/5000000000000 : ℝ)*(upper2) + (171245059/100000000000000 : ℝ)*(upper3) + (2906621/4000000000000 : ℝ)*(upper5) + (2366512923215361/100000000000000 : ℝ)*(major0) + (2366512923215361/100000000000000 : ℝ)*(major1) + (2366512923215361/100000000000000 : ℝ)*(major2) + (11209349241/100000000000000 : ℝ)*(sp1) + (8715936493/50000000000000 : ℝ)*(sp2) + (792305637599041/25000000000000 : ℝ)*(sp4) + (198075637612441/6250000000000 : ℝ)*(sp5) + (7923009184799/250000000000 : ℝ)*(sp6) + (781901584980483/50000000000000 : ℝ)*(sp7) + (781901584980483/50000000000000 : ℝ)*(f.failure) + (792305637599041/25000000000000 : ℝ)*(f.sum) + (17091762635113/3463750000000000000000000000 : ℝ)*base66 + (6389275334996355829/2771000000000000000000000000000000 : ℝ)*base67 + (8169253631420355829/2771000000000000000000000000000000 : ℝ)*base69 + (4867624730041355829/2771000000000000000000000000000000 : ℝ)*base71 + (25476565757651/6927500000000000000000000000 : ℝ)*base74 + (30338333711800355829/2771000000000000000000000000000000 : ℝ)*base75 + (17394222647261644171/2771000000000000000000000000000000 : ℝ)*base78 + (13442524844588355829/2771000000000000000000000000000000 : ℝ)*base79 + (1592660972791/6927500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (35426079/5000000000000000000000 : ℝ)*base89 + (35426079/5000000000000000000000 : ℝ)*base91 + (35426079/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1237_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1001/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1233/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9479/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4059/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1237_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1237_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9479/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4059/25000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1237_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1237_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1237_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9479/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4059/25000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1237_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
