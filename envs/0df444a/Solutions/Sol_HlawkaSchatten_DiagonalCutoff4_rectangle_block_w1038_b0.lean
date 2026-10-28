-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1038_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:44:31.739288+00:00
-- url     : https://prove2.me/submissions/1543ee6c-111a-429a-a9f7-2462446b4ef8

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
theorem support_rectangle_w1038_s0_0 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (342516101/625000000 : ℝ)*x 0 + (-2700167819/10000000000 : ℝ)*x 1 + (4795677003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (342516101/625000000 : ℝ)^8231 ≤ (11225968577233/25000000000000 : ℝ)^6183 := by
    have hnat : (342516101 : ℕ)^8231*25000000000000^6183 ≤ 11225968577233^6183*625000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      342516101 625000000 11225968577233 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2700167819/10000000000 : ℝ)^8231 ≤ (4375119045647/25000000000000 : ℝ)^6183 := by
    have hnat : (2700167819 : ℕ)^8231*25000000000000^6183 ≤ 4375119045647^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2700167819 10000000000 4375119045647 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4795677003/10000000000 : ℝ)^8231 ≤ (37595649505801/100000000000000 : ℝ)^6183 := by
    have hnat : (4795677003 : ℕ)^8231*100000000000000^6183 ≤ 37595649505801^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4795677003 10000000000 37595649505801 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(342516101/625000000 : ℝ), (-2700167819/10000000000 : ℝ), (4795677003/10000000000 : ℝ)] ![(11225968577233/25000000000000 : ℝ), (4375119045647/25000000000000 : ℝ), (37595649505801/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(342516101/625000000 : ℝ)|^8231 ≤ (11225968577233/25000000000000 : ℝ)^6183
        have hw : |(342516101/625000000 : ℝ)|=(342516101/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2700167819/10000000000 : ℝ)|^8231 ≤ (4375119045647/25000000000000 : ℝ)^6183
        have hw : |(-2700167819/10000000000 : ℝ)|=(2700167819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4795677003/10000000000 : ℝ)|^8231 ≤ (37595649505801/100000000000000 : ℝ)^6183
        have hw : |(4795677003/10000000000 : ℝ)|=(4795677003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s0_1 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5482405757/10000000000 : ℝ)*x 0 + (4787352611/10000000000 : ℝ)*x 1 + (-1353757293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5482405757/10000000000 : ℝ)^8231 ≤ (44927307269877/100000000000000 : ℝ)^6183 := by
    have hnat : (5482405757 : ℕ)^8231*100000000000000^6183 ≤ 44927307269877^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5482405757 10000000000 44927307269877 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4787352611/10000000000 : ℝ)^8231 ≤ (37508799744429/100000000000000 : ℝ)^6183 := by
    have hnat : (4787352611 : ℕ)^8231*100000000000000^6183 ≤ 37508799744429^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4787352611 10000000000 37508799744429 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353757293/5000000000 : ℝ)^8231 ≤ (8781946487213/50000000000000 : ℝ)^6183 := by
    have hnat : (1353757293 : ℕ)^8231*50000000000000^6183 ≤ 8781946487213^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353757293 5000000000 8781946487213 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5482405757/10000000000 : ℝ), (4787352611/10000000000 : ℝ), (-1353757293/5000000000 : ℝ)] ![(44927307269877/100000000000000 : ℝ), (37508799744429/100000000000000 : ℝ), (8781946487213/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5482405757/10000000000 : ℝ)|^8231 ≤ (44927307269877/100000000000000 : ℝ)^6183
        have hw : |(5482405757/10000000000 : ℝ)|=(5482405757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4787352611/10000000000 : ℝ)|^8231 ≤ (37508799744429/100000000000000 : ℝ)^6183
        have hw : |(4787352611/10000000000 : ℝ)|=(4787352611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1353757293/5000000000 : ℝ)|^8231 ≤ (8781946487213/50000000000000 : ℝ)^6183
        have hw : |(-1353757293/5000000000 : ℝ)|=(1353757293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s0_2 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-386125773/2000000000 : ℝ)*x 0 + (4801055007/10000000000 : ℝ)*x 1 + (3021811213/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (386125773/2000000000 : ℝ)^8231 ≤ (5598481456633/50000000000000 : ℝ)^6183 := by
    have hnat : (386125773 : ℕ)^8231*50000000000000^6183 ≤ 5598481456633^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386125773 2000000000 5598481456633 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4801055007/10000000000 : ℝ)^8231 ≤ (9412946418839/25000000000000 : ℝ)^6183 := by
    have hnat : (4801055007 : ℕ)^8231*25000000000000^6183 ≤ 9412946418839^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4801055007 10000000000 9412946418839 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3021811213/5000000000 : ℝ)^8231 ≤ (12787812849201/25000000000000 : ℝ)^6183 := by
    have hnat : (3021811213 : ℕ)^8231*25000000000000^6183 ≤ 12787812849201^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3021811213 5000000000 12787812849201 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-386125773/2000000000 : ℝ), (4801055007/10000000000 : ℝ), (3021811213/5000000000 : ℝ)] ![(5598481456633/50000000000000 : ℝ), (9412946418839/25000000000000 : ℝ), (12787812849201/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-386125773/2000000000 : ℝ)|^8231 ≤ (5598481456633/50000000000000 : ℝ)^6183
        have hw : |(-386125773/2000000000 : ℝ)|=(386125773/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4801055007/10000000000 : ℝ)|^8231 ≤ (9412946418839/25000000000000 : ℝ)^6183
        have hw : |(4801055007/10000000000 : ℝ)|=(4801055007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3021811213/5000000000 : ℝ)|^8231 ≤ (12787812849201/25000000000000 : ℝ)^6183
        have hw : |(3021811213/5000000000 : ℝ)|=(3021811213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s0_3 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5166846901/10000000000 : ℝ)*x 0 + (-175559411/1250000000 : ℝ)*x 1 + (377726411/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5166846901/10000000000 : ℝ)^8231 ≤ (8303612505563/20000000000000 : ℝ)^6183 := by
    have hnat : (5166846901 : ℕ)^8231*20000000000000^6183 ≤ 8303612505563^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5166846901 10000000000 8303612505563 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175559411/1250000000 : ℝ)^8231 ≤ (7330684374469/100000000000000 : ℝ)^6183 := by
    have hnat : (175559411 : ℕ)^8231*100000000000000^6183 ≤ 7330684374469^6183*1250000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175559411 1250000000 7330684374469 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (377726411/625000000 : ℝ)^8231 ≤ (5115125308687/10000000000000 : ℝ)^6183 := by
    have hnat : (377726411 : ℕ)^8231*10000000000000^6183 ≤ 5115125308687^6183*625000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377726411 625000000 5115125308687 10000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5166846901/10000000000 : ℝ), (-175559411/1250000000 : ℝ), (377726411/625000000 : ℝ)] ![(8303612505563/20000000000000 : ℝ), (7330684374469/100000000000000 : ℝ), (5115125308687/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5166846901/10000000000 : ℝ)|^8231 ≤ (8303612505563/20000000000000 : ℝ)^6183
        have hw : |(5166846901/10000000000 : ℝ)|=(5166846901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-175559411/1250000000 : ℝ)|^8231 ≤ (7330684374469/100000000000000 : ℝ)^6183
        have hw : |(-175559411/1250000000 : ℝ)|=(175559411/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(377726411/625000000 : ℝ)|^8231 ≤ (5115125308687/10000000000000 : ℝ)^6183
        have hw : |(377726411/625000000 : ℝ)|=(377726411/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s0_4 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (206673651/400000000 : ℝ)*x 0 + (6043627857/10000000000 : ℝ)*x 1 + (-280895077/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (206673651/400000000 : ℝ)^8231 ≤ (4151800234611/10000000000000 : ℝ)^6183 := by
    have hnat : (206673651 : ℕ)^8231*10000000000000^6183 ≤ 4151800234611^6183*400000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      206673651 400000000 4151800234611 10000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6043627857/10000000000 : ℝ)^8231 ≤ (25575656294227/50000000000000 : ℝ)^6183 := by
    have hnat : (6043627857 : ℕ)^8231*50000000000000^6183 ≤ 25575656294227^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6043627857 10000000000 25575656294227 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (280895077/2000000000 : ℝ)^8231 ≤ (7330685048463/100000000000000 : ℝ)^6183 := by
    have hnat : (280895077 : ℕ)^8231*100000000000000^6183 ≤ 7330685048463^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      280895077 2000000000 7330685048463 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(206673651/400000000 : ℝ), (6043627857/10000000000 : ℝ), (-280895077/2000000000 : ℝ)] ![(4151800234611/10000000000000 : ℝ), (25575656294227/50000000000000 : ℝ), (7330685048463/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(206673651/400000000 : ℝ)|^8231 ≤ (4151800234611/10000000000000 : ℝ)^6183
        have hw : |(206673651/400000000 : ℝ)|=(206673651/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6043627857/10000000000 : ℝ)|^8231 ≤ (25575656294227/50000000000000 : ℝ)^6183
        have hw : |(6043627857/10000000000 : ℝ)|=(6043627857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-280895077/2000000000 : ℝ)|^8231 ≤ (7330685048463/100000000000000 : ℝ)^6183
        have hw : |(-280895077/2000000000 : ℝ)|=(280895077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s0_5 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4220171181/10000000000 : ℝ)*x 0 + (5616461763/10000000000 : ℝ)*x 1 + (638944867/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4220171181/10000000000 : ℝ)^8231 ≤ (15856153901071/50000000000000 : ℝ)^6183 := by
    have hnat : (4220171181 : ℕ)^8231*50000000000000^6183 ≤ 15856153901071^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4220171181 10000000000 15856153901071 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5616461763/10000000000 : ℝ)^8231 ≤ (46395640327737/100000000000000 : ℝ)^6183 := by
    have hnat : (5616461763 : ℕ)^8231*100000000000000^6183 ≤ 46395640327737^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5616461763 10000000000 46395640327737 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638944867/2000000000 : ℝ)^8231 ≤ (21892051851157/100000000000000 : ℝ)^6183 := by
    have hnat : (638944867 : ℕ)^8231*100000000000000^6183 ≤ 21892051851157^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638944867 2000000000 21892051851157 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4220171181/10000000000 : ℝ), (5616461763/10000000000 : ℝ), (638944867/2000000000 : ℝ)] ![(15856153901071/50000000000000 : ℝ), (46395640327737/100000000000000 : ℝ), (21892051851157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4220171181/10000000000 : ℝ)|^8231 ≤ (15856153901071/50000000000000 : ℝ)^6183
        have hw : |(4220171181/10000000000 : ℝ)|=(4220171181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5616461763/10000000000 : ℝ)|^8231 ≤ (46395640327737/100000000000000 : ℝ)^6183
        have hw : |(5616461763/10000000000 : ℝ)|=(5616461763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(638944867/2000000000 : ℝ)|^8231 ≤ (21892051851157/100000000000000 : ℝ)^6183
        have hw : |(638944867/2000000000 : ℝ)|=(638944867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1038_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (0 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28219/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base43 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
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
  have hpowlo : (0 : ℝ) ^ (4115/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4115 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4115*1^1024 ≤ 0^1024*1^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4115/1024 : ℝ) ≤ (1258422043561358583/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4115 ≤ (1258422043561358583/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4115*50000000000000000000^1024 ≤ 1258422043561358583^1024*5^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1258422043561358583 50000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1258422043561358583/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4115 := by
      have hnat : (1 : ℕ)^1024*1^4115 ≤ 1^4115*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (51258422043561358583/50000000000000000000 : ℝ) ≤ (10062047101792297/10000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (51258422043561358583/50000000000000000000 : ℝ)^1024 ≤ (10062047101792297/10000000000000000 : ℝ)^4115 := by
      have hnat : (51258422043561358583 : ℕ)^1024*10000000000000000^4115 ≤ 10062047101792297^4115*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51258422043561358583 50000000000000000000 10062047101792297 10000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10062047101792297/10000000000000000 : ℝ)) (X := (51258422043561358583/50000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (26258422043561358583/25000000000000000000 : ℝ) ≤ (5062047101792297/5000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (26258422043561358583/25000000000000000000 : ℝ)^1024 ≤ (5062047101792297/5000000000000000 : ℝ)^4115 := by
      have hnat : (26258422043561358583 : ℕ)^1024*5000000000000000^4115 ≤ 5062047101792297^4115*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26258422043561358583 25000000000000000000 5062047101792297 5000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5062047101792297/5000000000000000 : ℝ)) (X := (26258422043561358583/25000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(62047101792297/4000000000000000 : ℝ)*(0 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(62047101792297/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1258422043561358583/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(62047101792297/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4115/1024 : ℝ) := by
    rw [show (1 : ℝ)+(62047101792297/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10062047101792297/10000000000000000 : ℝ) by norm_num, show 1+(1258422043561358583/50000000000000000000 : ℝ)+(0 : ℝ)=(51258422043561358583/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1258422043561358583/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(62047101792297/4000000000000000 : ℝ)*(2/5 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(62047101792297/4000000000000000 : ℝ)*(2/5 : ℝ)=(5062047101792297/5000000000000000 : ℝ) by norm_num, show 1+2*(1258422043561358583/50000000000000000000 : ℝ)=(26258422043561358583/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(62047101792297/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (62047101792297/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(62047101792297/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (62047101792297/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(62047101792297/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (62047101792297/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((342516101/625000000 : ℝ)*X 1 0+(-2700167819/10000000000 : ℝ)*X 1 1+(4795677003/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s0_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5482405757/10000000000 : ℝ)*X 2 0+(4787352611/10000000000 : ℝ)*X 2 1+(-1353757293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s0_1 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-386125773/2000000000 : ℝ)*X 0 0+(4801055007/10000000000 : ℝ)*X 0 1+(3021811213/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s0_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5166846901/10000000000 : ℝ)*X 1 0+(-175559411/1250000000 : ℝ)*X 1 1+(377726411/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s0_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((206673651/400000000 : ℝ)*X 2 0+(6043627857/10000000000 : ℝ)*X 2 1+(-280895077/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s0_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4220171181/10000000000 : ℝ)*X 0 0+(5616461763/10000000000 : ℝ)*X 0 1+(638944867/2000000000 : ℝ)*X 0 2+(4220171181/10000000000 : ℝ)*X 1 0+(5616461763/10000000000 : ℝ)*X 1 1+(638944867/2000000000 : ℝ)*X 1 2+(4220171181/10000000000 : ℝ)*X 2 0+(5616461763/10000000000 : ℝ)*X 2 1+(638944867/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s0_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(base43) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1057352645414856826516173/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1052919843/100000000000000 : ℝ)*(base19) + (288027649/20000000000000 : ℝ)*(base23) + (512178407/50000000000000 : ℝ)*(base39) + (173964951/100000000000000 : ℝ)*(upper2) + (451061747/100000000000000 : ℝ)*(upper5) + (608852232313501/100000000000000 : ℝ)*(major0) + (608852232313501/100000000000000 : ℝ)*(major1) + (304425603978343/50000000000000 : ℝ)*(major2) + (34348173/1000000000000 : ℝ)*(sp0) + (2317874397/100000000000000 : ℝ)*(sp1) + (160955664345541/20000000000000 : ℝ)*(sp2) + (402386916995281/50000000000000 : ℝ)*(sp3) + (402387794035939/50000000000000 : ℝ)*(sp4) + (103231235579259/25000000000000 : ℝ)*(sp5) + (103231235579259/25000000000000 : ℝ)*(f.failure) + (20119483652113/2500000000000 : ℝ)*(f.sum) + (957040241050461/400000000000000000000000000000 : ℝ)*base66 + (883016191623871/200000000000000000000000000000 : ℝ)*base67 + (621797465098203/400000000000000000000000000000 : ℝ)*base70 + (878879936623871/200000000000000000000000000000 : ℝ)*base71 + (240823929450461/400000000000000000000000000000 : ℝ)*base74 + (936664377898203/400000000000000000000000000000 : ℝ)*base76 + (32847107098203/400000000000000000000000000000 : ℝ)*base78 + (1231475698501797/400000000000000000000000000000 : ℝ)*base79 + (50502786698203/200000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (930811/500000000000000000000 : ℝ)*base89 + (930811/500000000000000000000 : ℝ)*base91 + (5930811/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1038_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28219/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1038_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1038_s1_0 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1068629973/5000000000 : ℝ)*x 0 + (716258917/1250000000 : ℝ)*x 1 + (2489976637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068629973/5000000000 : ℝ)^8231 ≤ (6409962192429/50000000000000 : ℝ)^6183 := by
    have hnat : (1068629973 : ℕ)^8231*50000000000000^6183 ≤ 6409962192429^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068629973 5000000000 6409962192429 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (716258917/1250000000 : ℝ)^8231 ≤ (2978072047719/6250000000000 : ℝ)^6183 := by
    have hnat : (716258917 : ℕ)^8231*6250000000000^6183 ≤ 2978072047719^6183*1250000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      716258917 1250000000 2978072047719 6250000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2489976637/5000000000 : ℝ)^8231 ≤ (39530922835411/100000000000000 : ℝ)^6183 := by
    have hnat : (2489976637 : ℕ)^8231*100000000000000^6183 ≤ 39530922835411^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2489976637 5000000000 39530922835411 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1068629973/5000000000 : ℝ), (716258917/1250000000 : ℝ), (2489976637/5000000000 : ℝ)] ![(6409962192429/50000000000000 : ℝ), (2978072047719/6250000000000 : ℝ), (39530922835411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1068629973/5000000000 : ℝ)|^8231 ≤ (6409962192429/50000000000000 : ℝ)^6183
        have hw : |(-1068629973/5000000000 : ℝ)|=(1068629973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(716258917/1250000000 : ℝ)|^8231 ≤ (2978072047719/6250000000000 : ℝ)^6183
        have hw : |(716258917/1250000000 : ℝ)|=(716258917/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2489976637/5000000000 : ℝ)|^8231 ≤ (39530922835411/100000000000000 : ℝ)^6183
        have hw : |(2489976637/5000000000 : ℝ)|=(2489976637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s1_1 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (678107643/1250000000 : ℝ)*x 0 + (-159017051/625000000 : ℝ)*x 1 + (622494199/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (678107643/1250000000 : ℝ)^8231 ≤ (44300635892773/100000000000000 : ℝ)^6183 := by
    have hnat : (678107643 : ℕ)^8231*100000000000000^6183 ≤ 44300635892773^6183*1250000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678107643 1250000000 44300635892773 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (159017051/625000000 : ℝ)^8231 ≤ (2021054736509/12500000000000 : ℝ)^6183 := by
    have hnat : (159017051 : ℕ)^8231*12500000000000^6183 ≤ 2021054736509^6183*625000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      159017051 625000000 2021054736509 12500000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (622494199/1250000000 : ℝ)^8231 ≤ (1976546309791/5000000000000 : ℝ)^6183 := by
    have hnat : (622494199 : ℕ)^8231*5000000000000^6183 ≤ 1976546309791^6183*1250000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      622494199 1250000000 1976546309791 5000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(678107643/1250000000 : ℝ), (-159017051/625000000 : ℝ), (622494199/1250000000 : ℝ)] ![(44300635892773/100000000000000 : ℝ), (2021054736509/12500000000000 : ℝ), (1976546309791/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(678107643/1250000000 : ℝ)|^8231 ≤ (44300635892773/100000000000000 : ℝ)^6183
        have hw : |(678107643/1250000000 : ℝ)|=(678107643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-159017051/625000000 : ℝ)|^8231 ≤ (2021054736509/12500000000000 : ℝ)^6183
        have hw : |(-159017051/625000000 : ℝ)|=(159017051/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(622494199/1250000000 : ℝ)|^8231 ≤ (1976546309791/5000000000000 : ℝ)^6183
        have hw : |(622494199/1250000000 : ℝ)|=(622494199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s1_2 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (10849723/20000000 : ℝ)*x 0 + (4979953139/10000000000 : ℝ)*x 1 + (-1272136463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10849723/20000000 : ℝ)^8231 ≤ (8860127952579/20000000000000 : ℝ)^6183 := by
    have hnat : (10849723 : ℕ)^8231*20000000000000^6183 ≤ 8860127952579^6183*20000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10849723 20000000 8860127952579 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4979953139/10000000000 : ℝ)^8231 ≤ (19765460704411/50000000000000 : ℝ)^6183 := by
    have hnat : (4979953139 : ℕ)^8231*50000000000000^6183 ≤ 19765460704411^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4979953139 10000000000 19765460704411 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1272136463/5000000000 : ℝ)^8231 ≤ (3233687764529/20000000000000 : ℝ)^6183 := by
    have hnat : (1272136463 : ℕ)^8231*20000000000000^6183 ≤ 3233687764529^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1272136463 5000000000 3233687764529 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10849723/20000000 : ℝ), (4979953139/10000000000 : ℝ), (-1272136463/5000000000 : ℝ)] ![(8860127952579/20000000000000 : ℝ), (19765460704411/50000000000000 : ℝ), (3233687764529/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10849723/20000000 : ℝ)|^8231 ≤ (8860127952579/20000000000000 : ℝ)^6183
        have hw : |(10849723/20000000 : ℝ)|=(10849723/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4979953139/10000000000 : ℝ)|^8231 ≤ (19765460704411/50000000000000 : ℝ)^6183
        have hw : |(4979953139/10000000000 : ℝ)|=(4979953139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1272136463/5000000000 : ℝ)|^8231 ≤ (3233687764529/20000000000000 : ℝ)^6183
        have hw : |(-1272136463/5000000000 : ℝ)|=(1272136463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s1_3 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4326164633/10000000000 : ℝ)*x 0 + (1828731303/5000000000 : ℝ)*x 1 + (319963817/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326164633/10000000000 : ℝ)^8231 ≤ (32776997227761/100000000000000 : ℝ)^6183 := by
    have hnat : (4326164633 : ℕ)^8231*100000000000000^6183 ≤ 32776997227761^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326164633 10000000000 32776997227761 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1828731303/5000000000 : ℝ)^8231 ≤ (13105742432851/50000000000000 : ℝ)^6183 := by
    have hnat : (1828731303 : ℕ)^8231*50000000000000^6183 ≤ 13105742432851^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1828731303 5000000000 13105742432851 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319963817/625000000 : ℝ)^8231 ≤ (4101151790087/10000000000000 : ℝ)^6183 := by
    have hnat : (319963817 : ℕ)^8231*10000000000000^6183 ≤ 4101151790087^6183*625000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319963817 625000000 4101151790087 10000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326164633/10000000000 : ℝ), (1828731303/5000000000 : ℝ), (319963817/625000000 : ℝ)] ![(32776997227761/100000000000000 : ℝ), (13105742432851/50000000000000 : ℝ), (4101151790087/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326164633/10000000000 : ℝ)|^8231 ≤ (32776997227761/100000000000000 : ℝ)^6183
        have hw : |(4326164633/10000000000 : ℝ)|=(4326164633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1828731303/5000000000 : ℝ)|^8231 ≤ (13105742432851/50000000000000 : ℝ)^6183
        have hw : |(1828731303/5000000000 : ℝ)|=(1828731303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(319963817/625000000 : ℝ)|^8231 ≤ (4101151790087/10000000000000 : ℝ)^6183
        have hw : |(319963817/625000000 : ℝ)|=(319963817/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s1_4 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-267278193/1250000000 : ℝ)*x 0 + (1247650371/2500000000 : ℝ)*x 1 + (5719203091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (267278193/1250000000 : ℝ)^8231 ≤ (12827635378067/100000000000000 : ℝ)^6183 := by
    have hnat : (267278193 : ℕ)^8231*100000000000000^6183 ≤ 12827635378067^6183*1250000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      267278193 1250000000 12827635378067 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1247650371/2500000000 : ℝ)^8231 ≤ (9910871438181/25000000000000 : ℝ)^6183 := by
    have hnat : (1247650371 : ℕ)^8231*25000000000000^6183 ≤ 9910871438181^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1247650371 2500000000 9910871438181 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5719203091/10000000000 : ℝ)^8231 ≤ (5941109856737/12500000000000 : ℝ)^6183 := by
    have hnat : (5719203091 : ℕ)^8231*12500000000000^6183 ≤ 5941109856737^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5719203091 10000000000 5941109856737 12500000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-267278193/1250000000 : ℝ), (1247650371/2500000000 : ℝ), (5719203091/10000000000 : ℝ)] ![(12827635378067/100000000000000 : ℝ), (9910871438181/25000000000000 : ℝ), (5941109856737/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-267278193/1250000000 : ℝ)|^8231 ≤ (12827635378067/100000000000000 : ℝ)^6183
        have hw : |(-267278193/1250000000 : ℝ)|=(267278193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1247650371/2500000000 : ℝ)|^8231 ≤ (9910871438181/25000000000000 : ℝ)^6183
        have hw : |(1247650371/2500000000 : ℝ)|=(1247650371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5719203091/10000000000 : ℝ)|^8231 ≤ (5941109856737/12500000000000 : ℝ)^6183
        have hw : |(5719203091/10000000000 : ℝ)|=(5719203091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s1_5 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1046713717/2000000000 : ℝ)*x 0 + (-902510919/5000000000 : ℝ)*x 1 + (285960209/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046713717/2000000000 : ℝ)^8231 ≤ (42233311105937/100000000000000 : ℝ)^6183 := by
    have hnat : (1046713717 : ℕ)^8231*100000000000000^6183 ≤ 42233311105937^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046713717 2000000000 42233311105937 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902510919/5000000000 : ℝ)^8231 ≤ (10237797981873/100000000000000 : ℝ)^6183 := by
    have hnat : (902510919 : ℕ)^8231*100000000000000^6183 ≤ 10237797981873^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902510919 5000000000 10237797981873 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (285960209/500000000 : ℝ)^8231 ≤ (47528890901573/100000000000000 : ℝ)^6183 := by
    have hnat : (285960209 : ℕ)^8231*100000000000000^6183 ≤ 47528890901573^6183*500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285960209 500000000 47528890901573 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046713717/2000000000 : ℝ), (-902510919/5000000000 : ℝ), (285960209/500000000 : ℝ)] ![(42233311105937/100000000000000 : ℝ), (10237797981873/100000000000000 : ℝ), (47528890901573/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046713717/2000000000 : ℝ)|^8231 ≤ (42233311105937/100000000000000 : ℝ)^6183
        have hw : |(1046713717/2000000000 : ℝ)|=(1046713717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-902510919/5000000000 : ℝ)|^8231 ≤ (10237797981873/100000000000000 : ℝ)^6183
        have hw : |(-902510919/5000000000 : ℝ)|=(902510919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(285960209/500000000 : ℝ)|^8231 ≤ (47528890901573/100000000000000 : ℝ)^6183
        have hw : |(285960209/500000000 : ℝ)|=(285960209/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s1_6 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1308391681/2500000000 : ℝ)*x 0 + (2859603111/5000000000 : ℝ)*x 1 + (-902510747/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1308391681/2500000000 : ℝ)^8231 ≤ (21116645556953/50000000000000 : ℝ)^6183 := by
    have hnat : (1308391681 : ℕ)^8231*50000000000000^6183 ≤ 21116645556953^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308391681 2500000000 21116645556953 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2859603111/5000000000 : ℝ)^8231 ≤ (47528913492351/100000000000000 : ℝ)^6183 := by
    have hnat : (2859603111 : ℕ)^8231*100000000000000^6183 ≤ 47528913492351^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2859603111 5000000000 47528913492351 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (902510747/5000000000 : ℝ)^8231 ≤ (10237795384491/100000000000000 : ℝ)^6183 := by
    have hnat : (902510747 : ℕ)^8231*100000000000000^6183 ≤ 10237795384491^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902510747 5000000000 10237795384491 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1308391681/2500000000 : ℝ), (2859603111/5000000000 : ℝ), (-902510747/5000000000 : ℝ)] ![(21116645556953/50000000000000 : ℝ), (47528913492351/100000000000000 : ℝ), (10237795384491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1308391681/2500000000 : ℝ)|^8231 ≤ (21116645556953/50000000000000 : ℝ)^6183
        have hw : |(1308391681/2500000000 : ℝ)|=(1308391681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2859603111/5000000000 : ℝ)|^8231 ≤ (47528913492351/100000000000000 : ℝ)^6183
        have hw : |(2859603111/5000000000 : ℝ)|=(2859603111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-902510747/5000000000 : ℝ)|^8231 ≤ (10237795384491/100000000000000 : ℝ)^6183
        have hw : |(-902510747/5000000000 : ℝ)|=(902510747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s1_7 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4328043603/10000000000 : ℝ)*x 0 + (5098664701/10000000000 : ℝ)*x 1 + (3678642109/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4328043603/10000000000 : ℝ)^8231 ≤ (16397974952317/50000000000000 : ℝ)^6183 := by
    have hnat : (4328043603 : ℕ)^8231*50000000000000^6183 ≤ 16397974952317^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4328043603 10000000000 16397974952317 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5098664701/10000000000 : ℝ)^8231 ≤ (40790311448539/100000000000000 : ℝ)^6183 := by
    have hnat : (5098664701 : ℕ)^8231*100000000000000^6183 ≤ 40790311448539^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5098664701 10000000000 40790311448539 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3678642109/10000000000 : ℝ)^8231 ≤ (26413738632951/100000000000000 : ℝ)^6183 := by
    have hnat : (3678642109 : ℕ)^8231*100000000000000^6183 ≤ 26413738632951^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3678642109 10000000000 26413738632951 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4328043603/10000000000 : ℝ), (5098664701/10000000000 : ℝ), (3678642109/10000000000 : ℝ)] ![(16397974952317/50000000000000 : ℝ), (40790311448539/100000000000000 : ℝ), (26413738632951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4328043603/10000000000 : ℝ)|^8231 ≤ (16397974952317/50000000000000 : ℝ)^6183
        have hw : |(4328043603/10000000000 : ℝ)|=(4328043603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5098664701/10000000000 : ℝ)|^8231 ≤ (40790311448539/100000000000000 : ℝ)^6183
        have hw : |(5098664701/10000000000 : ℝ)|=(5098664701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3678642109/10000000000 : ℝ)|^8231 ≤ (26413738632951/100000000000000 : ℝ)^6183
        have hw : |(3678642109/10000000000 : ℝ)|=(3678642109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s1_8 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (9885089/10000000000 : ℝ)*x 0 + (548996187/1000000000 : ℝ)*x 1 + (398774447/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9885089/10000000000 : ℝ)^8231 ≤ (9991383211/100000000000000 : ℝ)^6183 := by
    have hnat : (9885089 : ℕ)^8231*100000000000000^6183 ≤ 9991383211^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9885089 10000000000 9991383211 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (548996187/1000000000 : ℝ)^8231 ≤ (45009757164349/100000000000000 : ℝ)^6183 := by
    have hnat : (548996187 : ℕ)^8231*100000000000000^6183 ≤ 45009757164349^6183*1000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548996187 1000000000 45009757164349 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (398774447/625000000 : ℝ)^8231 ≤ (27490125720547/50000000000000 : ℝ)^6183 := by
    have hnat : (398774447 : ℕ)^8231*50000000000000^6183 ≤ 27490125720547^6183*625000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      398774447 625000000 27490125720547 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(9885089/10000000000 : ℝ), (548996187/1000000000 : ℝ), (398774447/625000000 : ℝ)] ![(9991383211/100000000000000 : ℝ), (45009757164349/100000000000000 : ℝ), (27490125720547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(9885089/10000000000 : ℝ)|^8231 ≤ (9991383211/100000000000000 : ℝ)^6183
        have hw : |(9885089/10000000000 : ℝ)|=(9885089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(548996187/1000000000 : ℝ)|^8231 ≤ (45009757164349/100000000000000 : ℝ)^6183
        have hw : |(548996187/1000000000 : ℝ)|=(548996187/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(398774447/625000000 : ℝ)|^8231 ≤ (27490125720547/50000000000000 : ℝ)^6183
        have hw : |(398774447/625000000 : ℝ)|=(398774447/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s1_9 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (479019373/5000000000 : ℝ)*x 0 + (-2238627259/5000000000 : ℝ)*x 1 + (3461254483/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (479019373/5000000000 : ℝ)^8231 ≤ (220270219483/5000000000000 : ℝ)^6183 := by
    have hnat : (479019373 : ℕ)^8231*5000000000000^6183 ≤ 220270219483^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      479019373 5000000000 220270219483 5000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238627259/5000000000 : ℝ)^8231 ≤ (2144352391769/6250000000000 : ℝ)^6183 := by
    have hnat : (2238627259 : ℕ)^8231*6250000000000^6183 ≤ 2144352391769^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238627259 5000000000 2144352391769 6250000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3461254483/5000000000 : ℝ)^8231 ≤ (12256991466881/20000000000000 : ℝ)^6183 := by
    have hnat : (3461254483 : ℕ)^8231*20000000000000^6183 ≤ 12256991466881^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3461254483 5000000000 12256991466881 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(479019373/5000000000 : ℝ), (-2238627259/5000000000 : ℝ), (3461254483/5000000000 : ℝ)] ![(220270219483/5000000000000 : ℝ), (2144352391769/6250000000000 : ℝ), (12256991466881/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(479019373/5000000000 : ℝ)|^8231 ≤ (220270219483/5000000000000 : ℝ)^6183
        have hw : |(479019373/5000000000 : ℝ)|=(479019373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2238627259/5000000000 : ℝ)|^8231 ≤ (2144352391769/6250000000000 : ℝ)^6183
        have hw : |(-2238627259/5000000000 : ℝ)|=(2238627259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3461254483/5000000000 : ℝ)|^8231 ≤ (12256991466881/20000000000000 : ℝ)^6183
        have hw : |(3461254483/5000000000 : ℝ)|=(3461254483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s1_10 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (958033619/10000000000 : ℝ)*x 0 + (6922498073/10000000000 : ℝ)*x 1 + (-2238635089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (958033619/10000000000 : ℝ)^8231 ≤ (4405373004887/100000000000000 : ℝ)^6183 := by
    have hnat : (958033619 : ℕ)^8231*100000000000000^6183 ≤ 4405373004887^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958033619 10000000000 4405373004887 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6922498073/10000000000 : ℝ)^8231 ≤ (61284828956257/100000000000000 : ℝ)^6183 := by
    have hnat : (6922498073 : ℕ)^8231*100000000000000^6183 ≤ 61284828956257^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6922498073 10000000000 61284828956257 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2238635089/5000000000 : ℝ)^8231 ≤ (857744950539/2500000000000 : ℝ)^6183 := by
    have hnat : (2238635089 : ℕ)^8231*2500000000000^6183 ≤ 857744950539^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238635089 5000000000 857744950539 2500000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(958033619/10000000000 : ℝ), (6922498073/10000000000 : ℝ), (-2238635089/5000000000 : ℝ)] ![(4405373004887/100000000000000 : ℝ), (61284828956257/100000000000000 : ℝ), (857744950539/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(958033619/10000000000 : ℝ)|^8231 ≤ (4405373004887/100000000000000 : ℝ)^6183
        have hw : |(958033619/10000000000 : ℝ)|=(958033619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6922498073/10000000000 : ℝ)|^8231 ≤ (61284828956257/100000000000000 : ℝ)^6183
        have hw : |(6922498073/10000000000 : ℝ)|=(6922498073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2238635089/5000000000 : ℝ)|^8231 ≤ (857744950539/2500000000000 : ℝ)^6183
        have hw : |(-2238635089/5000000000 : ℝ)|=(2238635089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s1_11 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (48216241/250000000 : ℝ)*x 0 + (2918538953/5000000000 : ℝ)*x 1 + (5022479821/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48216241/250000000 : ℝ)^8231 ≤ (2795421142983/25000000000000 : ℝ)^6183 := by
    have hnat : (48216241 : ℕ)^8231*25000000000000^6183 ≤ 2795421142983^6183*250000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48216241 250000000 2795421142983 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2918538953/5000000000 : ℝ)^8231 ≤ (12209341600047/25000000000000 : ℝ)^6183 := by
    have hnat : (2918538953 : ℕ)^8231*25000000000000^6183 ≤ 12209341600047^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2918538953 5000000000 12209341600047 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5022479821/10000000000 : ℝ)^8231 ≤ (39980949014129/100000000000000 : ℝ)^6183 := by
    have hnat : (5022479821 : ℕ)^8231*100000000000000^6183 ≤ 39980949014129^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5022479821 10000000000 39980949014129 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(48216241/250000000 : ℝ), (2918538953/5000000000 : ℝ), (5022479821/10000000000 : ℝ)] ![(2795421142983/25000000000000 : ℝ), (12209341600047/25000000000000 : ℝ), (39980949014129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(48216241/250000000 : ℝ)|^8231 ≤ (2795421142983/25000000000000 : ℝ)^6183
        have hw : |(48216241/250000000 : ℝ)|=(48216241/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2918538953/5000000000 : ℝ)|^8231 ≤ (12209341600047/25000000000000 : ℝ)^6183
        have hw : |(2918538953/5000000000 : ℝ)|=(2918538953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5022479821/10000000000 : ℝ)|^8231 ≤ (39980949014129/100000000000000 : ℝ)^6183
        have hw : |(5022479821/10000000000 : ℝ)|=(5022479821/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1038_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28219/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5051/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (10461/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28219/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28219/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28219/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28219/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28219/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28219/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (4115/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4115 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4115*1^1024 ≤ 0^1024*1^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (28219/100000 : ℝ) ^ (4115/1024 : ℝ) ≤ (309700177295416139/50000000000000000000 : ℝ) := by
    have hpowers : (28219/100000 : ℝ)^4115 ≤ (309700177295416139/50000000000000000000 : ℝ)^1024 := by
      have hnat : (28219 : ℕ)^4115*50000000000000000000^1024 ≤ 309700177295416139^1024*100000^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28219 100000 309700177295416139 50000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28219/100000 : ℝ)) (X := (309700177295416139/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4115 := by
      have hnat : (1 : ℕ)^1024*1^4115 ≤ 1^4115*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50309700177295416139/50000000000000000000 : ℝ) ≤ (10015377782884741/10000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (50309700177295416139/50000000000000000000 : ℝ)^1024 ≤ (10015377782884741/10000000000000000 : ℝ)^4115 := by
      have hnat : (50309700177295416139 : ℕ)^1024*10000000000000000^4115 ≤ 10015377782884741^4115*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50309700177295416139 50000000000000000000 10015377782884741 10000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015377782884741/10000000000000000 : ℝ)) (X := (50309700177295416139/50000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25309700177295416139/25000000000000000000 : ℝ) ≤ (5015377782884741/5000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (25309700177295416139/25000000000000000000 : ℝ)^1024 ≤ (5015377782884741/5000000000000000 : ℝ)^4115 := by
      have hnat : (25309700177295416139 : ℕ)^1024*5000000000000000^4115 ≤ 5015377782884741^4115*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25309700177295416139 25000000000000000000 5015377782884741 5000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015377782884741/5000000000000000 : ℝ)) (X := (25309700177295416139/25000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15377782884741/2821900000000000 : ℝ)*(0 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15377782884741/2821900000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(309700177295416139/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15377782884741/2821900000000000 : ℝ)*((28219/100000 : ℝ)+(0 : ℝ)))^(4115/1024 : ℝ) := by
    rw [show (1 : ℝ)+(15377782884741/2821900000000000 : ℝ)*((28219/100000 : ℝ)+(0 : ℝ))=(10015377782884741/10000000000000000 : ℝ) by norm_num, show 1+(309700177295416139/50000000000000000000 : ℝ)+(0 : ℝ)=(50309700177295416139/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(309700177295416139/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15377782884741/2821900000000000 : ℝ)*(28219/100000 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(15377782884741/2821900000000000 : ℝ)*(28219/100000 : ℝ)=(5015377782884741/5000000000000000 : ℝ) by norm_num, show 1+2*(309700177295416139/50000000000000000000 : ℝ)=(25309700177295416139/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15377782884741/2821900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (28219/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (15377782884741/2821900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15377782884741/2821900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (28219/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (15377782884741/2821900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15377782884741/2821900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (28219/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (15377782884741/2821900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1068629973/5000000000 : ℝ)*X 0 0+(716258917/1250000000 : ℝ)*X 0 1+(2489976637/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((678107643/1250000000 : ℝ)*X 1 0+(-159017051/625000000 : ℝ)*X 1 1+(622494199/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((10849723/20000000 : ℝ)*X 2 0+(4979953139/10000000000 : ℝ)*X 2 1+(-1272136463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4326164633/10000000000 : ℝ)*X 0 0+(1828731303/5000000000 : ℝ)*X 0 1+(319963817/625000000 : ℝ)*X 0 2+(4326164633/10000000000 : ℝ)*X 1 0+(1828731303/5000000000 : ℝ)*X 1 1+(319963817/625000000 : ℝ)*X 1 2+(4326164633/10000000000 : ℝ)*X 2 0+(1828731303/5000000000 : ℝ)*X 2 1+(319963817/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-267278193/1250000000 : ℝ)*X 0 0+(1247650371/2500000000 : ℝ)*X 0 1+(5719203091/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1046713717/2000000000 : ℝ)*X 1 0+(-902510919/5000000000 : ℝ)*X 1 1+(285960209/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1308391681/2500000000 : ℝ)*X 2 0+(2859603111/5000000000 : ℝ)*X 2 1+(-902510747/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4328043603/10000000000 : ℝ)*X 0 0+(5098664701/10000000000 : ℝ)*X 0 1+(3678642109/10000000000 : ℝ)*X 0 2+(4328043603/10000000000 : ℝ)*X 1 0+(5098664701/10000000000 : ℝ)*X 1 1+(3678642109/10000000000 : ℝ)*X 1 2+(4328043603/10000000000 : ℝ)*X 2 0+(5098664701/10000000000 : ℝ)*X 2 1+(3678642109/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((9885089/10000000000 : ℝ)*X 0 0+(548996187/1000000000 : ℝ)*X 0 1+(398774447/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((479019373/5000000000 : ℝ)*X 1 0+(-2238627259/5000000000 : ℝ)*X 1 1+(3461254483/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((958033619/10000000000 : ℝ)*X 2 0+(6922498073/10000000000 : ℝ)*X 2 1+(-2238635089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((48216241/250000000 : ℝ)*X 0 0+(2918538953/5000000000 : ℝ)*X 0 1+(5022479821/10000000000 : ℝ)*X 0 2+(48216241/250000000 : ℝ)*X 1 0+(2918538953/5000000000 : ℝ)*X 1 1+(5022479821/10000000000 : ℝ)*X 1 2+(48216241/250000000 : ℝ)*X 2 0+(2918538953/5000000000 : ℝ)*X 2 1+(5022479821/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (160063210384105021353861/14109500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1008572470677907/100000000000000 : ℝ)*(major0) + (1008572470677907/100000000000000 : ℝ)*(major1) + (1008572470677907/100000000000000 : ℝ)*(major2) + (666563004877451/50000000000000 : ℝ)*(sp0) + (666563393708669/50000000000000 : ℝ)*(sp1) + (166640774472529/12500000000000 : ℝ)*(sp2) + (136802939462321/20000000000000 : ℝ)*(sp3) + (1366730041/100000000000000 : ℝ)*(sp4) + (476662053/50000000000000 : ℝ)*(sp5) + (146043127/10000000000000 : ℝ)*(sp6) + (543482829/50000000000000 : ℝ)*(sp8) + (722709157/100000000000000 : ℝ)*(sp9) + (8072391/1000000000000 : ℝ)*(sp10) + (1402448353/100000000000000 : ℝ)*(sp11) + (684016099759959/100000000000000 : ℝ)*(f.failure) + (666564231725301/50000000000000 : ℝ)*(f.sum) + (148384987220121/70547500000000000000000000000 : ℝ)*base65 + (1984116078002527/282190000000000000000000000000 : ℝ)*base67 + (1944404200580167/282190000000000000000000000000 : ℝ)*base69 + (1517213289988177/282190000000000000000000000000 : ℝ)*base71 + (168861764639917/141095000000000000000000000000 : ℝ)*base73 + (1432037759654997/282190000000000000000000000000 : ℝ)*base75 + (173337432926737/282190000000000000000000000000 : ℝ)*base77 + (186781218062753/282190000000000000000000000000 : ℝ)*base80 + (82902923565849/17636875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (15961111/2000000000000000000000 : ℝ)*base89 + (15961111/2000000000000000000000 : ℝ)*base91 + (15961111/2000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4876010074208473137/1000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12788463/12500000000000 : ℝ)*(base59) + (207670870354753/20000000000000 : ℝ)*(major0) + (207670870354753/20000000000000 : ℝ)*(major1) + (207670870354753/20000000000000 : ℝ)*(major2) + (1807167149/100000000000000 : ℝ)*(sp0) + (1840636539/100000000000000 : ℝ)*(sp1) + (4301939839/100000000000000 : ℝ)*(sp2) + (1372489821436659/100000000000000 : ℝ)*(sp4) + (34312305360559/2500000000000 : ℝ)*(sp5) + (1372490001110853/100000000000000 : ℝ)*(sp6) + (176053224102663/25000000000000 : ℝ)*(sp7) + (668611721/25000000000000 : ℝ)*(sp8) + (247991793/100000000000000 : ℝ)*(sp9) + (268310503/20000000000000 : ℝ)*(sp11) + (704214237963167/100000000000000 : ℝ)*(f.failure) + (343123575762673/25000000000000 : ℝ)*(f.sum) + (3587201083383/5643800000000000000000000000 : ℝ)*base65 + (95823704654977/56438000000000000000000000000 : ℝ)*base67 + (2139719456633/2257520000000000000000000000 : ℝ)*base69 + (222110275924927/56438000000000000000000000000 : ℝ)*base72 + (78269659331743/28219000000000000000000000000 : ℝ)*base74 + (144640369791631/56438000000000000000000000000 : ℝ)*base75 + (50202457572691/56438000000000000000000000000 : ℝ)*base78 + (59529787744471/56438000000000000000000000000 : ℝ)*base79 + (978897759479/1410950000000000000000000000 : ℝ)*base82 + (6811743/2000000000000000000000 : ℝ)*base89 + (6811743/2000000000000000000000 : ℝ)*base91 + (6811743/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1038_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28219/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (10461/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1038_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1038_s2_0 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2196333507/10000000000 : ℝ)*x 0 + (5531692879/10000000000 : ℝ)*x 1 + (2570435639/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2196333507/10000000000 : ℝ)^8231 ≤ (13293780022743/100000000000000 : ℝ)^6183 := by
    have hnat : (2196333507 : ℕ)^8231*100000000000000^6183 ≤ 13293780022743^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196333507 10000000000 13293780022743 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5531692879/10000000000 : ℝ)^8231 ≤ (9093157776151/20000000000000 : ℝ)^6183 := by
    have hnat : (5531692879 : ℕ)^8231*20000000000000^6183 ≤ 9093157776151^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5531692879 10000000000 9093157776151 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2570435639/5000000000 : ℝ)^8231 ≤ (20620215539767/50000000000000 : ℝ)^6183 := by
    have hnat : (2570435639 : ℕ)^8231*50000000000000^6183 ≤ 20620215539767^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570435639 5000000000 20620215539767 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2196333507/10000000000 : ℝ), (5531692879/10000000000 : ℝ), (2570435639/5000000000 : ℝ)] ![(13293780022743/100000000000000 : ℝ), (9093157776151/20000000000000 : ℝ), (20620215539767/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2196333507/10000000000 : ℝ)|^8231 ≤ (13293780022743/100000000000000 : ℝ)^6183
        have hw : |(-2196333507/10000000000 : ℝ)|=(2196333507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5531692879/10000000000 : ℝ)|^8231 ≤ (9093157776151/20000000000000 : ℝ)^6183
        have hw : |(5531692879/10000000000 : ℝ)|=(5531692879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2570435639/5000000000 : ℝ)|^8231 ≤ (20620215539767/50000000000000 : ℝ)^6183
        have hw : |(2570435639/5000000000 : ℝ)|=(2570435639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s2_1 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1075689/2000000 : ℝ)*x 0 + (-2400393889/10000000000 : ℝ)*x 1 + (2570436023/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075689/2000000 : ℝ)^8231 ≤ (10949189089313/25000000000000 : ℝ)^6183 := by
    have hnat : (1075689 : ℕ)^8231*25000000000000^6183 ≤ 10949189089313^6183*2000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075689 2000000 10949189089313 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2400393889/10000000000 : ℝ)^8231 ≤ (7481402169571/50000000000000 : ℝ)^6183 := by
    have hnat : (2400393889 : ℕ)^8231*50000000000000^6183 ≤ 7481402169571^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2400393889 10000000000 7481402169571 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2570436023/5000000000 : ℝ)^8231 ≤ (41240439281181/100000000000000 : ℝ)^6183 := by
    have hnat : (2570436023 : ℕ)^8231*100000000000000^6183 ≤ 41240439281181^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2570436023 5000000000 41240439281181 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075689/2000000 : ℝ), (-2400393889/10000000000 : ℝ), (2570436023/5000000000 : ℝ)] ![(10949189089313/25000000000000 : ℝ), (7481402169571/50000000000000 : ℝ), (41240439281181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075689/2000000 : ℝ)|^8231 ≤ (10949189089313/25000000000000 : ℝ)^6183
        have hw : |(1075689/2000000 : ℝ)|=(1075689/2000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2400393889/10000000000 : ℝ)|^8231 ≤ (7481402169571/50000000000000 : ℝ)^6183
        have hw : |(-2400393889/10000000000 : ℝ)|=(2400393889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2570436023/5000000000 : ℝ)|^8231 ≤ (41240439281181/100000000000000 : ℝ)^6183
        have hw : |(2570436023/5000000000 : ℝ)|=(2570436023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s2_2 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2689222593/5000000000 : ℝ)*x 0 + (5140871949/10000000000 : ℝ)*x 1 + (-2400393771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689222593/5000000000 : ℝ)^8231 ≤ (8759351674707/20000000000000 : ℝ)^6183 := by
    have hnat : (2689222593 : ℕ)^8231*20000000000000^6183 ≤ 8759351674707^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689222593 5000000000 8759351674707 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140871949/10000000000 : ℝ)^8231 ≤ (2577527390331/6250000000000 : ℝ)^6183 := by
    have hnat : (5140871949 : ℕ)^8231*6250000000000^6183 ≤ 2577527390331^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140871949 10000000000 2577527390331 6250000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2400393771/10000000000 : ℝ)^8231 ≤ (7481401679977/50000000000000 : ℝ)^6183 := by
    have hnat : (2400393771 : ℕ)^8231*50000000000000^6183 ≤ 7481401679977^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2400393771 10000000000 7481401679977 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689222593/5000000000 : ℝ), (5140871949/10000000000 : ℝ), (-2400393771/10000000000 : ℝ)] ![(8759351674707/20000000000000 : ℝ), (2577527390331/6250000000000 : ℝ), (7481401679977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689222593/5000000000 : ℝ)|^8231 ≤ (8759351674707/20000000000000 : ℝ)^6183
        have hw : |(2689222593/5000000000 : ℝ)|=(2689222593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140871949/10000000000 : ℝ)|^8231 ≤ (2577527390331/6250000000000 : ℝ)^6183
        have hw : |(5140871949/10000000000 : ℝ)|=(5140871949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2400393771/10000000000 : ℝ)|^8231 ≤ (7481401679977/50000000000000 : ℝ)^6183
        have hw : |(-2400393771/10000000000 : ℝ)|=(2400393771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s2_3 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4366308861/10000000000 : ℝ)*x 0 + (4002319193/10000000000 : ℝ)*x 1 + (4764017407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4366308861/10000000000 : ℝ)^8231 ≤ (8295628338847/25000000000000 : ℝ)^6183 := by
    have hnat : (4366308861 : ℕ)^8231*25000000000000^6183 ≤ 8295628338847^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4366308861 10000000000 8295628338847 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4002319193/10000000000 : ℝ)^8231 ≤ (14775940091037/50000000000000 : ℝ)^6183 := by
    have hnat : (4002319193 : ℕ)^8231*50000000000000^6183 ≤ 14775940091037^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002319193 10000000000 14775940091037 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4764017407/10000000000 : ℝ)^8231 ≤ (18632803225863/50000000000000 : ℝ)^6183 := by
    have hnat : (4764017407 : ℕ)^8231*50000000000000^6183 ≤ 18632803225863^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4764017407 10000000000 18632803225863 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4366308861/10000000000 : ℝ), (4002319193/10000000000 : ℝ), (4764017407/10000000000 : ℝ)] ![(8295628338847/25000000000000 : ℝ), (14775940091037/50000000000000 : ℝ), (18632803225863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4366308861/10000000000 : ℝ)|^8231 ≤ (8295628338847/25000000000000 : ℝ)^6183
        have hw : |(4366308861/10000000000 : ℝ)|=(4366308861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4002319193/10000000000 : ℝ)|^8231 ≤ (14775940091037/50000000000000 : ℝ)^6183
        have hw : |(4002319193/10000000000 : ℝ)|=(4002319193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4764017407/10000000000 : ℝ)|^8231 ≤ (18632803225863/50000000000000 : ℝ)^6183
        have hw : |(4764017407/10000000000 : ℝ)|=(4764017407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s2_4 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2196468909/10000000000 : ℝ)*x 0 + (1028754059/2000000000 : ℝ)*x 1 + (5528763139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2196468909/10000000000 : ℝ)^8231 ≤ (13294871043641/100000000000000 : ℝ)^6183 := by
    have hnat : (2196468909 : ℕ)^8231*100000000000000^6183 ≤ 13294871043641^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2196468909 10000000000 13294871043641 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028754059/2000000000 : ℝ)^8231 ≤ (41271393231431/100000000000000 : ℝ)^6183 := by
    have hnat : (1028754059 : ℕ)^8231*100000000000000^6183 ≤ 41271393231431^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028754059 2000000000 41271393231431 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5528763139/10000000000 : ℝ)^8231 ≤ (45433735709299/100000000000000 : ℝ)^6183 := by
    have hnat : (5528763139 : ℕ)^8231*100000000000000^6183 ≤ 45433735709299^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5528763139 10000000000 45433735709299 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2196468909/10000000000 : ℝ), (1028754059/2000000000 : ℝ), (5528763139/10000000000 : ℝ)] ![(13294871043641/100000000000000 : ℝ), (41271393231431/100000000000000 : ℝ), (45433735709299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2196468909/10000000000 : ℝ)|^8231 ≤ (13294871043641/100000000000000 : ℝ)^6183
        have hw : |(-2196468909/10000000000 : ℝ)|=(2196468909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028754059/2000000000 : ℝ)|^8231 ≤ (41271393231431/100000000000000 : ℝ)^6183
        have hw : |(1028754059/2000000000 : ℝ)|=(1028754059/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5528763139/10000000000 : ℝ)|^8231 ≤ (45433735709299/100000000000000 : ℝ)^6183
        have hw : |(5528763139/10000000000 : ℝ)|=(5528763139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s2_5 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1319998771/2500000000 : ℝ)*x 0 + (-1006250887/5000000000 : ℝ)*x 1 + (138219089/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319998771/2500000000 : ℝ)^8231 ≤ (667699766199/1562500000000 : ℝ)^6183 := by
    have hnat : (1319998771 : ℕ)^8231*1562500000000^6183 ≤ 667699766199^6183*2500000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319998771 2500000000 667699766199 1562500000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1006250887/5000000000 : ℝ)^8231 ≤ (2366694927413/20000000000000 : ℝ)^6183 := by
    have hnat : (1006250887 : ℕ)^8231*20000000000000^6183 ≤ 2366694927413^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006250887 5000000000 2366694927413 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (138219089/250000000 : ℝ)^8231 ≤ (2839608769681/6250000000000 : ℝ)^6183 := by
    have hnat : (138219089 : ℕ)^8231*6250000000000^6183 ≤ 2839608769681^6183*250000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      138219089 250000000 2839608769681 6250000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319998771/2500000000 : ℝ), (-1006250887/5000000000 : ℝ), (138219089/250000000 : ℝ)] ![(667699766199/1562500000000 : ℝ), (2366694927413/20000000000000 : ℝ), (2839608769681/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319998771/2500000000 : ℝ)|^8231 ≤ (667699766199/1562500000000 : ℝ)^6183
        have hw : |(1319998771/2500000000 : ℝ)|=(1319998771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1006250887/5000000000 : ℝ)|^8231 ≤ (2366694927413/20000000000000 : ℝ)^6183
        have hw : |(-1006250887/5000000000 : ℝ)|=(1006250887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(138219089/250000000 : ℝ)|^8231 ≤ (2839608769681/6250000000000 : ℝ)^6183
        have hw : |(138219089/250000000 : ℝ)|=(138219089/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s2_6 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (82499913/156250000 : ℝ)*x 0 + (34554771/62500000 : ℝ)*x 1 + (-251562869/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82499913/156250000 : ℝ)^8231 ≤ (21366389006011/50000000000000 : ℝ)^6183 := by
    have hnat : (82499913 : ℕ)^8231*50000000000000^6183 ≤ 21366389006011^6183*156250000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82499913 156250000 21366389006011 50000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34554771/62500000 : ℝ)^8231 ≤ (11358434531741/25000000000000 : ℝ)^6183 := by
    have hnat : (34554771 : ℕ)^8231*25000000000000^6183 ≤ 11358434531741^6183*62500000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34554771 62500000 11358434531741 25000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (251562869/1250000000 : ℝ)^8231 ≤ (2366696771599/20000000000000 : ℝ)^6183 := by
    have hnat : (251562869 : ℕ)^8231*20000000000000^6183 ≤ 2366696771599^6183*1250000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      251562869 1250000000 2366696771599 20000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82499913/156250000 : ℝ), (34554771/62500000 : ℝ), (-251562869/1250000000 : ℝ)] ![(21366389006011/50000000000000 : ℝ), (11358434531741/25000000000000 : ℝ), (2366696771599/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82499913/156250000 : ℝ)|^8231 ≤ (21366389006011/50000000000000 : ℝ)^6183
        have hw : |(82499913/156250000 : ℝ)|=(82499913/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(34554771/62500000 : ℝ)|^8231 ≤ (11358434531741/25000000000000 : ℝ)^6183
        have hw : |(34554771/62500000 : ℝ)|=(34554771/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-251562869/1250000000 : ℝ)|^8231 ≤ (2366696771599/20000000000000 : ℝ)^6183
        have hw : |(-251562869/1250000000 : ℝ)|=(251562869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1038_s2_7 (p : ℝ) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (873314681/2000000000 : ℝ)*x 0 + (4758369141/10000000000 : ℝ)*x 1 + (2004014089/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (873314681/2000000000 : ℝ)^8231 ≤ (33185189751889/100000000000000 : ℝ)^6183 := by
    have hnat : (873314681 : ℕ)^8231*100000000000000^6183 ≤ 33185189751889^6183*2000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      873314681 2000000000 33185189751889 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4758369141/10000000000 : ℝ)^8231 ≤ (37206800938713/100000000000000 : ℝ)^6183 := by
    have hnat : (4758369141 : ℕ)^8231*100000000000000^6183 ≤ 37206800938713^6183*10000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4758369141 10000000000 37206800938713 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2004014089/5000000000 : ℝ)^8231 ≤ (29608009298351/100000000000000 : ℝ)^6183 := by
    have hnat : (2004014089 : ℕ)^8231*100000000000000^6183 ≤ 29608009298351^6183*5000000000^8231 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2004014089 5000000000 29608009298351 100000000000000 8231 6183 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8231/2048 : ℝ)) 8231 6183 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(873314681/2000000000 : ℝ), (4758369141/10000000000 : ℝ), (2004014089/5000000000 : ℝ)] ![(33185189751889/100000000000000 : ℝ), (37206800938713/100000000000000 : ℝ), (29608009298351/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(873314681/2000000000 : ℝ)|^8231 ≤ (33185189751889/100000000000000 : ℝ)^6183
        have hw : |(873314681/2000000000 : ℝ)|=(873314681/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4758369141/10000000000 : ℝ)|^8231 ≤ (37206800938713/100000000000000 : ℝ)^6183
        have hw : |(4758369141/10000000000 : ℝ)|=(4758369141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2004014089/5000000000 : ℝ)|^8231 ≤ (29608009298351/100000000000000 : ℝ)^6183
        have hw : |(2004014089/5000000000 : ℝ)|=(2004014089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1038_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10461/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4287/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16833/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (10461/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (10461/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (10461/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (10461/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (10461/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (10461/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5051/100000 : ℝ) ^ (4115/1024 : ℝ) ≤ (615816110397847/100000000000000000000 : ℝ) := by
    have hpowers : (5051/100000 : ℝ)^4115 ≤ (615816110397847/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5051 : ℕ)^4115*100000000000000000000^1024 ≤ 615816110397847^1024*100000^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5051 100000 615816110397847 100000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5051/100000 : ℝ)) (X := (615816110397847/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (10461/50000 : ℝ) ^ (4115/1024 : ℝ) ≤ (93062946767643133/50000000000000000000 : ℝ) := by
    have hpowers : (10461/50000 : ℝ)^4115 ≤ (93062946767643133/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10461 : ℕ)^4115*50000000000000000000^1024 ≤ 93062946767643133^1024*50000^4115 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10461 50000 93062946767643133 50000000000000000000 4115 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10461/50000 : ℝ)) (X := (93062946767643133/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000615816110397847/50000000000000000000 : ℝ) ≤ (10000030648494781/10000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (50000615816110397847/50000000000000000000 : ℝ)^1024 ≤ (10000030648494781/10000000000000000 : ℝ)^4115 := by
      have hnat : (50000615816110397847 : ℕ)^1024*10000000000000000^4115 ≤ 10000030648494781^4115*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000615816110397847 50000000000000000000 10000030648494781 10000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000030648494781/10000000000000000 : ℝ)) (X := (50000615816110397847/50000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100186741709645684113/100000000000000000000 : ℝ) ≤ (2000928746246967/2000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (100186741709645684113/100000000000000000000 : ℝ)^1024 ≤ (2000928746246967/2000000000000000 : ℝ)^4115 := by
      have hnat : (100186741709645684113 : ℕ)^1024*2000000000000000^4115 ≤ 2000928746246967^4115*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100186741709645684113 100000000000000000000 2000928746246967 2000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000928746246967/2000000000000000 : ℝ)) (X := (100186741709645684113/100000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25093062946767643133/25000000000000000000 : ℝ) ≤ (10009256813974889/10000000000000000 : ℝ) ^ (4115/1024 : ℝ) := by
    have hpowers : (25093062946767643133/25000000000000000000 : ℝ)^1024 ≤ (10009256813974889/10000000000000000 : ℝ)^4115 := by
      have hnat : (25093062946767643133 : ℕ)^1024*10000000000000000^4115 ≤ 10009256813974889^4115*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25093062946767643133 25000000000000000000 10009256813974889 10000000000000000 1024 4115 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009256813974889/10000000000000000 : ℝ)) (X := (25093062946767643133/25000000000000000000 : ℝ)) (by norm_num) 4115 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(615816110397847/100000000000000000000 : ℝ) ≤ ((158663885060420643743/158710000000000000000 : ℝ)+2*(2306541370027/793550000000000 : ℝ)*(5051/100000 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (158663885060420643743/158710000000000000000 : ℝ)+2*(2306541370027/793550000000000 : ℝ)*(5051/100000 : ℝ)=(10000030648494781/10000000000000000 : ℝ) by norm_num, show 1+2*(615816110397847/100000000000000000000 : ℝ)=(50000615816110397847/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(93062946767643133/50000000000000000000 : ℝ)+(615816110397847/100000000000000000000 : ℝ) ≤ ((158663885060420643743/158710000000000000000 : ℝ)+(2306541370027/793550000000000 : ℝ)*((10461/50000 : ℝ)+(5051/100000 : ℝ)))^(4115/1024 : ℝ) := by
    rw [show (158663885060420643743/158710000000000000000 : ℝ)+(2306541370027/793550000000000 : ℝ)*((10461/50000 : ℝ)+(5051/100000 : ℝ))=(2000928746246967/2000000000000000 : ℝ) by norm_num, show 1+(93062946767643133/50000000000000000000 : ℝ)+(615816110397847/100000000000000000000 : ℝ)=(100186741709645684113/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(93062946767643133/50000000000000000000 : ℝ) ≤ ((158663885060420643743/158710000000000000000 : ℝ)+2*(2306541370027/793550000000000 : ℝ)*(10461/50000 : ℝ))^(4115/1024 : ℝ) := by
    rw [show (158663885060420643743/158710000000000000000 : ℝ)+2*(2306541370027/793550000000000 : ℝ)*(10461/50000 : ℝ)=(10009256813974889/10000000000000000 : ℝ) by norm_num, show 1+2*(93062946767643133/50000000000000000000 : ℝ)=(25093062946767643133/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (158663885060420643743/158710000000000000000 : ℝ)*(X 1 0+X 2 0)+(2306541370027/793550000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (5051/100000 : ℝ)) (hi := (10461/50000 : ℝ)) (c := (158663885060420643743/158710000000000000000 : ℝ)) (alpha := (2306541370027/793550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (158663885060420643743/158710000000000000000 : ℝ)*(X 0 1+X 2 1)+(2306541370027/793550000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (5051/100000 : ℝ)) (hi := (10461/50000 : ℝ)) (c := (158663885060420643743/158710000000000000000 : ℝ)) (alpha := (2306541370027/793550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (158663885060420643743/158710000000000000000 : ℝ)*(X 0 2+X 1 2)+(2306541370027/793550000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4115/1024 : ℝ)) (lo := (5051/100000 : ℝ)) (hi := (10461/50000 : ℝ)) (c := (158663885060420643743/158710000000000000000 : ℝ)) (alpha := (2306541370027/793550000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2196333507/10000000000 : ℝ)*X 0 0+(5531692879/10000000000 : ℝ)*X 0 1+(2570435639/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1075689/2000000 : ℝ)*X 1 0+(-2400393889/10000000000 : ℝ)*X 1 1+(2570436023/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2689222593/5000000000 : ℝ)*X 2 0+(5140871949/10000000000 : ℝ)*X 2 1+(-2400393771/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4366308861/10000000000 : ℝ)*X 0 0+(4002319193/10000000000 : ℝ)*X 0 1+(4764017407/10000000000 : ℝ)*X 0 2+(4366308861/10000000000 : ℝ)*X 1 0+(4002319193/10000000000 : ℝ)*X 1 1+(4764017407/10000000000 : ℝ)*X 1 2+(4366308861/10000000000 : ℝ)*X 2 0+(4002319193/10000000000 : ℝ)*X 2 1+(4764017407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2196468909/10000000000 : ℝ)*X 0 0+(1028754059/2000000000 : ℝ)*X 0 1+(5528763139/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1319998771/2500000000 : ℝ)*X 1 0+(-1006250887/5000000000 : ℝ)*X 1 1+(138219089/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82499913/156250000 : ℝ)*X 2 0+(34554771/62500000 : ℝ)*X 2 1+(-251562869/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((873314681/2000000000 : ℝ)*X 0 0+(4758369141/10000000000 : ℝ)*X 0 1+(2004014089/5000000000 : ℝ)*X 0 2+(873314681/2000000000 : ℝ)*X 1 0+(4758369141/10000000000 : ℝ)*X 1 1+(2004014089/5000000000 : ℝ)*X 1 2+(873314681/2000000000 : ℝ)*X 2 0+(4758369141/10000000000 : ℝ)*X 2 1+(2004014089/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1038_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13041995420123422399866935853/1983875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (425083731/25000000000000 : ℝ)*(base19) + (1682421351/100000000000000 : ℝ)*(base23) + (105294453/50000000000000 : ℝ)*(upper3) + (57227487/100000000000000 : ℝ)*(upper4) + (27009979/12500000000000 : ℝ)*(upper5) + (483953189911581/25000000000000 : ℝ)*(major0) + (483953189911581/25000000000000 : ℝ)*(major1) + (483953189911581/25000000000000 : ℝ)*(major2) + (639682957626623/25000000000000 : ℝ)*(sp0) + (2558751067393617/100000000000000 : ℝ)*(sp1) + (255875108530719/10000000000000 : ℝ)*(sp2) + (262572804521533/20000000000000 : ℝ)*(sp3) + (20937222049/100000000000000 : ℝ)*(sp4) + (8509823083/100000000000000 : ℝ)*(sp7) + (328218133107687/25000000000000 : ℝ)*(f.failure) + (2558752767728541/100000000000000 : ℝ)*(f.sum) + (254303791812271/79355000000000000000000000000 : ℝ)*base65 + (11976598221123037683/3967750000000000000000000000000000 : ℝ)*base67 + (21592658393824287683/3967750000000000000000000000000000 : ℝ)*base69 + (13017373926613287683/3967750000000000000000000000000000 : ℝ)*base71 + (351897400611571/79355000000000000000000000000 : ℝ)*base73 + (16714143936713037683/3967750000000000000000000000000000 : ℝ)*base75 + (16980670762078287683/3967750000000000000000000000000000 : ℝ)*base77 + (24299999668603787683/3967750000000000000000000000000000 : ℝ)*base79 + (42234002382151/79355000000000000000000000000 : ℝ)*base81 + (2553177/500000000000000000000 : ℝ)*base90 + (2553177/500000000000000000000 : ℝ)*base92 + (2553177/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17877094431170724089368822767/1983875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (396301047/20000000000000 : ℝ)*(base19) + (161154411/10000000000000 : ℝ)*(base23) + (26487851/12500000000000 : ℝ)*(upper3) + (364819/800000000000 : ℝ)*(lower4) + (1300019/781250000000 : ℝ)*(upper5) + (491271882763159/25000000000000 : ℝ)*(major0) + (491271882763159/25000000000000 : ℝ)*(major1) + (491271882763159/25000000000000 : ℝ)*(major2) + (5049270003/25000000000000 : ℝ)*(sp1) + (2585087807/20000000000000 : ℝ)*(sp2) + (649362003505199/25000000000000 : ℝ)*(sp4) + (51948516708711/2000000000000 : ℝ)*(sp5) + (2597433477037651/100000000000000 : ℝ)*(sp6) + (666363373855567/50000000000000 : ℝ)*(sp7) + (666363373855567/50000000000000 : ℝ)*(f.failure) + (649362003505199/25000000000000 : ℝ)*(f.sum) + (90718210006357/39677500000000000000000000000 : ℝ)*base65 + (29111123578969364137/3967750000000000000000000000000000 : ℝ)*base67 + (52618051383438864137/3967750000000000000000000000000000 : ℝ)*base69 + (17208680000350364137/3967750000000000000000000000000000 : ℝ)*base71 + (24542336838307/39677500000000000000000000000 : ℝ)*base73 + (20953565712471864137/3967750000000000000000000000000000 : ℝ)*base75 + (18294182830329864137/3967750000000000000000000000000000 : ℝ)*base77 + (45960801830568114137/3967750000000000000000000000000000 : ℝ)*base79 + (156354097221519/79355000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4028657/1000000000000000000000 : ℝ)*base90 + (4028657/1000000000000000000000 : ℝ)*base92 + (4028657/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1038_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (10461/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4287/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16833/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1038_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1038_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4287/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16833/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1038_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1038_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1038_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4115/1024 : ℝ) ≤ p) (hpb : p ≤ (8231/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (29489729/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4287/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16833/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1038_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
