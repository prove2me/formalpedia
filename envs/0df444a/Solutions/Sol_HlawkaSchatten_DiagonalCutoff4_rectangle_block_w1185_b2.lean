-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1185_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:51:19.13798+00:00
-- url     : https://prove2.me/submissions/5aa22fef-6698-4a30-8f36-87cd036aaa55

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
theorem support_rectangle_w1185_s6_0 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2146467941/10000000000 : ℝ)*x 0 + (5392518211/10000000000 : ℝ)*x 1 + (526615611/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146467941/10000000000 : ℝ)^4189 ≤ (13047021753947/100000000000000 : ℝ)^3165 := by
    have hnat : (2146467941 : ℕ)^4189*100000000000000^3165 ≤ 13047021753947^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146467941 10000000000 13047021753947 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392518211/10000000000 : ℝ)^4189 ≤ (44158654157607/100000000000000 : ℝ)^3165 := by
    have hnat : (5392518211 : ℕ)^4189*100000000000000^3165 ≤ 44158654157607^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392518211 10000000000 44158654157607 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526615611/1000000000 : ℝ)^4189 ≤ (42794324066763/100000000000000 : ℝ)^3165 := by
    have hnat : (526615611 : ℕ)^4189*100000000000000^3165 ≤ 42794324066763^3165*1000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526615611 1000000000 42794324066763 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2146467941/10000000000 : ℝ), (5392518211/10000000000 : ℝ), (526615611/1000000000 : ℝ)] ![(13047021753947/100000000000000 : ℝ), (44158654157607/100000000000000 : ℝ), (42794324066763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2146467941/10000000000 : ℝ)|^4189 ≤ (13047021753947/100000000000000 : ℝ)^3165
        have hw : |(-2146467941/10000000000 : ℝ)|=(2146467941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392518211/10000000000 : ℝ)|^4189 ≤ (44158654157607/100000000000000 : ℝ)^3165
        have hw : |(5392518211/10000000000 : ℝ)|=(5392518211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526615611/1000000000 : ℝ)|^4189 ≤ (42794324066763/100000000000000 : ℝ)^3165
        have hw : |(526615611/1000000000 : ℝ)|=(526615611/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s6_1 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668081463/1250000000 : ℝ)*x 0 + (-44211083/200000000 : ℝ)*x 1 + (1053231231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668081463/1250000000 : ℝ)^4189 ≤ (43640609419189/100000000000000 : ℝ)^3165 := by
    have hnat : (668081463 : ℕ)^4189*100000000000000^3165 ≤ 43640609419189^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668081463 1250000000 43640609419189 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (44211083/200000000 : ℝ)^4189 ≤ (3391266504209/25000000000000 : ℝ)^3165 := by
    have hnat : (44211083 : ℕ)^4189*25000000000000^3165 ≤ 3391266504209^3165*200000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44211083 200000000 3391266504209 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053231231/2000000000 : ℝ)^4189 ≤ (42794324550759/100000000000000 : ℝ)^3165 := by
    have hnat : (1053231231 : ℕ)^4189*100000000000000^3165 ≤ 42794324550759^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053231231 2000000000 42794324550759 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668081463/1250000000 : ℝ), (-44211083/200000000 : ℝ), (1053231231/2000000000 : ℝ)] ![(43640609419189/100000000000000 : ℝ), (3391266504209/25000000000000 : ℝ), (42794324550759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668081463/1250000000 : ℝ)|^4189 ≤ (43640609419189/100000000000000 : ℝ)^3165
        have hw : |(668081463/1250000000 : ℝ)|=(668081463/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-44211083/200000000 : ℝ)|^4189 ≤ (3391266504209/25000000000000 : ℝ)^3165
        have hw : |(-44211083/200000000 : ℝ)|=(44211083/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053231231/2000000000 : ℝ)|^4189 ≤ (42794324550759/100000000000000 : ℝ)^3165
        have hw : |(1053231231/2000000000 : ℝ)|=(1053231231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s6_2 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344651793/10000000000 : ℝ)*x 0 + (1053231201/2000000000 : ℝ)*x 1 + (-2210554229/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344651793/10000000000 : ℝ)^4189 ≤ (21820305190509/50000000000000 : ℝ)^3165 := by
    have hnat : (5344651793 : ℕ)^4189*50000000000000^3165 ≤ 21820305190509^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344651793 10000000000 21820305190509 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053231201/2000000000 : ℝ)^4189 ≤ (267464518359/625000000000 : ℝ)^3165 := by
    have hnat : (1053231201 : ℕ)^4189*625000000000^3165 ≤ 267464518359^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053231201 2000000000 267464518359 625000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210554229/10000000000 : ℝ)^4189 ≤ (6782533329233/50000000000000 : ℝ)^3165 := by
    have hnat : (2210554229 : ℕ)^4189*50000000000000^3165 ≤ 6782533329233^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210554229 10000000000 6782533329233 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344651793/10000000000 : ℝ), (1053231201/2000000000 : ℝ), (-2210554229/10000000000 : ℝ)] ![(21820305190509/50000000000000 : ℝ), (267464518359/625000000000 : ℝ), (6782533329233/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344651793/10000000000 : ℝ)|^4189 ≤ (21820305190509/50000000000000 : ℝ)^3165
        have hw : |(5344651793/10000000000 : ℝ)|=(5344651793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053231201/2000000000 : ℝ)|^4189 ≤ (267464518359/625000000000 : ℝ)^3165
        have hw : |(1053231201/2000000000 : ℝ)|=(1053231201/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2210554229/10000000000 : ℝ)|^4189 ≤ (6782533329233/50000000000000 : ℝ)^3165
        have hw : |(-2210554229/10000000000 : ℝ)|=(2210554229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s6_3 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4358637379/10000000000 : ℝ)*x 0 + (4233694647/10000000000 : ℝ)*x 1 + (4487211277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358637379/10000000000 : ℝ)^4189 ≤ (16658532812149/50000000000000 : ℝ)^3165 := by
    have hnat : (4358637379 : ℕ)^4189*50000000000000^3165 ≤ 16658532812149^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358637379 10000000000 16658532812149 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4233694647/10000000000 : ℝ)^4189 ≤ (32058917385379/100000000000000 : ℝ)^3165 := by
    have hnat : (4233694647 : ℕ)^4189*100000000000000^3165 ≤ 32058917385379^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233694647 10000000000 32058917385379 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487211277/10000000000 : ℝ)^4189 ≤ (17312008489507/50000000000000 : ℝ)^3165 := by
    have hnat : (4487211277 : ℕ)^4189*50000000000000^3165 ≤ 17312008489507^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487211277 10000000000 17312008489507 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358637379/10000000000 : ℝ), (4233694647/10000000000 : ℝ), (4487211277/10000000000 : ℝ)] ![(16658532812149/50000000000000 : ℝ), (32058917385379/100000000000000 : ℝ), (17312008489507/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358637379/10000000000 : ℝ)|^4189 ≤ (16658532812149/50000000000000 : ℝ)^3165
        have hw : |(4358637379/10000000000 : ℝ)|=(4358637379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4233694647/10000000000 : ℝ)|^4189 ≤ (32058917385379/100000000000000 : ℝ)^3165
        have hw : |(4233694647/10000000000 : ℝ)|=(4233694647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487211277/10000000000 : ℝ)|^4189 ≤ (17312008489507/50000000000000 : ℝ)^3165
        have hw : |(4487211277/10000000000 : ℝ)|=(4487211277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s6_4 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-214647289/1000000000 : ℝ)*x 0 + (2633237603/5000000000 : ℝ)*x 1 + (43137583/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214647289/1000000000 : ℝ)^4189 ≤ (2609412313689/20000000000000 : ℝ)^3165 := by
    have hnat : (214647289 : ℕ)^4189*20000000000000^3165 ≤ 2609412313689^3165*1000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214647289 1000000000 2609412313689 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633237603/5000000000 : ℝ)^4189 ≤ (21398878062723/50000000000000 : ℝ)^3165 := by
    have hnat : (2633237603 : ℕ)^4189*50000000000000^3165 ≤ 21398878062723^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633237603 5000000000 21398878062723 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (43137583/80000000 : ℝ)^4189 ≤ (4415518229581/10000000000000 : ℝ)^3165 := by
    have hnat : (43137583 : ℕ)^4189*10000000000000^3165 ≤ 4415518229581^3165*80000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43137583 80000000 4415518229581 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214647289/1000000000 : ℝ), (2633237603/5000000000 : ℝ), (43137583/80000000 : ℝ)] ![(2609412313689/20000000000000 : ℝ), (21398878062723/50000000000000 : ℝ), (4415518229581/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214647289/1000000000 : ℝ)|^4189 ≤ (2609412313689/20000000000000 : ℝ)^3165
        have hw : |(-214647289/1000000000 : ℝ)|=(214647289/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633237603/5000000000 : ℝ)|^4189 ≤ (21398878062723/50000000000000 : ℝ)^3165
        have hw : |(2633237603/5000000000 : ℝ)|=(2633237603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(43137583/80000000 : ℝ)|^4189 ≤ (4415518229581/10000000000000 : ℝ)^3165
        have hw : |(43137583/80000000 : ℝ)|=(43137583/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s6_5 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656268607/5000000000 : ℝ)*x 0 + (-208451237/1000000000 : ℝ)*x 1 + (5392197823/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656268607/5000000000 : ℝ)^4189 ≤ (1082347090683/2500000000000 : ℝ)^3165 := by
    have hnat : (2656268607 : ℕ)^4189*2500000000000^3165 ≤ 1082347090683^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656268607 5000000000 1082347090683 2500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (208451237/1000000000 : ℝ)^4189 ≤ (12550934619141/100000000000000 : ℝ)^3165 := by
    have hnat : (208451237 : ℕ)^4189*100000000000000^3165 ≤ 12550934619141^3165*1000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208451237 1000000000 12550934619141 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392197823/10000000000 : ℝ)^4189 ≤ (44155181732229/100000000000000 : ℝ)^3165 := by
    have hnat : (5392197823 : ℕ)^4189*100000000000000^3165 ≤ 44155181732229^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392197823 10000000000 44155181732229 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656268607/5000000000 : ℝ), (-208451237/1000000000 : ℝ), (5392197823/10000000000 : ℝ)] ![(1082347090683/2500000000000 : ℝ), (12550934619141/100000000000000 : ℝ), (44155181732229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656268607/5000000000 : ℝ)|^4189 ≤ (1082347090683/2500000000000 : ℝ)^3165
        have hw : |(2656268607/5000000000 : ℝ)|=(2656268607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-208451237/1000000000 : ℝ)|^4189 ≤ (12550934619141/100000000000000 : ℝ)^3165
        have hw : |(-208451237/1000000000 : ℝ)|=(208451237/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392197823/10000000000 : ℝ)|^4189 ≤ (44155181732229/100000000000000 : ℝ)^3165
        have hw : |(5392197823/10000000000 : ℝ)|=(5392197823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s6_6 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312537231/10000000000 : ℝ)*x 0 + (168506179/312500000 : ℝ)*x 1 + (-2084512477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312537231/10000000000 : ℝ)^4189 ≤ (21646941905341/50000000000000 : ℝ)^3165 := by
    have hnat : (5312537231 : ℕ)^4189*50000000000000^3165 ≤ 21646941905341^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312537231 10000000000 21646941905341 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (168506179/312500000 : ℝ)^4189 ≤ (44155180702611/100000000000000 : ℝ)^3165 := by
    have hnat : (168506179 : ℕ)^4189*100000000000000^3165 ≤ 44155180702611^3165*312500000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168506179 312500000 44155180702611 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084512477/10000000000 : ℝ)^4189 ≤ (12550935471833/100000000000000 : ℝ)^3165 := by
    have hnat : (2084512477 : ℕ)^4189*100000000000000^3165 ≤ 12550935471833^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084512477 10000000000 12550935471833 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312537231/10000000000 : ℝ), (168506179/312500000 : ℝ), (-2084512477/10000000000 : ℝ)] ![(21646941905341/50000000000000 : ℝ), (44155180702611/100000000000000 : ℝ), (12550935471833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312537231/10000000000 : ℝ)|^4189 ≤ (21646941905341/50000000000000 : ℝ)^3165
        have hw : |(5312537231/10000000000 : ℝ)|=(5312537231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(168506179/312500000 : ℝ)|^4189 ≤ (44155180702611/100000000000000 : ℝ)^3165
        have hw : |(168506179/312500000 : ℝ)|=(168506179/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084512477/10000000000 : ℝ)|^4189 ≤ (12550935471833/100000000000000 : ℝ)^3165
        have hw : |(-2084512477/10000000000 : ℝ)|=(2084512477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s6_7 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (435864683/1000000000 : ℝ)*x 0 + (140205337/312500000 : ℝ)*x 1 + (2117168867/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (435864683/1000000000 : ℝ)^4189 ≤ (33317161240297/100000000000000 : ℝ)^3165 := by
    have hnat : (435864683 : ℕ)^4189*100000000000000^3165 ≤ 33317161240297^3165*1000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      435864683 1000000000 33317161240297 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (140205337/312500000 : ℝ)^4189 ≤ (6923495202461/20000000000000 : ℝ)^3165 := by
    have hnat : (140205337 : ℕ)^4189*20000000000000^3165 ≤ 6923495202461^3165*312500000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140205337 312500000 6923495202461 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2117168867/5000000000 : ℝ)^4189 ≤ (32065362733341/100000000000000 : ℝ)^3165 := by
    have hnat : (2117168867 : ℕ)^4189*100000000000000^3165 ≤ 32065362733341^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117168867 5000000000 32065362733341 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(435864683/1000000000 : ℝ), (140205337/312500000 : ℝ), (2117168867/5000000000 : ℝ)] ![(33317161240297/100000000000000 : ℝ), (6923495202461/20000000000000 : ℝ), (32065362733341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(435864683/1000000000 : ℝ)|^4189 ≤ (33317161240297/100000000000000 : ℝ)^3165
        have hw : |(435864683/1000000000 : ℝ)|=(435864683/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(140205337/312500000 : ℝ)|^4189 ≤ (6923495202461/20000000000000 : ℝ)^3165
        have hw : |(140205337/312500000 : ℝ)|=(140205337/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2117168867/5000000000 : ℝ)|^4189 ≤ (32065362733341/100000000000000 : ℝ)^3165
        have hw : |(2117168867/5000000000 : ℝ)|=(2117168867/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1185_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11403/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14079/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7053/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7053/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11377/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7053/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7053/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11377/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7053/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7053/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11377/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11377/100000 : ℝ) ^ (8377/2048 : ℝ) ≤ (430219532463403/3125000000000000000 : ℝ) := by
    have hpowers : (11377/100000 : ℝ)^8377 ≤ (430219532463403/3125000000000000000 : ℝ)^2048 := by
      have hnat : (11377 : ℕ)^8377*3125000000000000000^2048 ≤ 430219532463403^2048*100000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11377 100000 430219532463403 3125000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11377/100000 : ℝ)) (X := (430219532463403/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7053/50000 : ℝ) ^ (8377/2048 : ℝ) ≤ (8293148677381593/25000000000000000000 : ℝ) := by
    have hpowers : (7053/50000 : ℝ)^8377 ≤ (8293148677381593/25000000000000000000 : ℝ)^2048 := by
      have hnat : (7053 : ℕ)^8377*25000000000000000000^2048 ≤ 8293148677381593^2048*50000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7053 50000 8293148677381593 25000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7053/50000 : ℝ)) (X := (8293148677381593/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562930219532463403/1562500000000000000 : ℝ) ≤ (12500841349383/12500000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (1562930219532463403/1562500000000000000 : ℝ)^2048 ≤ (12500841349383/12500000000000 : ℝ)^8377 := by
      have hnat : (1562930219532463403 : ℕ)^2048*12500000000000^8377 ≤ 12500841349383^8377*1562500000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562930219532463403 1562500000000000000 12500841349383 12500000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (12500841349383/12500000000000 : ℝ)) (X := (1562930219532463403/1562500000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011734904937088817/25000000000000000000 : ℝ) ≤ (312535855355363/312500000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (25011734904937088817/25000000000000000000 : ℝ)^2048 ≤ (312535855355363/312500000000000 : ℝ)^8377 := by
      have hnat : (25011734904937088817 : ℕ)^2048*312500000000000^8377 ≤ 312535855355363^8377*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011734904937088817 25000000000000000000 312535855355363 312500000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312535855355363/312500000000000 : ℝ)) (X := (25011734904937088817/25000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508293148677381593/12500000000000000000 : ℝ) ≤ (312550676976151/312500000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (12508293148677381593/12500000000000000000 : ℝ)^2048 ≤ (312550676976151/312500000000000 : ℝ)^8377 := by
      have hnat : (12508293148677381593 : ℕ)^2048*312500000000000^8377 ≤ 312550676976151^8377*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508293148677381593 12500000000000000000 312550676976151 312500000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312550676976151/312500000000000 : ℝ)) (X := (12508293148677381593/12500000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(430219532463403/3125000000000000000 : ℝ) ≤ ((852532649902245023/852812500000000000 : ℝ)+2*(3705405197/2132031250000 : ℝ)*(11377/100000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (852532649902245023/852812500000000000 : ℝ)+2*(3705405197/2132031250000 : ℝ)*(11377/100000 : ℝ)=(12500841349383/12500000000000 : ℝ) by norm_num, show 1+2*(430219532463403/3125000000000000000 : ℝ)=(1562930219532463403/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8293148677381593/25000000000000000000 : ℝ)+(430219532463403/3125000000000000000 : ℝ) ≤ ((852532649902245023/852812500000000000 : ℝ)+(3705405197/2132031250000 : ℝ)*((7053/50000 : ℝ)+(11377/100000 : ℝ)))^(8377/2048 : ℝ) := by
    rw [show (852532649902245023/852812500000000000 : ℝ)+(3705405197/2132031250000 : ℝ)*((7053/50000 : ℝ)+(11377/100000 : ℝ))=(312535855355363/312500000000000 : ℝ) by norm_num, show 1+(8293148677381593/25000000000000000000 : ℝ)+(430219532463403/3125000000000000000 : ℝ)=(25011734904937088817/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8293148677381593/25000000000000000000 : ℝ) ≤ ((852532649902245023/852812500000000000 : ℝ)+2*(3705405197/2132031250000 : ℝ)*(7053/50000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (852532649902245023/852812500000000000 : ℝ)+2*(3705405197/2132031250000 : ℝ)*(7053/50000 : ℝ)=(312550676976151/312500000000000 : ℝ) by norm_num, show 1+2*(8293148677381593/25000000000000000000 : ℝ)=(12508293148677381593/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (852532649902245023/852812500000000000 : ℝ)*(X 1 0+X 2 0)+(3705405197/2132031250000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (852532649902245023/852812500000000000 : ℝ)) (alpha := (3705405197/2132031250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (852532649902245023/852812500000000000 : ℝ)*(X 0 1+X 2 1)+(3705405197/2132031250000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (852532649902245023/852812500000000000 : ℝ)) (alpha := (3705405197/2132031250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (852532649902245023/852812500000000000 : ℝ)*(X 0 2+X 1 2)+(3705405197/2132031250000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (11377/100000 : ℝ)) (hi := (7053/50000 : ℝ)) (c := (852532649902245023/852812500000000000 : ℝ)) (alpha := (3705405197/2132031250000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2146467941/10000000000 : ℝ)*X 0 0+(5392518211/10000000000 : ℝ)*X 0 1+(526615611/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668081463/1250000000 : ℝ)*X 1 0+(-44211083/200000000 : ℝ)*X 1 1+(1053231231/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344651793/10000000000 : ℝ)*X 2 0+(1053231201/2000000000 : ℝ)*X 2 1+(-2210554229/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358637379/10000000000 : ℝ)*X 0 0+(4233694647/10000000000 : ℝ)*X 0 1+(4487211277/10000000000 : ℝ)*X 0 2+(4358637379/10000000000 : ℝ)*X 1 0+(4233694647/10000000000 : ℝ)*X 1 1+(4487211277/10000000000 : ℝ)*X 1 2+(4358637379/10000000000 : ℝ)*X 2 0+(4233694647/10000000000 : ℝ)*X 2 1+(4487211277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-214647289/1000000000 : ℝ)*X 0 0+(2633237603/5000000000 : ℝ)*X 0 1+(43137583/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656268607/5000000000 : ℝ)*X 1 0+(-208451237/1000000000 : ℝ)*X 1 1+(5392197823/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312537231/10000000000 : ℝ)*X 2 0+(168506179/312500000 : ℝ)*X 2 1+(-2084512477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((435864683/1000000000 : ℝ)*X 0 0+(140205337/312500000 : ℝ)*X 0 1+(2117168867/5000000000 : ℝ)*X 0 2+(435864683/1000000000 : ℝ)*X 1 0+(140205337/312500000 : ℝ)*X 1 1+(2117168867/5000000000 : ℝ)*X 1 2+(435864683/1000000000 : ℝ)*X 2 0+(140205337/312500000 : ℝ)*X 2 1+(2117168867/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13491386248141051846917/3411250000000000000000000000 : ℝ) := by norm_num
    linear_combination (300957197/50000000000000 : ℝ)*(base19) + (626362063/100000000000000 : ℝ)*(base23) + (49207389/50000000000000 : ℝ)*(lower2) + (183623821/100000000000000 : ℝ)*(upper3) + (10262113/25000000000000 : ℝ)*(lower4) + (1482291028883989/25000000000000 : ℝ)*(major0) + (1482291028883989/25000000000000 : ℝ)*(major1) + (1482291028883989/25000000000000 : ℝ)*(major2) + (7913782081587323/100000000000000 : ℝ)*(sp0) + (7913792343145369/100000000000000 : ℝ)*(sp1) + (7913792318697699/100000000000000 : ℝ)*(sp2) + (394452225393301/10000000000000 : ℝ)*(sp3) + (271586811/2500000000000 : ℝ)*(sp4) + (201566357/1562500000000 : ℝ)*(sp7) + (1972267577089929/50000000000000 : ℝ)*(f.failure) + (3956896472529881/50000000000000 : ℝ)*(f.sum) + (54787585285619/13645000000000000000000000000 : ℝ)*base66 + (264231371129814119/42640625000000000000000000000000 : ℝ)*base67 + (246211695625507003/21320312500000000000000000000000 : ℝ)*base70 + (64890920905099407/5330078125000000000000000000000 : ℝ)*base72 + (323285610807/1705625000000000000000000000 : ℝ)*base73 + (300051018314845369/42640625000000000000000000000000 : ℝ)*base75 + (536664505663907869/42640625000000000000000000000000 : ℝ)*base77 + (76039567085154631/42640625000000000000000000000000 : ℝ)*base80 + (105430839645999/13645000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (402499/250000000000000000000 : ℝ)*base90 + (402499/250000000000000000000 : ℝ)*base92 + (402499/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (278584102106742110439/136450000000000000000000000 : ℝ) := by norm_num
    linear_combination (42014459/10000000000000 : ℝ)*(base19) + (104591219/20000000000000 : ℝ)*(base23) + (63182169/100000000000000 : ℝ)*(upper2) + (21124331/25000000000000 : ℝ)*(upper5) + (297965091339123/5000000000000 : ℝ)*(major0) + (297965091339123/5000000000000 : ℝ)*(major1) + (297965091339123/5000000000000 : ℝ)*(major2) + (350148999/50000000000000 : ℝ)*(sp0) + (6389160889/50000000000000 : ℝ)*(sp1) + (5901349323/100000000000000 : ℝ)*(sp2) + (7954017811825359/100000000000000 : ℝ)*(sp4) + (1988501328414247/25000000000000 : ℝ)*(sp5) + (3977006043908969/50000000000000 : ℝ)*(sp6) + (1982292536693161/50000000000000 : ℝ)*(sp7) + (1982292536693161/50000000000000 : ℝ)*(f.failure) + (1988504628030839/25000000000000 : ℝ)*(f.sum) + (388152371659/170562500000000000000000000 : ℝ)*base65 + (37348001613821421/4264062500000000000000000000000 : ℝ)*base68 + (24146798252695967/8528125000000000000000000000000 : ℝ)*base70 + (75912082903579/4264062500000000000000000000000 : ℝ)*base71 + (648044340739/136450000000000000000000000 : ℝ)*base74 + (8912675430762727/2132031250000000000000000000000 : ℝ)*base75 + (95676794842370967/8528125000000000000000000000000 : ℝ)*base78 + (159290256658722783/8528125000000000000000000000000 : ℝ)*base79 + (6849369819923/2729000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (2639709/250000000000000000000 : ℝ)*base89 + (2639709/250000000000000000000 : ℝ)*base91 + (2639709/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1185_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1185_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1185_s7_0 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-268311223/1250000000 : ℝ)*x 0 + (2696128789/5000000000 : ℝ)*x 1 + (658300301/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268311223/1250000000 : ℝ)^4189 ≤ (13047197480191/100000000000000 : ℝ)^3165 := by
    have hnat : (268311223 : ℕ)^4189*100000000000000^3165 ≤ 13047197480191^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268311223 1250000000 13047197480191 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696128789/5000000000 : ℝ)^4189 ≤ (44155829363089/100000000000000 : ℝ)^3165 := by
    have hnat : (2696128789 : ℕ)^4189*100000000000000^3165 ≤ 44155829363089^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696128789 5000000000 44155829363089 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658300301/1250000000 : ℝ)^4189 ≤ (42796973135693/100000000000000 : ℝ)^3165 := by
    have hnat : (658300301 : ℕ)^4189*100000000000000^3165 ≤ 42796973135693^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658300301 1250000000 42796973135693 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-268311223/1250000000 : ℝ), (2696128789/5000000000 : ℝ), (658300301/1250000000 : ℝ)] ![(13047197480191/100000000000000 : ℝ), (44155829363089/100000000000000 : ℝ), (42796973135693/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-268311223/1250000000 : ℝ)|^4189 ≤ (13047197480191/100000000000000 : ℝ)^3165
        have hw : |(-268311223/1250000000 : ℝ)|=(268311223/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696128789/5000000000 : ℝ)|^4189 ≤ (44155829363089/100000000000000 : ℝ)^3165
        have hw : |(2696128789/5000000000 : ℝ)|=(2696128789/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658300301/1250000000 : ℝ)|^4189 ≤ (42796973135693/100000000000000 : ℝ)^3165
        have hw : |(658300301/1250000000 : ℝ)|=(658300301/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s7_1 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672293097/5000000000 : ℝ)*x 0 + (-2210315203/10000000000 : ℝ)*x 1 + (5266402413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672293097/5000000000 : ℝ)^4189 ≤ (10909975362327/25000000000000 : ℝ)^3165 := by
    have hnat : (2672293097 : ℕ)^4189*25000000000000^3165 ≤ 10909975362327^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672293097 5000000000 10909975362327 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210315203/10000000000 : ℝ)^4189 ≤ (13563125348197/100000000000000 : ℝ)^3165 := by
    have hnat : (2210315203 : ℕ)^4189*100000000000000^3165 ≤ 13563125348197^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210315203 10000000000 13563125348197 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266402413/10000000000 : ℝ)^4189 ≤ (42796973189471/100000000000000 : ℝ)^3165 := by
    have hnat : (5266402413 : ℕ)^4189*100000000000000^3165 ≤ 42796973189471^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266402413 10000000000 42796973189471 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672293097/5000000000 : ℝ), (-2210315203/10000000000 : ℝ), (5266402413/10000000000 : ℝ)] ![(10909975362327/25000000000000 : ℝ), (13563125348197/100000000000000 : ℝ), (42796973189471/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672293097/5000000000 : ℝ)|^4189 ≤ (10909975362327/25000000000000 : ℝ)^3165
        have hw : |(2672293097/5000000000 : ℝ)|=(2672293097/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2210315203/10000000000 : ℝ)|^4189 ≤ (13563125348197/100000000000000 : ℝ)^3165
        have hw : |(-2210315203/10000000000 : ℝ)|=(2210315203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266402413/10000000000 : ℝ)|^4189 ≤ (42796973189471/100000000000000 : ℝ)^3165
        have hw : |(5266402413/10000000000 : ℝ)|=(5266402413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s7_2 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068917239/2000000000 : ℝ)*x 0 + (2633201207/5000000000 : ℝ)*x 1 + (-2210315201/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068917239/2000000000 : ℝ)^4189 ≤ (8727980292023/20000000000000 : ℝ)^3165 := by
    have hnat : (1068917239 : ℕ)^4189*20000000000000^3165 ≤ 8727980292023^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068917239 2000000000 8727980292023 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633201207/5000000000 : ℝ)^4189 ≤ (42796973200227/100000000000000 : ℝ)^3165 := by
    have hnat : (2633201207 : ℕ)^4189*100000000000000^3165 ≤ 42796973200227^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633201207 5000000000 42796973200227 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2210315201/10000000000 : ℝ)^4189 ≤ (6781562665977/50000000000000 : ℝ)^3165 := by
    have hnat : (2210315201 : ℕ)^4189*50000000000000^3165 ≤ 6781562665977^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210315201 10000000000 6781562665977 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068917239/2000000000 : ℝ), (2633201207/5000000000 : ℝ), (-2210315201/10000000000 : ℝ)] ![(8727980292023/20000000000000 : ℝ), (42796973200227/100000000000000 : ℝ), (6781562665977/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068917239/2000000000 : ℝ)|^4189 ≤ (8727980292023/20000000000000 : ℝ)^3165
        have hw : |(1068917239/2000000000 : ℝ)|=(1068917239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633201207/5000000000 : ℝ)|^4189 ≤ (42796973200227/100000000000000 : ℝ)^3165
        have hw : |(2633201207/5000000000 : ℝ)|=(2633201207/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2210315201/10000000000 : ℝ)|^4189 ≤ (6781562665977/50000000000000 : ℝ)^3165
        have hw : |(-2210315201/10000000000 : ℝ)|=(2210315201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s7_3 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (544831261/1250000000 : ℝ)*x 0 + (846840363/2000000000 : ℝ)*x 1 + (4486700953/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (544831261/1250000000 : ℝ)^4189 ≤ (16658597100789/50000000000000 : ℝ)^3165 := by
    have hnat : (544831261 : ℕ)^4189*50000000000000^3165 ≤ 16658597100789^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544831261 1250000000 16658597100789 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (846840363/2000000000 : ℝ)^4189 ≤ (32064000456969/100000000000000 : ℝ)^3165 := by
    have hnat : (846840363 : ℕ)^4189*100000000000000^3165 ≤ 32064000456969^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846840363 2000000000 32064000456969 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4486700953/10000000000 : ℝ)^4189 ≤ (270459416601/781250000000 : ℝ)^3165 := by
    have hnat : (4486700953 : ℕ)^4189*781250000000^3165 ≤ 270459416601^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4486700953 10000000000 270459416601 781250000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(544831261/1250000000 : ℝ), (846840363/2000000000 : ℝ), (4486700953/10000000000 : ℝ)] ![(16658597100789/50000000000000 : ℝ), (32064000456969/100000000000000 : ℝ), (270459416601/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(544831261/1250000000 : ℝ)|^4189 ≤ (16658597100789/50000000000000 : ℝ)^3165
        have hw : |(544831261/1250000000 : ℝ)|=(544831261/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(846840363/2000000000 : ℝ)|^4189 ≤ (32064000456969/100000000000000 : ℝ)^3165
        have hw : |(846840363/2000000000 : ℝ)|=(846840363/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4486700953/10000000000 : ℝ)|^4189 ≤ (270459416601/781250000000 : ℝ)^3165
        have hw : |(4486700953/10000000000 : ℝ)|=(4486700953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s7_4 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-429298913/2000000000 : ℝ)*x 0 + (5266719149/10000000000 : ℝ)*x 1 + (2695969847/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429298913/2000000000 : ℝ)^4189 ≤ (6523617971631/50000000000000 : ℝ)^3165 := by
    have hnat : (429298913 : ℕ)^4189*50000000000000^3165 ≤ 6523617971631^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429298913 2000000000 6523617971631 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266719149/10000000000 : ℝ)^4189 ≤ (10700094979079/25000000000000 : ℝ)^3165 := by
    have hnat : (5266719149 : ℕ)^4189*25000000000000^3165 ≤ 10700094979079^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266719149 10000000000 10700094979079 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2695969847/5000000000 : ℝ)^4189 ≤ (22076192065077/50000000000000 : ℝ)^3165 := by
    have hnat : (2695969847 : ℕ)^4189*50000000000000^3165 ≤ 22076192065077^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695969847 5000000000 22076192065077 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429298913/2000000000 : ℝ), (5266719149/10000000000 : ℝ), (2695969847/5000000000 : ℝ)] ![(6523617971631/50000000000000 : ℝ), (10700094979079/25000000000000 : ℝ), (22076192065077/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429298913/2000000000 : ℝ)|^4189 ≤ (6523617971631/50000000000000 : ℝ)^3165
        have hw : |(-429298913/2000000000 : ℝ)|=(429298913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266719149/10000000000 : ℝ)|^4189 ≤ (10700094979079/25000000000000 : ℝ)^3165
        have hw : |(5266719149/10000000000 : ℝ)|=(5266719149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2695969847/5000000000 : ℝ)|^4189 ≤ (22076192065077/50000000000000 : ℝ)^3165
        have hw : |(2695969847/5000000000 : ℝ)|=(2695969847/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s7_5 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312600389/10000000000 : ℝ)*x 0 + (-1042388957/5000000000 : ℝ)*x 1 + (336996231/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312600389/10000000000 : ℝ)^4189 ≤ (2164728251771/5000000000000 : ℝ)^3165 := by
    have hnat : (5312600389 : ℕ)^4189*5000000000000^3165 ≤ 2164728251771^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312600389 10000000000 2164728251771 5000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1042388957/5000000000 : ℝ)^4189 ≤ (12553050804371/100000000000000 : ℝ)^3165 := by
    have hnat : (1042388957 : ℕ)^4189*100000000000000^3165 ≤ 12553050804371^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1042388957 5000000000 12553050804371 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336996231/625000000 : ℝ)^4189 ≤ (44152384151829/100000000000000 : ℝ)^3165 := by
    have hnat : (336996231 : ℕ)^4189*100000000000000^3165 ≤ 44152384151829^3165*625000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336996231 625000000 44152384151829 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312600389/10000000000 : ℝ), (-1042388957/5000000000 : ℝ), (336996231/625000000 : ℝ)] ![(2164728251771/5000000000000 : ℝ), (12553050804371/100000000000000 : ℝ), (44152384151829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312600389/10000000000 : ℝ)|^4189 ≤ (2164728251771/5000000000000 : ℝ)^3165
        have hw : |(5312600389/10000000000 : ℝ)|=(5312600389/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1042388957/5000000000 : ℝ)|^4189 ≤ (12553050804371/100000000000000 : ℝ)^3165
        have hw : |(-1042388957/5000000000 : ℝ)|=(1042388957/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(336996231/625000000 : ℝ)|^4189 ≤ (44152384151829/100000000000000 : ℝ)^3165
        have hw : |(336996231/625000000 : ℝ)|=(336996231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s7_6 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656300193/5000000000 : ℝ)*x 0 + (2695969849/5000000000 : ℝ)*x 1 + (-416955583/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656300193/5000000000 : ℝ)^4189 ≤ (21647282501531/50000000000000 : ℝ)^3165 := by
    have hnat : (2656300193 : ℕ)^4189*50000000000000^3165 ≤ 21647282501531^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656300193 5000000000 21647282501531 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695969849/5000000000 : ℝ)^4189 ≤ (8830476834701/20000000000000 : ℝ)^3165 := by
    have hnat : (2695969849 : ℕ)^4189*20000000000000^3165 ≤ 8830476834701^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695969849 5000000000 8830476834701 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (416955583/2000000000 : ℝ)^4189 ≤ (12553050812341/100000000000000 : ℝ)^3165 := by
    have hnat : (416955583 : ℕ)^4189*100000000000000^3165 ≤ 12553050812341^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      416955583 2000000000 12553050812341 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656300193/5000000000 : ℝ), (2695969849/5000000000 : ℝ), (-416955583/2000000000 : ℝ)] ![(21647282501531/50000000000000 : ℝ), (8830476834701/20000000000000 : ℝ), (12553050812341/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656300193/5000000000 : ℝ)|^4189 ≤ (21647282501531/50000000000000 : ℝ)^3165
        have hw : |(2656300193/5000000000 : ℝ)|=(2656300193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695969849/5000000000 : ℝ)|^4189 ≤ (8830476834701/20000000000000 : ℝ)^3165
        have hw : |(2695969849/5000000000 : ℝ)|=(2695969849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-416955583/2000000000 : ℝ)|^4189 ≤ (12553050812341/100000000000000 : ℝ)^3165
        have hw : |(-416955583/2000000000 : ℝ)|=(416955583/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s7_7 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2179329843/5000000000 : ℝ)*x 0 + (2243032749/5000000000 : ℝ)*x 1 + (1058709893/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179329843/5000000000 : ℝ)^4189 ≤ (4164661413109/12500000000000 : ℝ)^3165 := by
    have hnat : (2179329843 : ℕ)^4189*12500000000000^3165 ≤ 4164661413109^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179329843 5000000000 4164661413109 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2243032749/5000000000 : ℝ)^4189 ≤ (8653079011473/25000000000000 : ℝ)^3165 := by
    have hnat : (2243032749 : ℕ)^4189*25000000000000^3165 ≤ 8653079011473^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243032749 5000000000 8653079011473 25000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058709893/2500000000 : ℝ)^4189 ≤ (16035196315671/50000000000000 : ℝ)^3165 := by
    have hnat : (1058709893 : ℕ)^4189*50000000000000^3165 ≤ 16035196315671^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058709893 2500000000 16035196315671 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179329843/5000000000 : ℝ), (2243032749/5000000000 : ℝ), (1058709893/2500000000 : ℝ)] ![(4164661413109/12500000000000 : ℝ), (8653079011473/25000000000000 : ℝ), (16035196315671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179329843/5000000000 : ℝ)|^4189 ≤ (4164661413109/12500000000000 : ℝ)^3165
        have hw : |(2179329843/5000000000 : ℝ)|=(2179329843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2243032749/5000000000 : ℝ)|^4189 ≤ (8653079011473/25000000000000 : ℝ)^3165
        have hw : |(2243032749/5000000000 : ℝ)|=(2243032749/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058709893/2500000000 : ℝ)|^4189 ≤ (16035196315671/50000000000000 : ℝ)^3165
        have hw : |(1058709893/2500000000 : ℝ)|=(1058709893/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1185_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (713/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7037/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11403/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11403/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11403/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11403/100000 : ℝ) ^ (8377/2048 : ℝ) ≤ (13896170029133803/100000000000000000000 : ℝ) := by
    have hpowers : (11403/100000 : ℝ)^8377 ≤ (13896170029133803/100000000000000000000 : ℝ)^2048 := by
      have hnat : (11403 : ℕ)^8377*100000000000000000000^2048 ≤ 13896170029133803^2048*100000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11403 100000 13896170029133803 100000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11403/100000 : ℝ)) (X := (13896170029133803/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14079/100000 : ℝ) ^ (8377/2048 : ℝ) ≤ (1645682314990853/5000000000000000000 : ℝ) := by
    have hpowers : (14079/100000 : ℝ)^8377 ≤ (1645682314990853/5000000000000000000 : ℝ)^2048 := by
      have hnat : (14079 : ℕ)^8377*5000000000000000000^2048 ≤ 1645682314990853^2048*100000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14079 100000 1645682314990853 5000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14079/100000 : ℝ)) (X := (1645682314990853/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013896170029133803/50000000000000000000 : ℝ) ≤ (10000679392832771/10000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (50013896170029133803/50000000000000000000 : ℝ)^2048 ≤ (10000679392832771/10000000000000000 : ℝ)^8377 := by
      have hnat : (50013896170029133803 : ℕ)^2048*10000000000000000^8377 ≤ 10000679392832771^8377*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013896170029133803 50000000000000000000 10000679392832771 10000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000679392832771/10000000000000000 : ℝ)) (X := (50013896170029133803/50000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100046809816328950863/100000000000000000000 : ℝ) ≤ (10001144199074901/10000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (100046809816328950863/100000000000000000000 : ℝ)^2048 ≤ (10001144199074901/10000000000000000 : ℝ)^8377 := by
      have hnat : (100046809816328950863 : ℕ)^2048*10000000000000000^8377 ≤ 10001144199074901^8377*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100046809816328950863 100000000000000000000 10001144199074901 10000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001144199074901/10000000000000000 : ℝ)) (X := (100046809816328950863/100000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501645682314990853/2500000000000000000 : ℝ) ≤ (10001609005317031/10000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (2501645682314990853/2500000000000000000 : ℝ)^2048 ≤ (10001609005317031/10000000000000000 : ℝ)^8377 := by
      have hnat : (2501645682314990853 : ℕ)^2048*10000000000000000^8377 ≤ 10001609005317031^8377*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501645682314990853 2500000000000000000 10001609005317031 10000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001609005317031/10000000000000000 : ℝ)) (X := (2501645682314990853/2500000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13896170029133803/100000000000000000000 : ℝ) ≤ ((557317035084634967/557500000000000000 : ℝ)+2*(46480624213/26760000000000 : ℝ)*(11403/100000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (557317035084634967/557500000000000000 : ℝ)+2*(46480624213/26760000000000 : ℝ)*(11403/100000 : ℝ)=(10000679392832771/10000000000000000 : ℝ) by norm_num, show 1+2*(13896170029133803/100000000000000000000 : ℝ)=(50013896170029133803/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1645682314990853/5000000000000000000 : ℝ)+(13896170029133803/100000000000000000000 : ℝ) ≤ ((557317035084634967/557500000000000000 : ℝ)+(46480624213/26760000000000 : ℝ)*((14079/100000 : ℝ)+(11403/100000 : ℝ)))^(8377/2048 : ℝ) := by
    rw [show (557317035084634967/557500000000000000 : ℝ)+(46480624213/26760000000000 : ℝ)*((14079/100000 : ℝ)+(11403/100000 : ℝ))=(10001144199074901/10000000000000000 : ℝ) by norm_num, show 1+(1645682314990853/5000000000000000000 : ℝ)+(13896170029133803/100000000000000000000 : ℝ)=(100046809816328950863/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1645682314990853/5000000000000000000 : ℝ) ≤ ((557317035084634967/557500000000000000 : ℝ)+2*(46480624213/26760000000000 : ℝ)*(14079/100000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (557317035084634967/557500000000000000 : ℝ)+2*(46480624213/26760000000000 : ℝ)*(14079/100000 : ℝ)=(10001609005317031/10000000000000000 : ℝ) by norm_num, show 1+2*(1645682314990853/5000000000000000000 : ℝ)=(2501645682314990853/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (557317035084634967/557500000000000000 : ℝ)*(X 1 0+X 2 0)+(46480624213/26760000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (557317035084634967/557500000000000000 : ℝ)) (alpha := (46480624213/26760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (557317035084634967/557500000000000000 : ℝ)*(X 0 1+X 2 1)+(46480624213/26760000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (557317035084634967/557500000000000000 : ℝ)) (alpha := (46480624213/26760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (557317035084634967/557500000000000000 : ℝ)*(X 0 2+X 1 2)+(46480624213/26760000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (11403/100000 : ℝ)) (hi := (14079/100000 : ℝ)) (c := (557317035084634967/557500000000000000 : ℝ)) (alpha := (46480624213/26760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-268311223/1250000000 : ℝ)*X 0 0+(2696128789/5000000000 : ℝ)*X 0 1+(658300301/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672293097/5000000000 : ℝ)*X 1 0+(-2210315203/10000000000 : ℝ)*X 1 1+(5266402413/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068917239/2000000000 : ℝ)*X 2 0+(2633201207/5000000000 : ℝ)*X 2 1+(-2210315201/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((544831261/1250000000 : ℝ)*X 0 0+(846840363/2000000000 : ℝ)*X 0 1+(4486700953/10000000000 : ℝ)*X 0 2+(544831261/1250000000 : ℝ)*X 1 0+(846840363/2000000000 : ℝ)*X 1 1+(4486700953/10000000000 : ℝ)*X 1 2+(544831261/1250000000 : ℝ)*X 2 0+(846840363/2000000000 : ℝ)*X 2 1+(4486700953/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-429298913/2000000000 : ℝ)*X 0 0+(5266719149/10000000000 : ℝ)*X 0 1+(2695969847/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312600389/10000000000 : ℝ)*X 1 0+(-1042388957/5000000000 : ℝ)*X 1 1+(336996231/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656300193/5000000000 : ℝ)*X 2 0+(2695969849/5000000000 : ℝ)*X 2 1+(-416955583/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179329843/5000000000 : ℝ)*X 0 0+(2243032749/5000000000 : ℝ)*X 0 1+(1058709893/2500000000 : ℝ)*X 0 2+(2179329843/5000000000 : ℝ)*X 1 0+(2243032749/5000000000 : ℝ)*X 1 1+(1058709893/2500000000 : ℝ)*X 1 2+(2179329843/5000000000 : ℝ)*X 2 0+(2243032749/5000000000 : ℝ)*X 2 1+(1058709893/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1341038801564076285177/223000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146930247/12500000000000 : ℝ)*(base19) + (68859163/6250000000000 : ℝ)*(base23) + (40181697/100000000000000 : ℝ)*(lower2) + (37729571/25000000000000 : ℝ)*(upper3) + (19893323/20000000000000 : ℝ)*(upper5) + (2976537563135837/50000000000000 : ℝ)*(major0) + (2976537563135837/50000000000000 : ℝ)*(major1) + (2976537563135837/50000000000000 : ℝ)*(major2) + (496604677574087/6250000000000 : ℝ)*(sp0) + (7945706282467111/100000000000000 : ℝ)*(sp1) + (7945706356162479/100000000000000 : ℝ)*(sp2) + (990106326421851/25000000000000 : ℝ)*(sp3) + (6523344739/20000000000000 : ℝ)*(sp4) + (17288492617/100000000000000 : ℝ)*(sp7) + (1980221297090011/50000000000000 : ℝ)*(f.failure) + (7945707457909087/100000000000000 : ℝ)*(f.sum) + (2178978567361/334500000000000000000000000 : ℝ)*base65 + (932592812581474637/83625000000000000000000000000000 : ℝ)*base67 + (803466902755849637/83625000000000000000000000000000 : ℝ)*base69 + (274240763703400363/83625000000000000000000000000000 : ℝ)*base72 + (482254510991/167250000000000000000000000 : ℝ)*base73 + (1509555906120775363/83625000000000000000000000000000 : ℝ)*base76 + (1169903456084224637/83625000000000000000000000000000 : ℝ)*base77 + (285688648552900363/83625000000000000000000000000000 : ℝ)*base80 + (551041983437/167250000000000000000000000 : ℝ)*base81 + (882359/250000000000000000000 : ℝ)*base89 + (882359/250000000000000000000 : ℝ)*base91 + (882359/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (23350276875090719612503111/3484375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (610314247/50000000000000 : ℝ)*(base19) + (8251079/625000000000 : ℝ)*(base23) + (68199651/50000000000000 : ℝ)*(upper3) + (23744817/50000000000000 : ℝ)*(lower4) + (27479799/20000000000000 : ℝ)*(upper5) + (747899335708487/12500000000000 : ℝ)*(major0) + (747899335708487/12500000000000 : ℝ)*(major1) + (747899335708487/12500000000000 : ℝ)*(major2) + (8516809461/25000000000000 : ℝ)*(sp1) + (912566939/2500000000000 : ℝ)*(sp2) + (998238588821601/12500000000000 : ℝ)*(sp4) + (798587342270647/10000000000000 : ℝ)*(sp5) + (499116930482663/6250000000000 : ℝ)*(sp6) + (497560054672769/12500000000000 : ℝ)*(sp7) + (497560054672769/12500000000000 : ℝ)*(f.failure) + (998238588821601/12500000000000 : ℝ)*(f.sum) + (83086941209/167250000000000000000000000 : ℝ)*base65 + (253987880074967713/20906250000000000000000000000000 : ℝ)*base68 + (44995784129717713/20906250000000000000000000000000 : ℝ)*base70 + (151864502192155213/20906250000000000000000000000000 : ℝ)*base72 + (429970836643/167250000000000000000000000 : ℝ)*base74 + (636711857562842713/20906250000000000000000000000000 : ℝ)*base76 + (45712355548967713/20906250000000000000000000000000 : ℝ)*base78 + (121915192750217713/20906250000000000000000000000000 : ℝ)*base80 + (649664494277/167250000000000000000000000 : ℝ)*base81 + (117461/62500000000000000000 : ℝ)*base89 + (117461/62500000000000000000 : ℝ)*base91 + (117461/62500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1185_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11403/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1185_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1185_s8_0 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2146493507/10000000000 : ℝ)*x 0 + (1348052321/2500000000 : ℝ)*x 1 + (164576509/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146493507/10000000000 : ℝ)^4189 ≤ (6523613715833/50000000000000 : ℝ)^3165 := by
    have hnat : (2146493507 : ℕ)^4189*50000000000000^3165 ≤ 6523613715833^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146493507 10000000000 6523613715833 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348052321/2500000000 : ℝ)^4189 ≤ (44155305947551/100000000000000 : ℝ)^3165 := by
    have hnat : (1348052321 : ℕ)^4189*100000000000000^3165 ≤ 44155305947551^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348052321 2500000000 44155305947551 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164576509/312500000 : ℝ)^4189 ≤ (5349683325559/12500000000000 : ℝ)^3165 := by
    have hnat : (164576509 : ℕ)^4189*12500000000000^3165 ≤ 5349683325559^3165*312500000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164576509 312500000 5349683325559 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2146493507/10000000000 : ℝ), (1348052321/2500000000 : ℝ), (164576509/312500000 : ℝ)] ![(6523613715833/50000000000000 : ℝ), (44155305947551/100000000000000 : ℝ), (5349683325559/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2146493507/10000000000 : ℝ)|^4189 ≤ (6523613715833/50000000000000 : ℝ)^3165
        have hw : |(-2146493507/10000000000 : ℝ)|=(2146493507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348052321/2500000000 : ℝ)|^4189 ≤ (44155305947551/100000000000000 : ℝ)^3165
        have hw : |(1348052321/2500000000 : ℝ)|=(1348052321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164576509/312500000 : ℝ)|^4189 ≤ (5349683325559/12500000000000 : ℝ)^3165
        have hw : |(164576509/312500000 : ℝ)|=(164576509/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s8_1 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344574057/10000000000 : ℝ)*x 0 + (-2210269819/10000000000 : ℝ)*x 1 + (2633224439/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344574057/10000000000 : ℝ)^4189 ≤ (43639770284443/100000000000000 : ℝ)^3165 := by
    have hnat : (5344574057 : ℕ)^4189*100000000000000^3165 ≤ 43639770284443^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344574057 10000000000 43639770284443 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2210269819/10000000000 : ℝ)^4189 ≤ (6781378379103/50000000000000 : ℝ)^3165 := by
    have hnat : (2210269819 : ℕ)^4189*50000000000000^3165 ≤ 6781378379103^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2210269819 10000000000 6781378379103 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633224439/5000000000 : ℝ)^4189 ≤ (42797472950309/100000000000000 : ℝ)^3165 := by
    have hnat : (2633224439 : ℕ)^4189*100000000000000^3165 ≤ 42797472950309^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633224439 5000000000 42797472950309 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344574057/10000000000 : ℝ), (-2210269819/10000000000 : ℝ), (2633224439/5000000000 : ℝ)] ![(43639770284443/100000000000000 : ℝ), (6781378379103/50000000000000 : ℝ), (42797472950309/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344574057/10000000000 : ℝ)|^4189 ≤ (43639770284443/100000000000000 : ℝ)^3165
        have hw : |(5344574057/10000000000 : ℝ)|=(5344574057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2210269819/10000000000 : ℝ)|^4189 ≤ (6781378379103/50000000000000 : ℝ)^3165
        have hw : |(-2210269819/10000000000 : ℝ)|=(2210269819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633224439/5000000000 : ℝ)|^4189 ≤ (42797472950309/100000000000000 : ℝ)^3165
        have hw : |(2633224439/5000000000 : ℝ)|=(2633224439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s8_2 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672287107/5000000000 : ℝ)*x 0 + (5266448549/10000000000 : ℝ)*x 1 + (-442054009/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672287107/5000000000 : ℝ)^4189 ≤ (21819885990573/50000000000000 : ℝ)^3165 := by
    have hnat : (2672287107 : ℕ)^4189*50000000000000^3165 ≤ 21819885990573^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672287107 5000000000 21819885990573 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266448549/10000000000 : ℝ)^4189 ≤ (21398734705849/50000000000000 : ℝ)^3165 := by
    have hnat : (5266448549 : ℕ)^4189*50000000000000^3165 ≤ 21398734705849^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266448549 10000000000 21398734705849 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442054009/2000000000 : ℝ)^4189 ≤ (6781379296839/50000000000000 : ℝ)^3165 := by
    have hnat : (442054009 : ℕ)^4189*50000000000000^3165 ≤ 6781379296839^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442054009 2000000000 6781379296839 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672287107/5000000000 : ℝ), (5266448549/10000000000 : ℝ), (-442054009/2000000000 : ℝ)] ![(21819885990573/50000000000000 : ℝ), (21398734705849/50000000000000 : ℝ), (6781379296839/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672287107/5000000000 : ℝ)|^4189 ≤ (21819885990573/50000000000000 : ℝ)^3165
        have hw : |(2672287107/5000000000 : ℝ)|=(2672287107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266448549/10000000000 : ℝ)|^4189 ≤ (21398734705849/50000000000000 : ℝ)^3165
        have hw : |(5266448549/10000000000 : ℝ)|=(5266448549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442054009/2000000000 : ℝ)|^4189 ≤ (6781379296839/50000000000000 : ℝ)^3165
        have hw : |(-442054009/2000000000 : ℝ)|=(442054009/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s8_3 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4358652813/10000000000 : ℝ)*x 0 + (4234296347/10000000000 : ℝ)*x 1 + (1121651369/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358652813/10000000000 : ℝ)^4189 ≤ (33317221770489/100000000000000 : ℝ)^3165 := by
    have hnat : (4358652813 : ℕ)^4189*100000000000000^3165 ≤ 33317221770489^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358652813 10000000000 33317221770489 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4234296347/10000000000 : ℝ)^4189 ≤ (641298958441/2000000000000 : ℝ)^3165 := by
    have hnat : (4234296347 : ℕ)^4189*2000000000000^3165 ≤ 641298958441^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234296347 10000000000 641298958441 2000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121651369/2500000000 : ℝ)^4189 ≤ (34617830292931/100000000000000 : ℝ)^3165 := by
    have hnat : (1121651369 : ℕ)^4189*100000000000000^3165 ≤ 34617830292931^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121651369 2500000000 34617830292931 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358652813/10000000000 : ℝ), (4234296347/10000000000 : ℝ), (1121651369/2500000000 : ℝ)] ![(33317221770489/100000000000000 : ℝ), (641298958441/2000000000000 : ℝ), (34617830292931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358652813/10000000000 : ℝ)|^4189 ≤ (33317221770489/100000000000000 : ℝ)^3165
        have hw : |(4358652813/10000000000 : ℝ)|=(4358652813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4234296347/10000000000 : ℝ)|^4189 ≤ (641298958441/2000000000000 : ℝ)^3165
        have hw : |(4234296347/10000000000 : ℝ)|=(4234296347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1121651369/2500000000 : ℝ)|^4189 ≤ (34617830292931/100000000000000 : ℝ)^3165
        have hw : |(1121651369/2500000000 : ℝ)|=(1121651369/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s8_4 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-85859921/400000000 : ℝ)*x 0 + (1316691221/2500000000 : ℝ)*x 1 + (673986467/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (85859921/400000000 : ℝ)^4189 ≤ (6523631889463/50000000000000 : ℝ)^3165 := by
    have hnat : (85859921 : ℕ)^4189*50000000000000^3165 ≤ 6523631889463^3165*400000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85859921 400000000 6523631889463 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316691221/2500000000 : ℝ)^4189 ≤ (5350108979387/12500000000000 : ℝ)^3165 := by
    have hnat : (1316691221 : ℕ)^4189*12500000000000^3165 ≤ 5350108979387^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316691221 2500000000 5350108979387 12500000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673986467/1250000000 : ℝ)^4189 ≤ (44151864366127/100000000000000 : ℝ)^3165 := by
    have hnat : (673986467 : ℕ)^4189*100000000000000^3165 ≤ 44151864366127^3165*1250000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673986467 1250000000 44151864366127 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-85859921/400000000 : ℝ), (1316691221/2500000000 : ℝ), (673986467/1250000000 : ℝ)] ![(6523631889463/50000000000000 : ℝ), (5350108979387/12500000000000 : ℝ), (44151864366127/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-85859921/400000000 : ℝ)|^4189 ≤ (6523631889463/50000000000000 : ℝ)^3165
        have hw : |(-85859921/400000000 : ℝ)|=(85859921/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316691221/2500000000 : ℝ)|^4189 ≤ (5350108979387/12500000000000 : ℝ)^3165
        have hw : |(1316691221/2500000000 : ℝ)|=(1316691221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673986467/1250000000 : ℝ)|^4189 ≤ (44151864366127/100000000000000 : ℝ)^3165
        have hw : |(673986467/1250000000 : ℝ)|=(673986467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s8_5 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2656306197/5000000000 : ℝ)*x 0 + (-521206723/2500000000 : ℝ)*x 1 + (5391891733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656306197/5000000000 : ℝ)^4189 ≤ (43294694522131/100000000000000 : ℝ)^3165 := by
    have hnat : (2656306197 : ℕ)^4189*100000000000000^3165 ≤ 43294694522131^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656306197 5000000000 43294694522131 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521206723/2500000000 : ℝ)^4189 ≤ (6276720565793/50000000000000 : ℝ)^3165 := by
    have hnat : (521206723 : ℕ)^4189*50000000000000^3165 ≤ 6276720565793^3165*2500000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521206723 2500000000 6276720565793 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391891733/10000000000 : ℝ)^4189 ≤ (22075932166807/50000000000000 : ℝ)^3165 := by
    have hnat : (5391891733 : ℕ)^4189*50000000000000^3165 ≤ 22075932166807^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391891733 10000000000 22075932166807 50000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656306197/5000000000 : ℝ), (-521206723/2500000000 : ℝ), (5391891733/10000000000 : ℝ)] ![(43294694522131/100000000000000 : ℝ), (6276720565793/50000000000000 : ℝ), (22075932166807/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656306197/5000000000 : ℝ)|^4189 ≤ (43294694522131/100000000000000 : ℝ)^3165
        have hw : |(2656306197/5000000000 : ℝ)|=(2656306197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-521206723/2500000000 : ℝ)|^4189 ≤ (6276720565793/50000000000000 : ℝ)^3165
        have hw : |(-521206723/2500000000 : ℝ)|=(521206723/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391891733/10000000000 : ℝ)|^4189 ≤ (22075932166807/50000000000000 : ℝ)^3165
        have hw : |(5391891733/10000000000 : ℝ)|=(5391891733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s8_6 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312612393/10000000000 : ℝ)*x 0 + (1078378347/2000000000 : ℝ)*x 1 + (-2084826891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312612393/10000000000 : ℝ)^4189 ≤ (8658938902269/20000000000000 : ℝ)^3165 := by
    have hnat : (5312612393 : ℕ)^4189*20000000000000^3165 ≤ 8658938902269^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312612393 10000000000 8658938902269 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078378347/2000000000 : ℝ)^4189 ≤ (4415186435529/10000000000000 : ℝ)^3165 := by
    have hnat : (1078378347 : ℕ)^4189*10000000000000^3165 ≤ 4415186435529^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078378347 2000000000 4415186435529 10000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2084826891/10000000000 : ℝ)^4189 ≤ (392295035113/3125000000000 : ℝ)^3165 := by
    have hnat : (2084826891 : ℕ)^4189*3125000000000^3165 ≤ 392295035113^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2084826891 10000000000 392295035113 3125000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312612393/10000000000 : ℝ), (1078378347/2000000000 : ℝ), (-2084826891/10000000000 : ℝ)] ![(8658938902269/20000000000000 : ℝ), (4415186435529/10000000000000 : ℝ), (392295035113/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312612393/10000000000 : ℝ)|^4189 ≤ (8658938902269/20000000000000 : ℝ)^3165
        have hw : |(5312612393/10000000000 : ℝ)|=(5312612393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078378347/2000000000 : ℝ)|^4189 ≤ (4415186435529/10000000000000 : ℝ)^3165
        have hw : |(1078378347/2000000000 : ℝ)|=(1078378347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2084826891/10000000000 : ℝ)|^4189 ≤ (392295035113/3125000000000 : ℝ)^3165
        have hw : |(-2084826891/10000000000 : ℝ)|=(2084826891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1185_s8_7 (p : ℝ) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4358662059/10000000000 : ℝ)*x 0 + (2242985597/5000000000 : ℝ)*x 1 + (846986651/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358662059/10000000000 : ℝ)^4189 ≤ (6663463062521/20000000000000 : ℝ)^3165 := by
    have hnat : (4358662059 : ℕ)^4189*20000000000000^3165 ≤ 6663463062521^3165*10000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358662059 10000000000 6663463062521 20000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242985597/5000000000 : ℝ)^4189 ≤ (34611353036919/100000000000000 : ℝ)^3165 := by
    have hnat : (2242985597 : ℕ)^4189*100000000000000^3165 ≤ 34611353036919^3165*5000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242985597 5000000000 34611353036919 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (846986651/2000000000 : ℝ)^4189 ≤ (32071331632881/100000000000000 : ℝ)^3165 := by
    have hnat : (846986651 : ℕ)^4189*100000000000000^3165 ≤ 32071331632881^3165*2000000000^4189 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      846986651 2000000000 32071331632881 100000000000000 4189 3165 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4189/1024 : ℝ)) 4189 3165 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358662059/10000000000 : ℝ), (2242985597/5000000000 : ℝ), (846986651/2000000000 : ℝ)] ![(6663463062521/20000000000000 : ℝ), (34611353036919/100000000000000 : ℝ), (32071331632881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358662059/10000000000 : ℝ)|^4189 ≤ (6663463062521/20000000000000 : ℝ)^3165
        have hw : |(4358662059/10000000000 : ℝ)|=(4358662059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242985597/5000000000 : ℝ)|^4189 ≤ (34611353036919/100000000000000 : ℝ)^3165
        have hw : |(2242985597/5000000000 : ℝ)|=(2242985597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(846986651/2000000000 : ℝ)|^4189 ≤ (32071331632881/100000000000000 : ℝ)^3165
        have hw : |(846986651/2000000000 : ℝ)|=(846986651/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1185_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11409/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14073/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (713/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7037/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (713/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (713/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7037/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (713/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (713/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7037/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (713/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (713/6250 : ℝ) ^ (8377/2048 : ℝ) ≤ (13921110164053641/100000000000000000000 : ℝ) := by
    have hpowers : (713/6250 : ℝ)^8377 ≤ (13921110164053641/100000000000000000000 : ℝ)^2048 := by
      have hnat : (713 : ℕ)^8377*100000000000000000000^2048 ≤ 13921110164053641^2048*6250^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        713 6250 13921110164053641 100000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (713/6250 : ℝ)) (X := (13921110164053641/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (7037/50000 : ℝ) ^ (8377/2048 : ℝ) ≤ (6573172197442367/20000000000000000000 : ℝ) := by
    have hpowers : (7037/50000 : ℝ)^8377 ≤ (6573172197442367/20000000000000000000 : ℝ)^2048 := by
      have hnat : (7037 : ℕ)^8377*20000000000000000000^2048 ≤ 6573172197442367^2048*50000^8377 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7037 50000 6573172197442367 20000000000000000000 8377 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7037/50000 : ℝ)) (X := (6573172197442367/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013921110164053641/50000000000000000000 : ℝ) ≤ (5000340306022023/5000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (50013921110164053641/50000000000000000000 : ℝ)^2048 ≤ (5000340306022023/5000000000000000 : ℝ)^8377 := by
      have hnat : (50013921110164053641 : ℕ)^2048*5000000000000000^8377 ≤ 5000340306022023^8377*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013921110164053641 50000000000000000000 5000340306022023 5000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000340306022023/5000000000000000 : ℝ)) (X := (50013921110164053641/50000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011696742787816369/25000000000000000000 : ℝ) ≤ (2000228728151167/2000000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (25011696742787816369/25000000000000000000 : ℝ)^2048 ≤ (2000228728151167/2000000000000000 : ℝ)^8377 := by
      have hnat : (25011696742787816369 : ℕ)^2048*2000000000000000^8377 ≤ 2000228728151167^8377*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011696742787816369 25000000000000000000 2000228728151167 2000000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000228728151167/2000000000000000 : ℝ)) (X := (25011696742787816369/25000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006573172197442367/10000000000000000000 : ℝ) ≤ (1250200833683453/1250000000000000 : ℝ) ^ (8377/2048 : ℝ) := by
    have hpowers : (10006573172197442367/10000000000000000000 : ℝ)^2048 ≤ (1250200833683453/1250000000000000 : ℝ)^8377 := by
      have hnat : (10006573172197442367 : ℕ)^2048*1250000000000000^8377 ≤ 1250200833683453^8377*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006573172197442367 10000000000000000000 1250200833683453 1250000000000000 2048 8377 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250200833683453/1250000000000000 : ℝ)) (X := (10006573172197442367/10000000000000000000 : ℝ)) (by norm_num) 8377 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13921110164053641/100000000000000000000 : ℝ) ≤ ((214929435875977813/215000000000000000 : ℝ)+2*(463028711789/266600000000000 : ℝ)*(713/6250 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (214929435875977813/215000000000000000 : ℝ)+2*(463028711789/266600000000000 : ℝ)*(713/6250 : ℝ)=(5000340306022023/5000000000000000 : ℝ) by norm_num, show 1+2*(13921110164053641/100000000000000000000 : ℝ)=(50013921110164053641/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6573172197442367/20000000000000000000 : ℝ)+(13921110164053641/100000000000000000000 : ℝ) ≤ ((214929435875977813/215000000000000000 : ℝ)+(463028711789/266600000000000 : ℝ)*((7037/50000 : ℝ)+(713/6250 : ℝ)))^(8377/2048 : ℝ) := by
    rw [show (214929435875977813/215000000000000000 : ℝ)+(463028711789/266600000000000 : ℝ)*((7037/50000 : ℝ)+(713/6250 : ℝ))=(2000228728151167/2000000000000000 : ℝ) by norm_num, show 1+(6573172197442367/20000000000000000000 : ℝ)+(13921110164053641/100000000000000000000 : ℝ)=(25011696742787816369/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6573172197442367/20000000000000000000 : ℝ) ≤ ((214929435875977813/215000000000000000 : ℝ)+2*(463028711789/266600000000000 : ℝ)*(7037/50000 : ℝ))^(8377/2048 : ℝ) := by
    rw [show (214929435875977813/215000000000000000 : ℝ)+2*(463028711789/266600000000000 : ℝ)*(7037/50000 : ℝ)=(1250200833683453/1250000000000000 : ℝ) by norm_num, show 1+2*(6573172197442367/20000000000000000000 : ℝ)=(10006573172197442367/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (214929435875977813/215000000000000000 : ℝ)*(X 1 0+X 2 0)+(463028711789/266600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (713/6250 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (214929435875977813/215000000000000000 : ℝ)) (alpha := (463028711789/266600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (214929435875977813/215000000000000000 : ℝ)*(X 0 1+X 2 1)+(463028711789/266600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (713/6250 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (214929435875977813/215000000000000000 : ℝ)) (alpha := (463028711789/266600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (214929435875977813/215000000000000000 : ℝ)*(X 0 2+X 1 2)+(463028711789/266600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8377/2048 : ℝ)) (lo := (713/6250 : ℝ)) (hi := (7037/50000 : ℝ)) (c := (214929435875977813/215000000000000000 : ℝ)) (alpha := (463028711789/266600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2146493507/10000000000 : ℝ)*X 0 0+(1348052321/2500000000 : ℝ)*X 0 1+(164576509/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344574057/10000000000 : ℝ)*X 1 0+(-2210269819/10000000000 : ℝ)*X 1 1+(2633224439/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672287107/5000000000 : ℝ)*X 2 0+(5266448549/10000000000 : ℝ)*X 2 1+(-442054009/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358652813/10000000000 : ℝ)*X 0 0+(4234296347/10000000000 : ℝ)*X 0 1+(1121651369/2500000000 : ℝ)*X 0 2+(4358652813/10000000000 : ℝ)*X 1 0+(4234296347/10000000000 : ℝ)*X 1 1+(1121651369/2500000000 : ℝ)*X 1 2+(4358652813/10000000000 : ℝ)*X 2 0+(4234296347/10000000000 : ℝ)*X 2 1+(1121651369/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-85859921/400000000 : ℝ)*X 0 0+(1316691221/2500000000 : ℝ)*X 0 1+(673986467/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656306197/5000000000 : ℝ)*X 1 0+(-521206723/2500000000 : ℝ)*X 1 1+(5391891733/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312612393/10000000000 : ℝ)*X 2 0+(1078378347/2000000000 : ℝ)*X 2 1+(-2084826891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4358662059/10000000000 : ℝ)*X 0 0+(2242985597/5000000000 : ℝ)*X 0 1+(846986651/2000000000 : ℝ)*X 0 2+(4358662059/10000000000 : ℝ)*X 1 0+(2242985597/5000000000 : ℝ)*X 1 1+(846986651/2000000000 : ℝ)*X 1 2+(4358662059/10000000000 : ℝ)*X 2 0+(2242985597/5000000000 : ℝ)*X 2 1+(846986651/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1185_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1406780473320043326270575937/333250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1435593641/100000000000000 : ℝ)*(base19) + (399000351/25000000000000 : ℝ)*(base23) + (111014721/25000000000000 : ℝ)*(upper3) + (39110837/100000000000000 : ℝ)*(upper4) + (66488023/100000000000000 : ℝ)*(upper5) + (5957578508994207/100000000000000 : ℝ)*(major0) + (5957578508994207/100000000000000 : ℝ)*(major1) + (5957578508994207/100000000000000 : ℝ)*(major2) + (993957764426089/12500000000000 : ℝ)*(sp0) + (7951716851587821/100000000000000 : ℝ)*(sp1) + (7951716691180059/100000000000000 : ℝ)*(sp2) + (3963410633883197/100000000000000 : ℝ)*(sp3) + (56171772751/100000000000000 : ℝ)*(sp4) + (27956210517/100000000000000 : ℝ)*(sp7) + (1981719295046857/50000000000000 : ℝ)*(f.failure) + (7951718287181463/100000000000000 : ℝ)*(f.sum) + (13042010232673/13330000000000000000000000000 : ℝ)*base65 + (7911152301552983021/666500000000000000000000000000000 : ℝ)*base67 + (1210842396172016979/666500000000000000000000000000000 : ℝ)*base70 + (7323791817995016979/666500000000000000000000000000000 : ℝ)*base72 + (48943081347183/13330000000000000000000000000 : ℝ)*base73 + (12049612297168983021/666500000000000000000000000000000 : ℝ)*base75 + (1214980402476483021/666500000000000000000000000000000 : ℝ)*base77 + (21559388523269483021/666500000000000000000000000000000 : ℝ)*base79 + (81160953763837/13330000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (797667/250000000000000000000 : ℝ)*base90 + (797667/250000000000000000000 : ℝ)*base92 + (797667/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1147747807433265466035919587/166625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1236016293/100000000000000 : ℝ)*(base19) + (269654137/20000000000000 : ℝ)*(base23) + (431655667/100000000000000 : ℝ)*(lower1) + (135516503/100000000000000 : ℝ)*(upper3) + (51992321/100000000000000 : ℝ)*(lower4) + (70854779/50000000000000 : ℝ)*(upper5) + (2993824539470643/50000000000000 : ℝ)*(major0) + (2993824539470643/50000000000000 : ℝ)*(major1) + (2993824539470643/50000000000000 : ℝ)*(major2) + (660417861/25000000000000 : ℝ)*(sp2) + (7991854086522217/100000000000000 : ℝ)*(sp4) + (1997963212626481/25000000000000 : ℝ)*(sp5) + (7991850096580089/100000000000000 : ℝ)*(sp6) + (995860960438333/25000000000000 : ℝ)*(sp7) + (995860960438333/25000000000000 : ℝ)*(f.failure) + (7991854086522217/100000000000000 : ℝ)*(f.sum) + (11526351484733/1666250000000000000000000000 : ℝ)*base65 + (9909236016629331529/333250000000000000000000000000000 : ℝ)*base67 + (5493381744692668471/333250000000000000000000000000000 : ℝ)*base70 + (29576525543836668471/333250000000000000000000000000000 : ℝ)*base72 + (77238280527327/6665000000000000000000000000 : ℝ)*base73 + (115922780764272331529/333250000000000000000000000000000 : ℝ)*base75 + (2312731842341918471/333250000000000000000000000000000 : ℝ)*base78 + (2304966783425418471/333250000000000000000000000000000 : ℝ)*base80 + (7089100807981/3332500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1760223/125000000000000000000 : ℝ)*base90 + (1760223/125000000000000000000 : ℝ)*base92 + (1760223/125000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1185_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7037/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (713/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1185_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1185_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1185_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1185_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1185_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8377/2048 : ℝ) ≤ p) (hpb : p ≤ (4189/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (7515669/5000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7053/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11377/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11409/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14073/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1185_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
