-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1230_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:14:53.175156+00:00
-- url     : https://prove2.me/submissions/11dfd934-81c2-410f-b40b-2f9335795a39

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
theorem support_rectangle_w1230_s9_0 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672180051/5000000000 : ℝ)*x 0 + (-437702551/2000000000 : ℝ)*x 1 + (2633549711/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672180051/5000000000 : ℝ)^8423 ≤ (10924985916957/25000000000000 : ℝ)^6375 := by
    have hnat : (2672180051 : ℕ)^8423*25000000000000^6375 ≤ 10924985916957^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672180051 5000000000 10924985916957 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (437702551/2000000000 : ℝ)^8423 ≤ (13432867784701/100000000000000 : ℝ)^6375 := by
    have hnat : (437702551 : ℕ)^8423*100000000000000^6375 ≤ 13432867784701^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      437702551 2000000000 13432867784701 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2633549711/5000000000 : ℝ)^8423 ≤ (2143359426233/5000000000000 : ℝ)^6375 := by
    have hnat : (2633549711 : ℕ)^8423*5000000000000^6375 ≤ 2143359426233^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633549711 5000000000 2143359426233 5000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672180051/5000000000 : ℝ), (-437702551/2000000000 : ℝ), (2633549711/5000000000 : ℝ)] ![(10924985916957/25000000000000 : ℝ), (13432867784701/100000000000000 : ℝ), (2143359426233/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672180051/5000000000 : ℝ)|^8423 ≤ (10924985916957/25000000000000 : ℝ)^6375
        have hw : |(2672180051/5000000000 : ℝ)|=(2672180051/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-437702551/2000000000 : ℝ)|^8423 ≤ (13432867784701/100000000000000 : ℝ)^6375
        have hw : |(-437702551/2000000000 : ℝ)|=(437702551/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2633549711/5000000000 : ℝ)|^8423 ≤ (2143359426233/5000000000000 : ℝ)^6375
        have hw : |(2633549711/5000000000 : ℝ)|=(2633549711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s9_1 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352423979/10000000000 : ℝ)*x 0 + (4228438129/10000000000 : ℝ)*x 1 + (447995229/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352423979/10000000000 : ℝ)^8423 ≤ (6663490996073/20000000000000 : ℝ)^6375 := by
    have hnat : (4352423979 : ℕ)^8423*20000000000000^6375 ≤ 6663490996073^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352423979 10000000000 6663490996073 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4228438129/10000000000 : ℝ)^8423 ≤ (320692251377/1000000000000 : ℝ)^6375 := by
    have hnat : (4228438129 : ℕ)^8423*1000000000000^6375 ≤ 320692251377^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4228438129 10000000000 320692251377 1000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (447995229/1000000000 : ℝ)^8423 ≤ (8653329964897/25000000000000 : ℝ)^6375 := by
    have hnat : (447995229 : ℕ)^8423*25000000000000^6375 ≤ 8653329964897^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447995229 1000000000 8653329964897 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352423979/10000000000 : ℝ), (4228438129/10000000000 : ℝ), (447995229/1000000000 : ℝ)] ![(6663490996073/20000000000000 : ℝ), (320692251377/1000000000000 : ℝ), (8653329964897/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352423979/10000000000 : ℝ)|^8423 ≤ (6663490996073/20000000000000 : ℝ)^6375
        have hw : |(4352423979/10000000000 : ℝ)|=(4352423979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4228438129/10000000000 : ℝ)|^8423 ≤ (320692251377/1000000000000 : ℝ)^6375
        have hw : |(4228438129/10000000000 : ℝ)|=(4228438129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(447995229/1000000000 : ℝ)|^8423 ≤ (8653329964897/25000000000000 : ℝ)^6375
        have hw : |(447995229/1000000000 : ℝ)|=(447995229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s9_2 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-53137633/250000000 : ℝ)*x 0 + (1053482569/2000000000 : ℝ)*x 1 + (5391058767/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53137633/250000000 : ℝ)^8423 ≤ (12924273210187/100000000000000 : ℝ)^6375 := by
    have hnat : (53137633 : ℕ)^8423*100000000000000^6375 ≤ 12924273210187^6375*250000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53137633 250000000 12924273210187 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1053482569/2000000000 : ℝ)^8423 ≤ (42870558875493/100000000000000 : ℝ)^6375 := by
    have hnat : (1053482569 : ℕ)^8423*100000000000000^6375 ≤ 42870558875493^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053482569 2000000000 42870558875493 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5391058767/10000000000 : ℝ)^8423 ≤ (44205167896441/100000000000000 : ℝ)^6375 := by
    have hnat : (5391058767 : ℕ)^8423*100000000000000^6375 ≤ 44205167896441^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5391058767 10000000000 44205167896441 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53137633/250000000 : ℝ), (1053482569/2000000000 : ℝ), (5391058767/10000000000 : ℝ)] ![(12924273210187/100000000000000 : ℝ), (42870558875493/100000000000000 : ℝ), (44205167896441/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53137633/250000000 : ℝ)|^8423 ≤ (12924273210187/100000000000000 : ℝ)^6375
        have hw : |(-53137633/250000000 : ℝ)|=(53137633/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1053482569/2000000000 : ℝ)|^8423 ≤ (42870558875493/100000000000000 : ℝ)^6375
        have hw : |(1053482569/2000000000 : ℝ)|=(1053482569/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5391058767/10000000000 : ℝ)|^8423 ≤ (44205167896441/100000000000000 : ℝ)^6375
        have hw : |(5391058767/10000000000 : ℝ)|=(5391058767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s9_3 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664084567/1250000000 : ℝ)*x 0 + (-412910559/2000000000 : ℝ)*x 1 + (1078211913/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664084567/1250000000 : ℝ)^8423 ≤ (21678985453747/50000000000000 : ℝ)^6375 := by
    have hnat : (664084567 : ℕ)^8423*50000000000000^6375 ≤ 21678985453747^6375*1250000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664084567 1250000000 21678985453747 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (412910559/2000000000 : ℝ)^8423 ≤ (6218426266267/50000000000000 : ℝ)^6375 := by
    have hnat : (412910559 : ℕ)^8423*50000000000000^6375 ≤ 6218426266267^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412910559 2000000000 6218426266267 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078211913/2000000000 : ℝ)^8423 ≤ (11051294135477/25000000000000 : ℝ)^6375 := by
    have hnat : (1078211913 : ℕ)^8423*25000000000000^6375 ≤ 11051294135477^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078211913 2000000000 11051294135477 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664084567/1250000000 : ℝ), (-412910559/2000000000 : ℝ), (1078211913/2000000000 : ℝ)] ![(21678985453747/50000000000000 : ℝ), (6218426266267/50000000000000 : ℝ), (11051294135477/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664084567/1250000000 : ℝ)|^8423 ≤ (21678985453747/50000000000000 : ℝ)^6375
        have hw : |(664084567/1250000000 : ℝ)|=(664084567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-412910559/2000000000 : ℝ)|^8423 ≤ (6218426266267/50000000000000 : ℝ)^6375
        have hw : |(-412910559/2000000000 : ℝ)|=(412910559/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078211913/2000000000 : ℝ)|^8423 ≤ (11051294135477/25000000000000 : ℝ)^6375
        have hw : |(1078211913/2000000000 : ℝ)|=(1078211913/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s9_4 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312676967/10000000000 : ℝ)*x 0 + (2695529469/5000000000 : ℝ)*x 1 + (-1032276533/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312676967/10000000000 : ℝ)^8423 ≤ (8671595110999/20000000000000 : ℝ)^6375 := by
    have hnat : (5312676967 : ℕ)^8423*20000000000000^6375 ≤ 8671595110999^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312676967 10000000000 8671595110999 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695529469/5000000000 : ℝ)^8423 ≤ (44205169749041/100000000000000 : ℝ)^6375 := by
    have hnat : (2695529469 : ℕ)^8423*100000000000000^6375 ≤ 44205169749041^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695529469 5000000000 44205169749041 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032276533/5000000000 : ℝ)^8423 ≤ (6218427344743/50000000000000 : ℝ)^6375 := by
    have hnat : (1032276533 : ℕ)^8423*50000000000000^6375 ≤ 6218427344743^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032276533 5000000000 6218427344743 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312676967/10000000000 : ℝ), (2695529469/5000000000 : ℝ), (-1032276533/5000000000 : ℝ)] ![(8671595110999/20000000000000 : ℝ), (44205169749041/100000000000000 : ℝ), (6218427344743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312676967/10000000000 : ℝ)|^8423 ≤ (8671595110999/20000000000000 : ℝ)^6375
        have hw : |(5312676967/10000000000 : ℝ)|=(5312676967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695529469/5000000000 : ℝ)|^8423 ≤ (44205169749041/100000000000000 : ℝ)^6375
        have hw : |(2695529469/5000000000 : ℝ)|=(2695529469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1032276533/5000000000 : ℝ)|^8423 ≤ (6218427344743/50000000000000 : ℝ)^6375
        have hw : |(-1032276533/5000000000 : ℝ)|=(1032276533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_s9_5 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4352433259/10000000000 : ℝ)*x 0 + (4479319187/10000000000 : ℝ)*x 1 + (2114536849/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4352433259/10000000000 : ℝ)^8423 ≤ (8329387209811/25000000000000 : ℝ)^6375 := by
    have hnat : (4352433259 : ℕ)^8423*25000000000000^6375 ≤ 8329387209811^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4352433259 10000000000 8329387209811 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4479319187/10000000000 : ℝ)^8423 ≤ (34606857055501/100000000000000 : ℝ)^6375 := by
    have hnat : (4479319187 : ℕ)^8423*100000000000000^6375 ≤ 34606857055501^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479319187 10000000000 34606857055501 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2114536849/5000000000 : ℝ)^8423 ≤ (32075594094293/100000000000000 : ℝ)^6375 := by
    have hnat : (2114536849 : ℕ)^8423*100000000000000^6375 ≤ 32075594094293^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2114536849 5000000000 32075594094293 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4352433259/10000000000 : ℝ), (4479319187/10000000000 : ℝ), (2114536849/5000000000 : ℝ)] ![(8329387209811/25000000000000 : ℝ), (34606857055501/100000000000000 : ℝ), (32075594094293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4352433259/10000000000 : ℝ)|^8423 ≤ (8329387209811/25000000000000 : ℝ)^6375
        have hw : |(4352433259/10000000000 : ℝ)|=(4352433259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4479319187/10000000000 : ℝ)|^8423 ≤ (34606857055501/100000000000000 : ℝ)^6375
        have hw : |(4479319187/10000000000 : ℝ)|=(4479319187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2114536849/5000000000 : ℝ)|^8423 ≤ (32075594094293/100000000000000 : ℝ)^6375
        have hw : |(2114536849/5000000000 : ℝ)|=(2114536849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1230_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2293/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14097/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2293/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2293/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2293/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7049/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2293/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2293/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7049/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2293/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2293/20000 : ℝ) ^ (4211/1024 : ℝ) ≤ (2709502334757541/20000000000000000000 : ℝ) := by
    have hpowers : (2293/20000 : ℝ)^4211 ≤ (2709502334757541/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2293 : ℕ)^4211*20000000000000000000^1024 ≤ 2709502334757541^1024*20000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2293 20000 2709502334757541 20000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2293/20000 : ℝ)) (X := (2709502334757541/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7049/50000 : ℝ) ^ (4211/1024 : ℝ) ≤ (990664148032197/3125000000000000000 : ℝ) := by
    have hpowers : (7049/50000 : ℝ)^4211 ≤ (990664148032197/3125000000000000000 : ℝ)^1024 := by
      have hnat : (7049 : ℕ)^4211*3125000000000000000^1024 ≤ 990664148032197^1024*50000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7049 50000 990664148032197 3125000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7049/50000 : ℝ)) (X := (990664148032197/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002709502334757541/10000000000000000000 : ℝ) ≤ (10000658809299403/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (10002709502334757541/10000000000000000000 : ℝ)^1024 ≤ (10000658809299403/10000000000000000 : ℝ)^4211 := by
      have hnat : (10002709502334757541 : ℕ)^1024*10000000000000000^4211 ≤ 10000658809299403^4211*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002709502334757541 10000000000000000000 10000658809299403 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000658809299403/10000000000000000 : ℝ)) (X := (10002709502334757541/10000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045248764410818009/100000000000000000000 : ℝ) ≤ (10001100137807573/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (100045248764410818009/100000000000000000000 : ℝ)^1024 ≤ (10001100137807573/10000000000000000 : ℝ)^4211 := by
      have hnat : (100045248764410818009 : ℕ)^1024*10000000000000000^4211 ≤ 10001100137807573^4211*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045248764410818009 100000000000000000000 10001100137807573 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001100137807573/10000000000000000 : ℝ)) (X := (100045248764410818009/100000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1563490664148032197/1562500000000000000 : ℝ) ≤ (10001541466315743/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (1563490664148032197/1562500000000000000 : ℝ)^1024 ≤ (10001541466315743/10000000000000000 : ℝ)^4211 := by
      have hnat : (1563490664148032197 : ℕ)^1024*10000000000000000^4211 ≤ 10001541466315743^4211*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1563490664148032197 1562500000000000000 10001541466315743 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001541466315743/10000000000000000 : ℝ)) (X := (1563490664148032197/1562500000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2709502334757541/20000000000000000000 : ℝ) ≤ ((26321614982192989999/26330000000000000000 : ℝ)+2*(44132850817/26330000000000 : ℝ)*(2293/20000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (26321614982192989999/26330000000000000000 : ℝ)+2*(44132850817/26330000000000 : ℝ)*(2293/20000 : ℝ)=(10000658809299403/10000000000000000 : ℝ) by norm_num, show 1+2*(2709502334757541/20000000000000000000 : ℝ)=(10002709502334757541/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(990664148032197/3125000000000000000 : ℝ)+(2709502334757541/20000000000000000000 : ℝ) ≤ ((26321614982192989999/26330000000000000000 : ℝ)+(44132850817/26330000000000 : ℝ)*((7049/50000 : ℝ)+(2293/20000 : ℝ)))^(4211/1024 : ℝ) := by
    rw [show (26321614982192989999/26330000000000000000 : ℝ)+(44132850817/26330000000000 : ℝ)*((7049/50000 : ℝ)+(2293/20000 : ℝ))=(10001100137807573/10000000000000000 : ℝ) by norm_num, show 1+(990664148032197/3125000000000000000 : ℝ)+(2709502334757541/20000000000000000000 : ℝ)=(100045248764410818009/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(990664148032197/3125000000000000000 : ℝ) ≤ ((26321614982192989999/26330000000000000000 : ℝ)+2*(44132850817/26330000000000 : ℝ)*(7049/50000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (26321614982192989999/26330000000000000000 : ℝ)+2*(44132850817/26330000000000 : ℝ)*(7049/50000 : ℝ)=(10001541466315743/10000000000000000 : ℝ) by norm_num, show 1+2*(990664148032197/3125000000000000000 : ℝ)=(1563490664148032197/1562500000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (26321614982192989999/26330000000000000000 : ℝ)*(X 1 0+X 2 0)+(44132850817/26330000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (2293/20000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (26321614982192989999/26330000000000000000 : ℝ)) (alpha := (44132850817/26330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (26321614982192989999/26330000000000000000 : ℝ)*(X 0 1+X 2 1)+(44132850817/26330000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (2293/20000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (26321614982192989999/26330000000000000000 : ℝ)) (alpha := (44132850817/26330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (26321614982192989999/26330000000000000000 : ℝ)*(X 0 2+X 1 2)+(44132850817/26330000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (2293/20000 : ℝ)) (hi := (7049/50000 : ℝ)) (c := (26321614982192989999/26330000000000000000 : ℝ)) (alpha := (44132850817/26330000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((2672180051/5000000000 : ℝ)*X 1 0+(-437702551/2000000000 : ℝ)*X 1 1+(2633549711/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s9_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4352423979/10000000000 : ℝ)*X 0 0+(4228438129/10000000000 : ℝ)*X 0 1+(447995229/1000000000 : ℝ)*X 0 2+(4352423979/10000000000 : ℝ)*X 1 0+(4228438129/10000000000 : ℝ)*X 1 1+(447995229/1000000000 : ℝ)*X 1 2+(4352423979/10000000000 : ℝ)*X 2 0+(4228438129/10000000000 : ℝ)*X 2 1+(447995229/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s9_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-53137633/250000000 : ℝ)*X 0 0+(1053482569/2000000000 : ℝ)*X 0 1+(5391058767/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s9_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((664084567/1250000000 : ℝ)*X 1 0+(-412910559/2000000000 : ℝ)*X 1 1+(1078211913/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s9_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5312676967/10000000000 : ℝ)*X 2 0+(2695529469/5000000000 : ℝ)*X 2 1+(-1032276533/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s9_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4352433259/10000000000 : ℝ)*X 0 0+(4479319187/10000000000 : ℝ)*X 0 1+(2114536849/5000000000 : ℝ)*X 0 2+(4352433259/10000000000 : ℝ)*X 1 0+(4479319187/10000000000 : ℝ)*X 1 1+(2114536849/5000000000 : ℝ)*X 1 2+(4352433259/10000000000 : ℝ)*X 2 0+(4479319187/10000000000 : ℝ)*X 2 1+(2114536849/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_s9_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3165268805065614914317593669/1316500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60457887/100000000000000 : ℝ)*(base19) + (174388731/20000000000000 : ℝ)*(base23) + (128707979/25000000000000 : ℝ)*(lower1) + (12060437/12500000000000 : ℝ)*(upper2) + (51937759/50000000000000 : ℝ)*(upper3) + (6041826913566259/100000000000000 : ℝ)*(major0) + (6041826913566259/100000000000000 : ℝ)*(major1) + (6041826913566259/100000000000000 : ℝ)*(major2) + (550025997/12500000000000 : ℝ)*(sp0) + (1725132747/12500000000000 : ℝ)*(sp1) + (12940106162683/160000000000 : ℝ)*(sp2) + (2021890472752753/25000000000000 : ℝ)*(sp3) + (404378273986661/5000000000000 : ℝ)*(sp4) + (999018398562531/25000000000000 : ℝ)*(sp5) + (39960873953121/1000000000000 : ℝ)*(f.failure) + (12940106162683/160000000000 : ℝ)*(f.sum) + (409161070873/1316500000000000000000000000 : ℝ)*base65 + (46372580725597156259/2633000000000000000000000000000000 : ℝ)*base68 + (34067532348847156259/2633000000000000000000000000000000 : ℝ)*base70 + (16678957815318156259/2633000000000000000000000000000000 : ℝ)*base72 + (143336166917/263300000000000000000000000 : ℝ)*base74 + (30677298734438156259/2633000000000000000000000000000000 : ℝ)*base76 + (24557303920866156259/2633000000000000000000000000000000 : ℝ)*base78 + (111860717299102156259/2633000000000000000000000000000000 : ℝ)*base80 + (1209704168537/263300000000000000000000000 : ℝ)*base82 + (39877/100000000000000000000 : ℝ)*base90 + (39877/100000000000000000000 : ℝ)*base92 + (39877/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1230_s9 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1230_s9 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1230_box_0 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2001443631/10000000000 : ℝ)*x 0 + (215000781/400000000 : ℝ)*x 1 + (2687509669/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2001443631/10000000000 : ℝ)^8423 ≤ (5968517863179/50000000000000 : ℝ)^6375 := by
    have hnat : (2001443631 : ℕ)^8423*50000000000000^6375 ≤ 5968517863179^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2001443631 10000000000 5968517863179 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215000781/400000000 : ℝ)^8423 ≤ (22015741571847/50000000000000 : ℝ)^6375 := by
    have hnat : (215000781 : ℕ)^8423*50000000000000^6375 ≤ 22015741571847^6375*400000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215000781 400000000 22015741571847 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2687509669/5000000000 : ℝ)^8423 ≤ (4403148111969/10000000000000 : ℝ)^6375 := by
    have hnat : (2687509669 : ℕ)^8423*10000000000000^6375 ≤ 4403148111969^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2687509669 5000000000 4403148111969 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2001443631/10000000000 : ℝ), (215000781/400000000 : ℝ), (2687509669/5000000000 : ℝ)] ![(5968517863179/50000000000000 : ℝ), (22015741571847/50000000000000 : ℝ), (4403148111969/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2001443631/10000000000 : ℝ)|^8423 ≤ (5968517863179/50000000000000 : ℝ)^6375
        have hw : |(-2001443631/10000000000 : ℝ)|=(2001443631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215000781/400000000 : ℝ)|^8423 ≤ (22015741571847/50000000000000 : ℝ)^6375
        have hw : |(215000781/400000000 : ℝ)|=(215000781/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2687509669/5000000000 : ℝ)|^8423 ≤ (4403148111969/10000000000000 : ℝ)^6375
        have hw : |(2687509669/5000000000 : ℝ)|=(2687509669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_1 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5296712187/10000000000 : ℝ)*x 0 + (-2107848721/10000000000 : ℝ)*x 1 + (537501927/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5296712187/10000000000 : ℝ)^8423 ≤ (43185909455993/100000000000000 : ℝ)^6375 := by
    have hnat : (5296712187 : ℕ)^8423*100000000000000^6375 ≤ 43185909455993^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5296712187 10000000000 43185909455993 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107848721/10000000000 : ℝ)^8423 ≤ (12782610148453/100000000000000 : ℝ)^6375 := by
    have hnat : (2107848721 : ℕ)^8423*100000000000000^6375 ≤ 12782610148453^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107848721 10000000000 12782610148453 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (537501927/1000000000 : ℝ)^8423 ≤ (5503935047961/12500000000000 : ℝ)^6375 := by
    have hnat : (537501927 : ℕ)^8423*12500000000000^6375 ≤ 5503935047961^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537501927 1000000000 5503935047961 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5296712187/10000000000 : ℝ), (-2107848721/10000000000 : ℝ), (537501927/1000000000 : ℝ)] ![(43185909455993/100000000000000 : ℝ), (12782610148453/100000000000000 : ℝ), (5503935047961/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5296712187/10000000000 : ℝ)|^8423 ≤ (43185909455993/100000000000000 : ℝ)^6375
        have hw : |(5296712187/10000000000 : ℝ)|=(5296712187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2107848721/10000000000 : ℝ)|^8423 ≤ (12782610148453/100000000000000 : ℝ)^6375
        have hw : |(-2107848721/10000000000 : ℝ)|=(2107848721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(537501927/1000000000 : ℝ)|^8423 ≤ (5503935047961/12500000000000 : ℝ)^6375
        have hw : |(537501927/1000000000 : ℝ)|=(537501927/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_2 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2648356069/5000000000 : ℝ)*x 0 + (1343754853/2500000000 : ℝ)*x 1 + (-421569719/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2648356069/5000000000 : ℝ)^8423 ≤ (43185908928133/100000000000000 : ℝ)^6375 := by
    have hnat : (2648356069 : ℕ)^8423*100000000000000^6375 ≤ 43185908928133^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2648356069 5000000000 43185908928133 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1343754853/2500000000 : ℝ)^8423 ≤ (44031481920633/100000000000000 : ℝ)^6375 := by
    have hnat : (1343754853 : ℕ)^8423*100000000000000^6375 ≤ 44031481920633^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343754853 2500000000 44031481920633 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (421569719/2000000000 : ℝ)^8423 ≤ (12782609138881/100000000000000 : ℝ)^6375 := by
    have hnat : (421569719 : ℕ)^8423*100000000000000^6375 ≤ 12782609138881^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421569719 2000000000 12782609138881 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2648356069/5000000000 : ℝ), (1343754853/2500000000 : ℝ), (-421569719/2000000000 : ℝ)] ![(43185908928133/100000000000000 : ℝ), (44031481920633/100000000000000 : ℝ), (12782609138881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2648356069/5000000000 : ℝ)|^8423 ≤ (43185908928133/100000000000000 : ℝ)^6375
        have hw : |(2648356069/5000000000 : ℝ)|=(2648356069/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1343754853/2500000000 : ℝ)|^8423 ≤ (44031481920633/100000000000000 : ℝ)^6375
        have hw : |(1343754853/2500000000 : ℝ)|=(1343754853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-421569719/2000000000 : ℝ)|^8423 ≤ (12782609138881/100000000000000 : ℝ)^6375
        have hw : |(-421569719/2000000000 : ℝ)|=(421569719/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_3 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4459061073/10000000000 : ℝ)*x 0 + (4301154567/10000000000 : ℝ)*x 1 + (4301154163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4459061073/10000000000 : ℝ)^8423 ≤ (34400214464493/100000000000000 : ℝ)^6375 := by
    have hnat : (4459061073 : ℕ)^8423*100000000000000^6375 ≤ 34400214464493^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4459061073 10000000000 34400214464493 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4301154567/10000000000 : ℝ)^8423 ≤ (32799894799381/100000000000000 : ℝ)^6375 := by
    have hnat : (4301154567 : ℕ)^8423*100000000000000^6375 ≤ 32799894799381^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301154567 10000000000 32799894799381 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4301154163/10000000000 : ℝ)^8423 ≤ (3279989072881/10000000000000 : ℝ)^6375 := by
    have hnat : (4301154163 : ℕ)^8423*10000000000000^6375 ≤ 3279989072881^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301154163 10000000000 3279989072881 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4459061073/10000000000 : ℝ), (4301154567/10000000000 : ℝ), (4301154163/10000000000 : ℝ)] ![(34400214464493/100000000000000 : ℝ), (32799894799381/100000000000000 : ℝ), (3279989072881/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4459061073/10000000000 : ℝ)|^8423 ≤ (34400214464493/100000000000000 : ℝ)^6375
        have hw : |(4459061073/10000000000 : ℝ)|=(4459061073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4301154567/10000000000 : ℝ)|^8423 ≤ (32799894799381/100000000000000 : ℝ)^6375
        have hw : |(4301154567/10000000000 : ℝ)|=(4301154567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4301154163/10000000000 : ℝ)|^8423 ≤ (3279989072881/10000000000000 : ℝ)^6375
        have hw : |(4301154163/10000000000 : ℝ)|=(4301154163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_4 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-225094423/1000000000 : ℝ)*x 0 + (211286581/400000000 : ℝ)*x 1 + (5282164623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (225094423/1000000000 : ℝ)^8423 ≤ (13941475226463/100000000000000 : ℝ)^6375 := by
    have hnat : (225094423 : ℕ)^8423*100000000000000^6375 ≤ 13941475226463^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      225094423 1000000000 13941475226463 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (211286581/400000000 : ℝ)^8423 ≤ (4302926185463/10000000000000 : ℝ)^6375 := by
    have hnat : (211286581 : ℕ)^8423*10000000000000^6375 ≤ 4302926185463^6375*400000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211286581 400000000 4302926185463 10000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282164623/10000000000 : ℝ)^8423 ≤ (5378657863677/12500000000000 : ℝ)^6375 := by
    have hnat : (5282164623 : ℕ)^8423*12500000000000^6375 ≤ 5378657863677^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282164623 10000000000 5378657863677 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-225094423/1000000000 : ℝ), (211286581/400000000 : ℝ), (5282164623/10000000000 : ℝ)] ![(13941475226463/100000000000000 : ℝ), (4302926185463/10000000000000 : ℝ), (5378657863677/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-225094423/1000000000 : ℝ)|^8423 ≤ (13941475226463/100000000000000 : ℝ)^6375
        have hw : |(-225094423/1000000000 : ℝ)|=(225094423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(211286581/400000000 : ℝ)|^8423 ≤ (4302926185463/10000000000000 : ℝ)^6375
        have hw : |(211286581/400000000 : ℝ)|=(211286581/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282164623/10000000000 : ℝ)|^8423 ≤ (5378657863677/12500000000000 : ℝ)^6375
        have hw : |(5282164623/10000000000 : ℝ)|=(5282164623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_5 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1072437107/2000000000 : ℝ)*x 0 + (-1072313049/5000000000 : ℝ)*x 1 + (5282164567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072437107/2000000000 : ℝ)^8423 ≤ (8778525413517/20000000000000 : ℝ)^6375 := by
    have hnat : (1072437107 : ℕ)^8423*20000000000000^6375 ≤ 8778525413517^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072437107 2000000000 8778525413517 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1072313049/5000000000 : ℝ)^8423 ≤ (6539055304813/50000000000000 : ℝ)^6375 := by
    have hnat : (1072313049 : ℕ)^8423*50000000000000^6375 ≤ 6539055304813^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072313049 5000000000 6539055304813 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5282164567/10000000000 : ℝ)^8423 ≤ (43029262306681/100000000000000 : ℝ)^6375 := by
    have hnat : (5282164567 : ℕ)^8423*100000000000000^6375 ≤ 43029262306681^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5282164567 10000000000 43029262306681 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072437107/2000000000 : ℝ), (-1072313049/5000000000 : ℝ), (5282164567/10000000000 : ℝ)] ![(8778525413517/20000000000000 : ℝ), (6539055304813/50000000000000 : ℝ), (43029262306681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072437107/2000000000 : ℝ)|^8423 ≤ (8778525413517/20000000000000 : ℝ)^6375
        have hw : |(1072437107/2000000000 : ℝ)|=(1072437107/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1072313049/5000000000 : ℝ)|^8423 ≤ (6539055304813/50000000000000 : ℝ)^6375
        have hw : |(-1072313049/5000000000 : ℝ)|=(1072313049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5282164567/10000000000 : ℝ)|^8423 ≤ (43029262306681/100000000000000 : ℝ)^6375
        have hw : |(5282164567/10000000000 : ℝ)|=(5282164567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_6 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5362185477/10000000000 : ℝ)*x 0 + (2641082303/5000000000 : ℝ)*x 1 + (-536156531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5362185477/10000000000 : ℝ)^8423 ≤ (43892626440301/100000000000000 : ℝ)^6375 := by
    have hnat : (5362185477 : ℕ)^8423*100000000000000^6375 ≤ 43892626440301^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5362185477 10000000000 43892626440301 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2641082303/5000000000 : ℝ)^8423 ≤ (43029262726443/100000000000000 : ℝ)^6375 := by
    have hnat : (2641082303 : ℕ)^8423*100000000000000^6375 ≤ 43029262726443^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2641082303 5000000000 43029262726443 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (536156531/2500000000 : ℝ)^8423 ≤ (1634763852389/12500000000000 : ℝ)^6375 := by
    have hnat : (536156531 : ℕ)^8423*12500000000000^6375 ≤ 1634763852389^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536156531 2500000000 1634763852389 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5362185477/10000000000 : ℝ), (2641082303/5000000000 : ℝ), (-536156531/2500000000 : ℝ)] ![(43892626440301/100000000000000 : ℝ), (43029262726443/100000000000000 : ℝ), (1634763852389/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5362185477/10000000000 : ℝ)|^8423 ≤ (43892626440301/100000000000000 : ℝ)^6375
        have hw : |(5362185477/10000000000 : ℝ)|=(5362185477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2641082303/5000000000 : ℝ)|^8423 ≤ (43029262726443/100000000000000 : ℝ)^6375
        have hw : |(2641082303/5000000000 : ℝ)|=(2641082303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-536156531/2500000000 : ℝ)|^8423 ≤ (1634763852389/12500000000000 : ℝ)^6375
        have hw : |(-536156531/2500000000 : ℝ)|=(536156531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_7 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2122694517/5000000000 : ℝ)*x 0 + (4407970169/10000000000 : ℝ)*x 1 + (4407970239/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2122694517/5000000000 : ℝ)^8423 ≤ (32239193189337/100000000000000 : ℝ)^6375 := by
    have hnat : (2122694517 : ℕ)^8423*100000000000000^6375 ≤ 32239193189337^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2122694517 5000000000 32239193189337 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4407970169/10000000000 : ℝ)^8423 ≤ (33880403044899/100000000000000 : ℝ)^6375 := by
    have hnat : (4407970169 : ℕ)^8423*100000000000000^6375 ≤ 33880403044899^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4407970169 10000000000 33880403044899 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4407970239/10000000000 : ℝ)^8423 ≤ (132345327171/390625000000 : ℝ)^6375 := by
    have hnat : (4407970239 : ℕ)^8423*390625000000^6375 ≤ 132345327171^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4407970239 10000000000 132345327171 390625000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2122694517/5000000000 : ℝ), (4407970169/10000000000 : ℝ), (4407970239/10000000000 : ℝ)] ![(32239193189337/100000000000000 : ℝ), (33880403044899/100000000000000 : ℝ), (132345327171/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2122694517/5000000000 : ℝ)|^8423 ≤ (32239193189337/100000000000000 : ℝ)^6375
        have hw : |(2122694517/5000000000 : ℝ)|=(2122694517/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4407970169/10000000000 : ℝ)|^8423 ≤ (33880403044899/100000000000000 : ℝ)^6375
        have hw : |(4407970169/10000000000 : ℝ)|=(4407970169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4407970239/10000000000 : ℝ)|^8423 ≤ (132345327171/390625000000 : ℝ)^6375
        have hw : |(4407970239/10000000000 : ℝ)|=(4407970239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_8 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1099337101/5000000000 : ℝ)*x 0 + (5218849869/10000000000 : ℝ)*x 1 + (673078959/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099337101/5000000000 : ℝ)^8423 ≤ (13515335747359/100000000000000 : ℝ)^6375 := by
    have hnat : (1099337101 : ℕ)^8423*100000000000000^6375 ≤ 13515335747359^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099337101 5000000000 13515335747359 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218849869/10000000000 : ℝ)^8423 ≤ (21174556812443/50000000000000 : ℝ)^6375 := by
    have hnat : (5218849869 : ℕ)^8423*50000000000000^6375 ≤ 21174556812443^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218849869 10000000000 21174556812443 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673078959/1250000000 : ℝ)^8423 ≤ (8827110121299/20000000000000 : ℝ)^6375 := by
    have hnat : (673078959 : ℕ)^8423*20000000000000^6375 ≤ 8827110121299^6375*1250000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673078959 1250000000 8827110121299 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1099337101/5000000000 : ℝ), (5218849869/10000000000 : ℝ), (673078959/1250000000 : ℝ)] ![(13515335747359/100000000000000 : ℝ), (21174556812443/50000000000000 : ℝ), (8827110121299/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1099337101/5000000000 : ℝ)|^8423 ≤ (13515335747359/100000000000000 : ℝ)^6375
        have hw : |(-1099337101/5000000000 : ℝ)|=(1099337101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218849869/10000000000 : ℝ)|^8423 ≤ (21174556812443/50000000000000 : ℝ)^6375
        have hw : |(5218849869/10000000000 : ℝ)|=(5218849869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673078959/1250000000 : ℝ)|^8423 ≤ (8827110121299/20000000000000 : ℝ)^6375
        have hw : |(673078959/1250000000 : ℝ)|=(673078959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_9 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1322482843/2500000000 : ℝ)*x 0 + (-105198697/500000000 : ℝ)*x 1 + (5384631623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1322482843/2500000000 : ℝ)^8423 ≤ (8622575435119/20000000000000 : ℝ)^6375 := by
    have hnat : (1322482843 : ℕ)^8423*20000000000000^6375 ≤ 8622575435119^6375*2500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1322482843 2500000000 8622575435119 20000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (105198697/500000000 : ℝ)^8423 ≤ (12751572731583/100000000000000 : ℝ)^6375 := by
    have hnat : (105198697 : ℕ)^8423*100000000000000^6375 ≤ 12751572731583^6375*500000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105198697 500000000 12751572731583 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5384631623/10000000000 : ℝ)^8423 ≤ (44135550075837/100000000000000 : ℝ)^6375 := by
    have hnat : (5384631623 : ℕ)^8423*100000000000000^6375 ≤ 44135550075837^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5384631623 10000000000 44135550075837 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1322482843/2500000000 : ℝ), (-105198697/500000000 : ℝ), (5384631623/10000000000 : ℝ)] ![(8622575435119/20000000000000 : ℝ), (12751572731583/100000000000000 : ℝ), (44135550075837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1322482843/2500000000 : ℝ)|^8423 ≤ (8622575435119/20000000000000 : ℝ)^6375
        have hw : |(1322482843/2500000000 : ℝ)|=(1322482843/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-105198697/500000000 : ℝ)|^8423 ≤ (12751572731583/100000000000000 : ℝ)^6375
        have hw : |(-105198697/500000000 : ℝ)|=(105198697/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5384631623/10000000000 : ℝ)|^8423 ≤ (44135550075837/100000000000000 : ℝ)^6375
        have hw : |(5384631623/10000000000 : ℝ)|=(5384631623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_10 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5289931367/10000000000 : ℝ)*x 0 + (1076926339/2000000000 : ℝ)*x 1 + (-42079477/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289931367/10000000000 : ℝ)^8423 ≤ (21556438560877/50000000000000 : ℝ)^6375 := by
    have hnat : (5289931367 : ℕ)^8423*50000000000000^6375 ≤ 21556438560877^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289931367 10000000000 21556438560877 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076926339/2000000000 : ℝ)^8423 ≤ (2206777542779/5000000000000 : ℝ)^6375 := by
    have hnat : (1076926339 : ℕ)^8423*5000000000000^6375 ≤ 2206777542779^6375*2000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076926339 2000000000 2206777542779 5000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42079477/200000000 : ℝ)^8423 ≤ (6375786005443/50000000000000 : ℝ)^6375 := by
    have hnat : (42079477 : ℕ)^8423*50000000000000^6375 ≤ 6375786005443^6375*200000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42079477 200000000 6375786005443 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289931367/10000000000 : ℝ), (1076926339/2000000000 : ℝ), (-42079477/200000000 : ℝ)] ![(21556438560877/50000000000000 : ℝ), (2206777542779/5000000000000 : ℝ), (6375786005443/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289931367/10000000000 : ℝ)|^8423 ≤ (21556438560877/50000000000000 : ℝ)^6375
        have hw : |(5289931367/10000000000 : ℝ)|=(5289931367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076926339/2000000000 : ℝ)|^8423 ≤ (2206777542779/5000000000000 : ℝ)^6375
        have hw : |(1076926339/2000000000 : ℝ)|=(1076926339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42079477/200000000 : ℝ)|^8423 ≤ (6375786005443/50000000000000 : ℝ)^6375
        have hw : |(-42079477/200000000 : ℝ)|=(42079477/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_11 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4480907493/10000000000 : ℝ)*x 0 + (4290090613/10000000000 : ℝ)*x 1 + (2145045331/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4480907493/10000000000 : ℝ)^8423 ≤ (34623071260883/100000000000000 : ℝ)^6375 := by
    have hnat : (4480907493 : ℕ)^8423*100000000000000^6375 ≤ 34623071260883^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480907493 10000000000 34623071260883 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4290090613/10000000000 : ℝ)^8423 ≤ (4086058014683/12500000000000 : ℝ)^6375 := by
    have hnat : (4290090613 : ℕ)^8423*12500000000000^6375 ≤ 4086058014683^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4290090613 10000000000 4086058014683 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145045331/5000000000 : ℝ)^8423 ≤ (32688464610763/100000000000000 : ℝ)^6375 := by
    have hnat : (2145045331 : ℕ)^8423*100000000000000^6375 ≤ 32688464610763^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145045331 5000000000 32688464610763 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4480907493/10000000000 : ℝ), (4290090613/10000000000 : ℝ), (2145045331/5000000000 : ℝ)] ![(34623071260883/100000000000000 : ℝ), (4086058014683/12500000000000 : ℝ), (32688464610763/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4480907493/10000000000 : ℝ)|^8423 ≤ (34623071260883/100000000000000 : ℝ)^6375
        have hw : |(4480907493/10000000000 : ℝ)|=(4480907493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4290090613/10000000000 : ℝ)|^8423 ≤ (4086058014683/12500000000000 : ℝ)^6375
        have hw : |(4290090613/10000000000 : ℝ)|=(4290090613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2145045331/5000000000 : ℝ)|^8423 ≤ (32688464610763/100000000000000 : ℝ)^6375
        have hw : |(2145045331/5000000000 : ℝ)|=(2145045331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_12 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2053980167/10000000000 : ℝ)*x 0 + (5437118081/10000000000 : ℝ)*x 1 + (5274089799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2053980167/10000000000 : ℝ)^8423 ≤ (3088192961361/25000000000000 : ℝ)^6375 := by
    have hnat : (2053980167 : ℕ)^8423*25000000000000^6375 ≤ 3088192961361^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2053980167 10000000000 3088192961361 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437118081/10000000000 : ℝ)^8423 ≤ (11176213566247/25000000000000 : ℝ)^6375 := by
    have hnat : (5437118081 : ℕ)^8423*25000000000000^6375 ≤ 11176213566247^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437118081 10000000000 11176213566247 25000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274089799/10000000000 : ℝ)^8423 ≤ (42942373877211/100000000000000 : ℝ)^6375 := by
    have hnat : (5274089799 : ℕ)^8423*100000000000000^6375 ≤ 42942373877211^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274089799 10000000000 42942373877211 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2053980167/10000000000 : ℝ), (5437118081/10000000000 : ℝ), (5274089799/10000000000 : ℝ)] ![(3088192961361/25000000000000 : ℝ), (11176213566247/25000000000000 : ℝ), (42942373877211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2053980167/10000000000 : ℝ)|^8423 ≤ (3088192961361/25000000000000 : ℝ)^6375
        have hw : |(-2053980167/10000000000 : ℝ)|=(2053980167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437118081/10000000000 : ℝ)|^8423 ≤ (11176213566247/25000000000000 : ℝ)^6375
        have hw : |(5437118081/10000000000 : ℝ)|=(5437118081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274089799/10000000000 : ℝ)|^8423 ≤ (42942373877211/100000000000000 : ℝ)^6375
        have hw : |(5274089799/10000000000 : ℝ)|=(5274089799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_13 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5367876329/10000000000 : ℝ)*x 0 + (-2147768309/10000000000 : ℝ)*x 1 + (5274090493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5367876329/10000000000 : ℝ)^8423 ≤ (2197709244337/5000000000000 : ℝ)^6375 := by
    have hnat : (5367876329 : ℕ)^8423*5000000000000^6375 ≤ 2197709244337^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5367876329 10000000000 2197709244337 5000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2147768309/10000000000 : ℝ)^8423 ≤ (102370576161/781250000000 : ℝ)^6375 := by
    have hnat : (2147768309 : ℕ)^8423*781250000000^6375 ≤ 102370576161^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147768309 10000000000 102370576161 781250000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5274090493/10000000000 : ℝ)^8423 ≤ (42942381343153/100000000000000 : ℝ)^6375 := by
    have hnat : (5274090493 : ℕ)^8423*100000000000000^6375 ≤ 42942381343153^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274090493 10000000000 42942381343153 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5367876329/10000000000 : ℝ), (-2147768309/10000000000 : ℝ), (5274090493/10000000000 : ℝ)] ![(2197709244337/5000000000000 : ℝ), (102370576161/781250000000 : ℝ), (42942381343153/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5367876329/10000000000 : ℝ)|^8423 ≤ (2197709244337/5000000000000 : ℝ)^6375
        have hw : |(5367876329/10000000000 : ℝ)|=(5367876329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2147768309/10000000000 : ℝ)|^8423 ≤ (102370576161/781250000000 : ℝ)^6375
        have hw : |(-2147768309/10000000000 : ℝ)|=(2147768309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5274090493/10000000000 : ℝ)|^8423 ≤ (42942381343153/100000000000000 : ℝ)^6375
        have hw : |(5274090493/10000000000 : ℝ)|=(5274090493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_14 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (536787689/1000000000 : ℝ)*x 0 + (5274090101/10000000000 : ℝ)*x 1 + (-26847101/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (536787689/1000000000 : ℝ)^8423 ≤ (68678423369/156250000000 : ℝ)^6375 := by
    have hnat : (536787689 : ℕ)^8423*156250000000^6375 ≤ 68678423369^6375*1000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      536787689 1000000000 68678423369 156250000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5274090101/10000000000 : ℝ)^8423 ≤ (134194928519/312500000000 : ℝ)^6375 := by
    have hnat : (5274090101 : ℕ)^8423*312500000000^6375 ≤ 134194928519^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5274090101 10000000000 134194928519 312500000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (26847101/125000000 : ℝ)^8423 ≤ (13103431902659/100000000000000 : ℝ)^6375 := by
    have hnat : (26847101 : ℕ)^8423*100000000000000^6375 ≤ 13103431902659^6375*125000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26847101 125000000 13103431902659 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(536787689/1000000000 : ℝ), (5274090101/10000000000 : ℝ), (-26847101/125000000 : ℝ)] ![(68678423369/156250000000 : ℝ), (134194928519/312500000000 : ℝ), (13103431902659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(536787689/1000000000 : ℝ)|^8423 ≤ (68678423369/156250000000 : ℝ)^6375
        have hw : |(536787689/1000000000 : ℝ)|=(536787689/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5274090101/10000000000 : ℝ)|^8423 ≤ (134194928519/312500000000 : ℝ)^6375
        have hw : |(5274090101/10000000000 : ℝ)|=(5274090101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-26847101/125000000 : ℝ)|^8423 ≤ (13103431902659/100000000000000 : ℝ)^6375
        have hw : |(-26847101/125000000 : ℝ)|=(26847101/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1230_box_15 (p : ℝ) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4226576819/10000000000 : ℝ)*x 0 + (4417253813/10000000000 : ℝ)*x 1 + (2208626767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4226576819/10000000000 : ℝ)^8423 ≤ (4006321869341/12500000000000 : ℝ)^6375 := by
    have hnat : (4226576819 : ℕ)^8423*12500000000000^6375 ≤ 4006321869341^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226576819 10000000000 4006321869341 12500000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4417253813/10000000000 : ℝ)^8423 ≤ (33974713933623/100000000000000 : ℝ)^6375 := by
    have hnat : (4417253813 : ℕ)^8423*100000000000000^6375 ≤ 33974713933623^6375*10000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4417253813 10000000000 33974713933623 100000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208626767/5000000000 : ℝ)^8423 ≤ (16987355549177/50000000000000 : ℝ)^6375 := by
    have hnat : (2208626767 : ℕ)^8423*50000000000000^6375 ≤ 16987355549177^6375*5000000000^8423 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208626767 5000000000 16987355549177 50000000000000 8423 6375 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8423/2048 : ℝ)) 8423 6375 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4226576819/10000000000 : ℝ), (4417253813/10000000000 : ℝ), (2208626767/5000000000 : ℝ)] ![(4006321869341/12500000000000 : ℝ), (33974713933623/100000000000000 : ℝ), (16987355549177/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4226576819/10000000000 : ℝ)|^8423 ≤ (4006321869341/12500000000000 : ℝ)^6375
        have hw : |(4226576819/10000000000 : ℝ)|=(4226576819/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4417253813/10000000000 : ℝ)|^8423 ≤ (33974713933623/100000000000000 : ℝ)^6375
        have hw : |(4417253813/10000000000 : ℝ)|=(4417253813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2208626767/5000000000 : ℝ)|^8423 ≤ (16987355549177/50000000000000 : ℝ)^6375
        have hw : |(2208626767/5000000000 : ℝ)|=(2208626767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1230_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(15561/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7421/12500 : ℝ) ∧ (80073/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (83319/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2293/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2293/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2293/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14097/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2293/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2293/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14097/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2293/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2293/20000 : ℝ) ^ (4211/1024 : ℝ) ≤ (2709502334757541/20000000000000000000 : ℝ) := by
    have hpowers : (2293/20000 : ℝ)^4211 ≤ (2709502334757541/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2293 : ℕ)^4211*20000000000000000000^1024 ≤ 2709502334757541^1024*20000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2293 20000 2709502334757541 20000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2293/20000 : ℝ)) (X := (2709502334757541/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14097/100000 : ℝ) ^ (4211/1024 : ℝ) ≤ (31692006686448859/100000000000000000000 : ℝ) := by
    have hpowers : (14097/100000 : ℝ)^4211 ≤ (31692006686448859/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14097 : ℕ)^4211*100000000000000000000^1024 ≤ 31692006686448859^1024*100000^4211 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14097 100000 31692006686448859 100000000000000000000 4211 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14097/100000 : ℝ)) (X := (31692006686448859/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002709502334757541/10000000000000000000 : ℝ) ≤ (10000658809299403/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (10002709502334757541/10000000000000000000 : ℝ)^1024 ≤ (10000658809299403/10000000000000000 : ℝ)^4211 := by
      have hnat : (10002709502334757541 : ℕ)^1024*10000000000000000^4211 ≤ 10000658809299403^4211*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002709502334757541 10000000000000000000 10000658809299403 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000658809299403/10000000000000000 : ℝ)) (X := (10002709502334757541/10000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011309879590059141/25000000000000000000 : ℝ) ≤ (2500274978261469/2500000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (25011309879590059141/25000000000000000000 : ℝ)^1024 ≤ (2500274978261469/2500000000000000 : ℝ)^4211 := by
      have hnat : (25011309879590059141 : ℕ)^1024*2500000000000000^4211 ≤ 2500274978261469^4211*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011309879590059141 25000000000000000000 2500274978261469 2500000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500274978261469/2500000000000000 : ℝ)) (X := (25011309879590059141/25000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031692006686448859/50000000000000000000 : ℝ) ≤ (10001541016792349/10000000000000000 : ℝ) ^ (4211/1024 : ℝ) := by
    have hpowers : (50031692006686448859/50000000000000000000 : ℝ)^1024 ≤ (10001541016792349/10000000000000000 : ℝ)^4211 := by
      have hnat : (50031692006686448859 : ℕ)^1024*10000000000000000^4211 ≤ 10001541016792349^4211*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031692006686448859 50000000000000000000 10001541016792349 10000000000000000 1024 4211 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001541016792349/10000000000000000 : ℝ)) (X := (50031692006686448859/50000000000000000000 : ℝ)) (by norm_num) 4211 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2709502334757541/20000000000000000000 : ℝ) ≤ ((13155809738584701403/13160000000000000000 : ℝ)+2*(441103746473/263200000000000 : ℝ)*(2293/20000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (13155809738584701403/13160000000000000000 : ℝ)+2*(441103746473/263200000000000 : ℝ)*(2293/20000 : ℝ)=(10000658809299403/10000000000000000 : ℝ) by norm_num, show 1+2*(2709502334757541/20000000000000000000 : ℝ)=(10002709502334757541/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31692006686448859/100000000000000000000 : ℝ)+(2709502334757541/20000000000000000000 : ℝ) ≤ ((13155809738584701403/13160000000000000000 : ℝ)+(441103746473/263200000000000 : ℝ)*((14097/100000 : ℝ)+(2293/20000 : ℝ)))^(4211/1024 : ℝ) := by
    rw [show (13155809738584701403/13160000000000000000 : ℝ)+(441103746473/263200000000000 : ℝ)*((14097/100000 : ℝ)+(2293/20000 : ℝ))=(2500274978261469/2500000000000000 : ℝ) by norm_num, show 1+(31692006686448859/100000000000000000000 : ℝ)+(2709502334757541/20000000000000000000 : ℝ)=(25011309879590059141/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31692006686448859/100000000000000000000 : ℝ) ≤ ((13155809738584701403/13160000000000000000 : ℝ)+2*(441103746473/263200000000000 : ℝ)*(14097/100000 : ℝ))^(4211/1024 : ℝ) := by
    rw [show (13155809738584701403/13160000000000000000 : ℝ)+2*(441103746473/263200000000000 : ℝ)*(14097/100000 : ℝ)=(10001541016792349/10000000000000000 : ℝ) by norm_num, show 1+2*(31692006686448859/100000000000000000000 : ℝ)=(50031692006686448859/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13155809738584701403/13160000000000000000 : ℝ)*(X 1 0+X 2 0)+(441103746473/263200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (2293/20000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (13155809738584701403/13160000000000000000 : ℝ)) (alpha := (441103746473/263200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13155809738584701403/13160000000000000000 : ℝ)*(X 0 1+X 2 1)+(441103746473/263200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (2293/20000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (13155809738584701403/13160000000000000000 : ℝ)) (alpha := (441103746473/263200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13155809738584701403/13160000000000000000 : ℝ)*(X 0 2+X 1 2)+(441103746473/263200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4211/1024 : ℝ)) (lo := (2293/20000 : ℝ)) (hi := (14097/100000 : ℝ)) (c := (13155809738584701403/13160000000000000000 : ℝ)) (alpha := (441103746473/263200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2001443631/10000000000 : ℝ)*X 0 0+(215000781/400000000 : ℝ)*X 0 1+(2687509669/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5296712187/10000000000 : ℝ)*X 1 0+(-2107848721/10000000000 : ℝ)*X 1 1+(537501927/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2648356069/5000000000 : ℝ)*X 2 0+(1343754853/2500000000 : ℝ)*X 2 1+(-421569719/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4459061073/10000000000 : ℝ)*X 0 0+(4301154567/10000000000 : ℝ)*X 0 1+(4301154163/10000000000 : ℝ)*X 0 2+(4459061073/10000000000 : ℝ)*X 1 0+(4301154567/10000000000 : ℝ)*X 1 1+(4301154163/10000000000 : ℝ)*X 1 2+(4459061073/10000000000 : ℝ)*X 2 0+(4301154567/10000000000 : ℝ)*X 2 1+(4301154163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-225094423/1000000000 : ℝ)*X 0 0+(211286581/400000000 : ℝ)*X 0 1+(5282164623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1072437107/2000000000 : ℝ)*X 1 0+(-1072313049/5000000000 : ℝ)*X 1 1+(5282164567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5362185477/10000000000 : ℝ)*X 2 0+(2641082303/5000000000 : ℝ)*X 2 1+(-536156531/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2122694517/5000000000 : ℝ)*X 0 0+(4407970169/10000000000 : ℝ)*X 0 1+(4407970239/10000000000 : ℝ)*X 0 2+(2122694517/5000000000 : ℝ)*X 1 0+(4407970169/10000000000 : ℝ)*X 1 1+(4407970239/10000000000 : ℝ)*X 1 2+(2122694517/5000000000 : ℝ)*X 2 0+(4407970169/10000000000 : ℝ)*X 2 1+(4407970239/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1099337101/5000000000 : ℝ)*X 0 0+(5218849869/10000000000 : ℝ)*X 0 1+(673078959/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1322482843/2500000000 : ℝ)*X 1 0+(-105198697/500000000 : ℝ)*X 1 1+(5384631623/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5289931367/10000000000 : ℝ)*X 2 0+(1076926339/2000000000 : ℝ)*X 2 1+(-42079477/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4480907493/10000000000 : ℝ)*X 0 0+(4290090613/10000000000 : ℝ)*X 0 1+(2145045331/5000000000 : ℝ)*X 0 2+(4480907493/10000000000 : ℝ)*X 1 0+(4290090613/10000000000 : ℝ)*X 1 1+(2145045331/5000000000 : ℝ)*X 1 2+(4480907493/10000000000 : ℝ)*X 2 0+(4290090613/10000000000 : ℝ)*X 2 1+(2145045331/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-2053980167/10000000000 : ℝ)*X 0 0+(5437118081/10000000000 : ℝ)*X 0 1+(5274089799/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5367876329/10000000000 : ℝ)*X 1 0+(-2147768309/10000000000 : ℝ)*X 1 1+(5274090493/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((536787689/1000000000 : ℝ)*X 2 0+(5274090101/10000000000 : ℝ)*X 2 1+(-26847101/125000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4226576819/10000000000 : ℝ)*X 0 0+(4417253813/10000000000 : ℝ)*X 0 1+(2208626767/5000000000 : ℝ)*X 0 2+(4226576819/10000000000 : ℝ)*X 1 0+(4417253813/10000000000 : ℝ)*X 1 1+(2208626767/5000000000 : ℝ)*X 1 2+(4226576819/10000000000 : ℝ)*X 2 0+(4417253813/10000000000 : ℝ)*X 2 1+(2208626767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1230_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-15561/25000 : ℝ) ≤ (-204775537505366920250483172402609/329000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (540651/3125000000000 : ℝ)*(upper0) + (13039263/20000000000000 : ℝ)*(upper1) + (31211461/50000000000000 : ℝ)*(upper2) + (4392947/12500000000000 : ℝ)*(upper3) + (13144429/12500000000000 : ℝ)*(upper5) + (1996798630597601/50000000000000 : ℝ)*(major0) + (1996798630597601/50000000000000 : ℝ)*(major1) + (1996798630597601/50000000000000 : ℝ)*(major2) + (4780093057/100000000000000 : ℝ)*(sp2) + (1568382561/25000000000000 : ℝ)*(sp3) + (5366561309902583/100000000000000 : ℝ)*(sp4) + (5366561309902583/100000000000000 : ℝ)*(sp5) + (2683278264904763/50000000000000 : ℝ)*(sp6) + (2641374207195117/100000000000000 : ℝ)*(sp7) + (2641380480725361/100000000000000 : ℝ)*(f.failure) + (5366561309902583/100000000000000 : ℝ)*(f.sum) + (579389954727/6580000000000000000000000000 : ℝ)*base66 + (1157075442804112029/94000000000000000000000000000000 : ℝ)*base67 + (2274914724492112029/94000000000000000000000000000000 : ℝ)*base69 + (628323703898112029/94000000000000000000000000000000 : ℝ)*base71 + (13078003143187/6580000000000000000000000000 : ℝ)*base74 + (6350241921404112029/94000000000000000000000000000000 : ℝ)*base75 + (391871725223887971/94000000000000000000000000000000 : ℝ)*base78 + (6322672926705887971/94000000000000000000000000000000 : ℝ)*base80 + (4283882501809593/6580000000000000000000000000 : ℝ)*base81 + (45948757/10000000000000000000000 : ℝ)*base90 + (45948757/10000000000000000000000 : ℝ)*base92 + (45948757/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (7421/12500 : ℝ) ≤ (97664142927598994210412452073417/164500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2515091/2500000000000 : ℝ)*(upper3) + (51690107/50000000000000 : ℝ)*(upper4) + (1359743/10000000000000 : ℝ)*(lower5) + (1014798259615687/25000000000000 : ℝ)*(major0) + (1014798259615687/25000000000000 : ℝ)*(major1) + (1014798259615687/25000000000000 : ℝ)*(major2) + (5413824508437753/100000000000000 : ℝ)*(sp0) + (5413681548983171/100000000000000 : ℝ)*(sp1) + (2706912876209957/50000000000000 : ℝ)*(sp2) + (671191019824791/25000000000000 : ℝ)*(sp3) + (889258189/20000000000000 : ℝ)*(sp6) + (849515729/50000000000000 : ℝ)*(sp7) + (2845136553/50000000000000 : ℝ)*(sp8) + (18581215961/12500000000000 : ℝ)*(sp9) + (1342382889165311/50000000000000 : ℝ)*(f.failure) + (5413830198710859/100000000000000 : ℝ)*(f.sum) + (16909726221859/3290000000000000000000000000 : ℝ)*base66 + (58635237459105877/47000000000000000000000000000000 : ℝ)*base68 + (59564432676105877/47000000000000000000000000000000 : ℝ)*base70 + (24131827024894123/47000000000000000000000000000000 : ℝ)*base71 + (7984152905041/3290000000000000000000000000 : ℝ)*base73 + (94007971067894123/47000000000000000000000000000000 : ℝ)*base75 + (125158844776894123/47000000000000000000000000000000 : ℝ)*base77 + (38268760987894123/47000000000000000000000000000000 : ℝ)*base79 + (3838434416591/3290000000000000000000000000 : ℝ)*base81 + (66093093/5000000000000000000000 : ℝ)*base89 + (66093093/5000000000000000000000 : ℝ)*base91 + (66093093/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (80073/100000 : ℝ) ≤ (75271375474949826989333042358123/94000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7803483/12500000000000 : ℝ)*(lower3) + (1499307/6250000000000 : ℝ)*(upper4) + (111297/1250000000000 : ℝ)*(lower5) + (4526175727624257/100000000000000 : ℝ)*(major0) + (4526175727624257/100000000000000 : ℝ)*(major1) + (4526175727624257/100000000000000 : ℝ)*(major2) + (1528521747/100000000000000 : ℝ)*(sp0) + (4465632069/12500000000000 : ℝ)*(sp1) + (37775517367/50000000000000 : ℝ)*(sp2) + (33677022427/100000000000000 : ℝ)*(sp3) + (1206405607437241/20000000000000 : ℝ)*(sp8) + (30159969203257/500000000000 : ℝ)*(sp9) + (3015977007336609/50000000000000 : ℝ)*(sp10) + (187099764712459/6250000000000 : ℝ)*(sp11) + (748407478105443/25000000000000 : ℝ)*(f.failure) + (377001847856747/6250000000000 : ℝ)*(f.sum) + (3001629189743/1880000000000000000000000000 : ℝ)*base65 + (4153841640655254653/188000000000000000000000000000000 : ℝ)*base67 + (2308966005143254653/188000000000000000000000000000000 : ℝ)*base69 + (2528640017287254653/188000000000000000000000000000000 : ℝ)*base71 + (22432925682903/1880000000000000000000000000 : ℝ)*base73 + (2625567218271254653/188000000000000000000000000000000 : ℝ)*base75 + (2872283285775254653/188000000000000000000000000000000 : ℝ)*base77 + (2453995724231254653/188000000000000000000000000000000 : ℝ)*base79 + (8892328500103/1880000000000000000000000000 : ℝ)*base81 + (8136591/2500000000000000000000 : ℝ)*base90 + (8136591/2500000000000000000000 : ℝ)*base92 + (8136591/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-83319/100000 : ℝ) ≤ (-548225189465691772470724267324797/658000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (29713549/100000000000000 : ℝ)*(upper1) + (61710069/25000000000000 : ℝ)*(lower2) + (436553899/100000000000000 : ℝ)*(upper3) + (288133919/50000000000000 : ℝ)*(upper5) + (4561599305061711/100000000000000 : ℝ)*(major0) + (4561599305061711/100000000000000 : ℝ)*(major1) + (4561599305061711/100000000000000 : ℝ)*(major2) + (23348027263/100000000000000 : ℝ)*(sp4) + (170910403553/100000000000000 : ℝ)*(sp6) + (59986592811/20000000000000 : ℝ)*(sp7) + (766736044954263/12500000000000 : ℝ)*(sp12) + (766738963457671/12500000000000 : ℝ)*(sp13) + (1226748159451563/20000000000000 : ℝ)*(sp14) + (377094908607877/12500000000000 : ℝ)*(sp15) + (11785387507137/390625000000 : ℝ)*(f.failure) + (766738963457671/12500000000000 : ℝ)*(f.sum) + (31380654508743/13160000000000000000000000000 : ℝ)*base65 + (3359154900822347219/188000000000000000000000000000000 : ℝ)*base67 + (4292510072406347219/188000000000000000000000000000000 : ℝ)*base69 + (3777055918950347219/188000000000000000000000000000000 : ℝ)*base71 + (11691616937743/13160000000000000000000000000 : ℝ)*base73 + (627421406354347219/188000000000000000000000000000000 : ℝ)*base75 + (885383351858347219/188000000000000000000000000000000 : ℝ)*base77 + (3337430573230347219/188000000000000000000000000000000 : ℝ)*base79 + (96943200352417/13160000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (24939/9765625000000000000 : ℝ)*base89 + (24939/9765625000000000000 : ℝ)*base91 + (24939/9765625000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1230_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14097/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15561/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(7421/12500 : ℝ) else (80073/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83319/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1230_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1230_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15561/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(7421/12500 : ℝ) else (80073/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83319/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1230_s9 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1230_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4211/1024 : ℝ) ≤ p) (hpb : p ≤ (8423/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151193563/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7049/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2293/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(15561/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(7421/12500 : ℝ) else (80073/100000 : ℝ) ≤ X j i ∧ X j i ≤ (83319/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1230_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
