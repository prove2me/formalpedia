-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1233_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:15:47.200127+00:00
-- url     : https://prove2.me/submissions/93132610-75ce-4798-bb0f-f890e51c1957

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
theorem support_rectangle_w1233_s3_0 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121190679/10000000000 : ℝ)*x 0 + (2710227213/5000000000 : ℝ)*x 1 + (5239919993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121190679/10000000000 : ℝ)^4213 ≤ (1611580162307/12500000000000 : ℝ)^3189 := by
    have hnat : (2121190679 : ℕ)^4213*12500000000000^3189 ≤ 1611580162307^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121190679 10000000000 1611580162307 12500000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2710227213/5000000000 : ℝ)^4213 ≤ (22264018536923/50000000000000 : ℝ)^3189 := by
    have hnat : (2710227213 : ℕ)^4213*50000000000000^3189 ≤ 22264018536923^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710227213 5000000000 22264018536923 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239919993/10000000000 : ℝ)^4213 ≤ (42579321623409/100000000000000 : ℝ)^3189 := by
    have hnat : (5239919993 : ℕ)^4213*100000000000000^3189 ≤ 42579321623409^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239919993 10000000000 42579321623409 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121190679/10000000000 : ℝ), (2710227213/5000000000 : ℝ), (5239919993/10000000000 : ℝ)] ![(1611580162307/12500000000000 : ℝ), (22264018536923/50000000000000 : ℝ), (42579321623409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121190679/10000000000 : ℝ)|^4213 ≤ (1611580162307/12500000000000 : ℝ)^3189
        have hw : |(-2121190679/10000000000 : ℝ)|=(2121190679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2710227213/5000000000 : ℝ)|^4213 ≤ (22264018536923/50000000000000 : ℝ)^3189
        have hw : |(2710227213/5000000000 : ℝ)|=(2710227213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239919993/10000000000 : ℝ)|^4213 ≤ (42579321623409/100000000000000 : ℝ)^3189
        have hw : |(5239919993/10000000000 : ℝ)|=(5239919993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s3_1 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337922561/2500000000 : ℝ)*x 0 + (-553325901/2500000000 : ℝ)*x 1 + (104798403/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337922561/2500000000 : ℝ)^4213 ≤ (43783289570627/100000000000000 : ℝ)^3189 := by
    have hnat : (1337922561 : ℕ)^4213*100000000000000^3189 ≤ 43783289570627^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337922561 2500000000 43783289570627 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553325901/2500000000 : ℝ)^4213 ≤ (26635521689/195312500000 : ℝ)^3189 := by
    have hnat : (553325901 : ℕ)^4213*195312500000^3189 ≤ 26635521689^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553325901 2500000000 26635521689 195312500000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104798403/200000000 : ℝ)^4213 ≤ (42579323308839/100000000000000 : ℝ)^3189 := by
    have hnat : (104798403 : ℕ)^4213*100000000000000^3189 ≤ 42579323308839^3189*200000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104798403 200000000 42579323308839 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337922561/2500000000 : ℝ), (-553325901/2500000000 : ℝ), (104798403/200000000 : ℝ)] ![(43783289570627/100000000000000 : ℝ), (26635521689/195312500000 : ℝ), (42579323308839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337922561/2500000000 : ℝ)|^4213 ≤ (43783289570627/100000000000000 : ℝ)^3189
        have hw : |(1337922561/2500000000 : ℝ)|=(1337922561/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553325901/2500000000 : ℝ)|^4213 ≤ (26635521689/195312500000 : ℝ)^3189
        have hw : |(-553325901/2500000000 : ℝ)|=(553325901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(104798403/200000000 : ℝ)|^4213 ≤ (42579323308839/100000000000000 : ℝ)^3189
        have hw : |(104798403/200000000 : ℝ)|=(104798403/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s3_2 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351690139/10000000000 : ℝ)*x 0 + (5239920561/10000000000 : ℝ)*x 1 + (-1106651601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351690139/10000000000 : ℝ)^4213 ≤ (43783288435763/100000000000000 : ℝ)^3189 := by
    have hnat : (5351690139 : ℕ)^4213*100000000000000^3189 ≤ 43783288435763^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351690139 10000000000 43783288435763 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239920561/10000000000 : ℝ)^4213 ≤ (8515865544203/20000000000000 : ℝ)^3189 := by
    have hnat : (5239920561 : ℕ)^4213*20000000000000^3189 ≤ 8515865544203^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239920561 10000000000 8515865544203 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1106651601/5000000000 : ℝ)^4213 ≤ (3409345958117/25000000000000 : ℝ)^3189 := by
    have hnat : (1106651601 : ℕ)^4213*25000000000000^3189 ≤ 3409345958117^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106651601 5000000000 3409345958117 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351690139/10000000000 : ℝ), (5239920561/10000000000 : ℝ), (-1106651601/5000000000 : ℝ)] ![(43783288435763/100000000000000 : ℝ), (8515865544203/20000000000000 : ℝ), (3409345958117/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351690139/10000000000 : ℝ)|^4213 ≤ (43783288435763/100000000000000 : ℝ)^3189
        have hw : |(5351690139/10000000000 : ℝ)|=(5351690139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239920561/10000000000 : ℝ)|^4213 ≤ (8515865544203/20000000000000 : ℝ)^3189
        have hw : |(5239920561/10000000000 : ℝ)|=(5239920561/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1106651601/5000000000 : ℝ)|^4213 ≤ (3409345958117/25000000000000 : ℝ)^3189
        have hw : |(-1106651601/5000000000 : ℝ)|=(1106651601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s3_3 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4350266189/10000000000 : ℝ)*x 0 + (417120931/1000000000 : ℝ)*x 1 + (567099821/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4350266189/10000000000 : ℝ)^4213 ≤ (33299820609029/100000000000000 : ℝ)^3189 := by
    have hnat : (4350266189 : ℕ)^4213*100000000000000^3189 ≤ 33299820609029^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4350266189 10000000000 33299820609029 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (417120931/1000000000 : ℝ)^4213 ≤ (31501168598813/100000000000000 : ℝ)^3189 := by
    have hnat : (417120931 : ℕ)^4213*100000000000000^3189 ≤ 31501168598813^3189*1000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417120931 1000000000 31501168598813 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (567099821/1250000000 : ℝ)^4213 ≤ (35199010776421/100000000000000 : ℝ)^3189 := by
    have hnat : (567099821 : ℕ)^4213*100000000000000^3189 ≤ 35199010776421^3189*1250000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      567099821 1250000000 35199010776421 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4350266189/10000000000 : ℝ), (417120931/1000000000 : ℝ), (567099821/1250000000 : ℝ)] ![(33299820609029/100000000000000 : ℝ), (31501168598813/100000000000000 : ℝ), (35199010776421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4350266189/10000000000 : ℝ)|^4213 ≤ (33299820609029/100000000000000 : ℝ)^3189
        have hw : |(4350266189/10000000000 : ℝ)|=(4350266189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(417120931/1000000000 : ℝ)|^4213 ≤ (31501168598813/100000000000000 : ℝ)^3189
        have hw : |(417120931/1000000000 : ℝ)|=(417120931/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(567099821/1250000000 : ℝ)|^4213 ≤ (35199010776421/100000000000000 : ℝ)^3189
        have hw : |(567099821/1250000000 : ℝ)|=(567099821/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s3_4 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-530301387/2500000000 : ℝ)*x 0 + (5240580181/10000000000 : ℝ)*x 1 + (5419790351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530301387/2500000000 : ℝ)^4213 ≤ (3223190173037/25000000000000 : ℝ)^3189 := by
    have hnat : (530301387 : ℕ)^4213*25000000000000^3189 ≤ 3223190173037^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530301387 2500000000 3223190173037 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240580181/10000000000 : ℝ)^4213 ≤ (42586409031379/100000000000000 : ℝ)^3189 := by
    have hnat : (5240580181 : ℕ)^4213*100000000000000^3189 ≤ 42586409031379^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240580181 10000000000 42586409031379 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419790351/10000000000 : ℝ)^4213 ≤ (44520830258721/100000000000000 : ℝ)^3189 := by
    have hnat : (5419790351 : ℕ)^4213*100000000000000^3189 ≤ 44520830258721^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419790351 10000000000 44520830258721 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-530301387/2500000000 : ℝ), (5240580181/10000000000 : ℝ), (5419790351/10000000000 : ℝ)] ![(3223190173037/25000000000000 : ℝ), (42586409031379/100000000000000 : ℝ), (44520830258721/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-530301387/2500000000 : ℝ)|^4213 ≤ (3223190173037/25000000000000 : ℝ)^3189
        have hw : |(-530301387/2500000000 : ℝ)|=(530301387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240580181/10000000000 : ℝ)|^4213 ≤ (42586409031379/100000000000000 : ℝ)^3189
        have hw : |(5240580181/10000000000 : ℝ)|=(5240580181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419790351/10000000000 : ℝ)|^4213 ≤ (44520830258721/100000000000000 : ℝ)^3189
        have hw : |(5419790351/10000000000 : ℝ)|=(5419790351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s3_5 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652829649/5000000000 : ℝ)*x 0 + (-508358281/2500000000 : ℝ)*x 1 + (2709895387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652829649/5000000000 : ℝ)^4213 ≤ (43286465145917/100000000000000 : ℝ)^3189 := by
    have hnat : (2652829649 : ℕ)^4213*100000000000000^3189 ≤ 43286465145917^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652829649 5000000000 43286465145917 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (508358281/2500000000 : ℝ)^4213 ≤ (6096349996593/50000000000000 : ℝ)^3189 := by
    have hnat : (508358281 : ℕ)^4213*50000000000000^3189 ≤ 6096349996593^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      508358281 2500000000 6096349996593 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709895387/5000000000 : ℝ)^4213 ≤ (44520834849201/100000000000000 : ℝ)^3189 := by
    have hnat : (2709895387 : ℕ)^4213*100000000000000^3189 ≤ 44520834849201^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709895387 5000000000 44520834849201 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652829649/5000000000 : ℝ), (-508358281/2500000000 : ℝ), (2709895387/5000000000 : ℝ)] ![(43286465145917/100000000000000 : ℝ), (6096349996593/50000000000000 : ℝ), (44520834849201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652829649/5000000000 : ℝ)|^4213 ≤ (43286465145917/100000000000000 : ℝ)^3189
        have hw : |(2652829649/5000000000 : ℝ)|=(2652829649/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-508358281/2500000000 : ℝ)|^4213 ≤ (6096349996593/50000000000000 : ℝ)^3189
        have hw : |(-508358281/2500000000 : ℝ)|=(508358281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709895387/5000000000 : ℝ)|^4213 ≤ (44520834849201/100000000000000 : ℝ)^3189
        have hw : |(2709895387/5000000000 : ℝ)|=(2709895387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s3_6 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305659857/10000000000 : ℝ)*x 0 + (5419790611/10000000000 : ℝ)*x 1 + (-1016716293/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305659857/10000000000 : ℝ)^4213 ≤ (43286471170979/100000000000000 : ℝ)^3189 := by
    have hnat : (5305659857 : ℕ)^4213*100000000000000^3189 ≤ 43286471170979^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305659857 10000000000 43286471170979 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419790611/10000000000 : ℝ)^4213 ≤ (44520833080293/100000000000000 : ℝ)^3189 := by
    have hnat : (5419790611 : ℕ)^4213*100000000000000^3189 ≤ 44520833080293^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419790611 10000000000 44520833080293 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1016716293/5000000000 : ℝ)^4213 ≤ (381021741607/3125000000000 : ℝ)^3189 := by
    have hnat : (1016716293 : ℕ)^4213*3125000000000^3189 ≤ 381021741607^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1016716293 5000000000 381021741607 3125000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305659857/10000000000 : ℝ), (5419790611/10000000000 : ℝ), (-1016716293/5000000000 : ℝ)] ![(43286471170979/100000000000000 : ℝ), (44520833080293/100000000000000 : ℝ), (381021741607/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305659857/10000000000 : ℝ)|^4213 ≤ (43286471170979/100000000000000 : ℝ)^3189
        have hw : |(5305659857/10000000000 : ℝ)|=(5305659857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419790611/10000000000 : ℝ)|^4213 ≤ (44520833080293/100000000000000 : ℝ)^3189
        have hw : |(5419790611/10000000000 : ℝ)|=(5419790611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1016716293/5000000000 : ℝ)|^4213 ≤ (381021741607/3125000000000 : ℝ)^3189
        have hw : |(-1016716293/5000000000 : ℝ)|=(1016716293/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s3_7 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1087573809/2500000000 : ℝ)*x 0 + (4535462887/10000000000 : ℝ)*x 1 + (2086275969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087573809/2500000000 : ℝ)^4213 ≤ (33300114350153/100000000000000 : ℝ)^3189 := by
    have hnat : (1087573809 : ℕ)^4213*100000000000000^3189 ≤ 33300114350153^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087573809 2500000000 33300114350153 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4535462887/10000000000 : ℝ)^4213 ≤ (439816511017/1250000000000 : ℝ)^3189 := by
    have hnat : (4535462887 : ℕ)^4213*1250000000000^3189 ≤ 439816511017^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4535462887 10000000000 439816511017 1250000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2086275969/5000000000 : ℝ)^4213 ≤ (1969660296341/6250000000000 : ℝ)^3189 := by
    have hnat : (2086275969 : ℕ)^4213*6250000000000^3189 ≤ 1969660296341^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086275969 5000000000 1969660296341 6250000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087573809/2500000000 : ℝ), (4535462887/10000000000 : ℝ), (2086275969/5000000000 : ℝ)] ![(33300114350153/100000000000000 : ℝ), (439816511017/1250000000000 : ℝ), (1969660296341/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087573809/2500000000 : ℝ)|^4213 ≤ (33300114350153/100000000000000 : ℝ)^3189
        have hw : |(1087573809/2500000000 : ℝ)|=(1087573809/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4535462887/10000000000 : ℝ)|^4213 ≤ (439816511017/1250000000000 : ℝ)^3189
        have hw : |(4535462887/10000000000 : ℝ)|=(4535462887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2086275969/5000000000 : ℝ)|^4213 ≤ (1969660296341/6250000000000 : ℝ)^3189
        have hw : |(2086275969/5000000000 : ℝ)|=(2086275969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1233_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1361/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14709/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16247/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9463/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16247/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9463/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16247/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9463/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9463/100000 : ℝ) ^ (8425/2048 : ℝ) ≤ (1226446581819669/20000000000000000000 : ℝ) := by
    have hpowers : (9463/100000 : ℝ)^8425 ≤ (1226446581819669/20000000000000000000 : ℝ)^2048 := by
      have hnat : (9463 : ℕ)^8425*20000000000000000000^2048 ≤ 1226446581819669^2048*100000^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9463 100000 1226446581819669 20000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9463/100000 : ℝ)) (X := (1226446581819669/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16247/100000 : ℝ) ^ (8425/2048 : ℝ) ≤ (56663416496325461/100000000000000000000 : ℝ) := by
    have hpowers : (16247/100000 : ℝ)^8425 ≤ (56663416496325461/100000000000000000000 : ℝ)^2048 := by
      have hnat : (16247 : ℕ)^8425*100000000000000000000^2048 ≤ 56663416496325461^2048*100000^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16247 100000 56663416496325461 100000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16247/100000 : ℝ)) (X := (56663416496325461/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001226446581819669/10000000000000000000 : ℝ) ≤ (5000149059111137/5000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (10001226446581819669/10000000000000000000 : ℝ)^2048 ≤ (5000149059111137/5000000000000000 : ℝ)^8425 := by
      have hnat : (10001226446581819669 : ℕ)^2048*5000000000000000^8425 ≤ 5000149059111137^8425*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001226446581819669 10000000000000000000 5000149059111137 5000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000149059111137/5000000000000000 : ℝ)) (X := (10001226446581819669/10000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50031397824702711903/50000000000000000000 : ℝ) ≤ (2000305222403661/2000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (50031397824702711903/50000000000000000000 : ℝ)^2048 ≤ (2000305222403661/2000000000000000 : ℝ)^8425 := by
      have hnat : (50031397824702711903 : ℕ)^2048*2000000000000000^8425 ≤ 2000305222403661^8425*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031397824702711903 50000000000000000000 2000305222403661 2000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000305222403661/2000000000000000 : ℝ)) (X := (50031397824702711903/50000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50056663416496325461/50000000000000000000 : ℝ) ≤ (156293032903349/156250000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (50056663416496325461/50000000000000000000 : ℝ)^2048 ≤ (156293032903349/156250000000000 : ℝ)^8425 := by
      have hnat : (50056663416496325461 : ℕ)^2048*156250000000000^8425 ≤ 156293032903349^8425*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50056663416496325461 50000000000000000000 156293032903349 156250000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156293032903349/156250000000000 : ℝ)) (X := (50056663416496325461/50000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1226446581819669/20000000000000000000 : ℝ) ≤ ((6781878142343622411/6784000000000000000 : ℝ)+2*(1227993796031/678400000000000 : ℝ)*(9463/100000 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (6781878142343622411/6784000000000000000 : ℝ)+2*(1227993796031/678400000000000 : ℝ)*(9463/100000 : ℝ)=(5000149059111137/5000000000000000 : ℝ) by norm_num, show 1+2*(1226446581819669/20000000000000000000 : ℝ)=(10001226446581819669/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(56663416496325461/100000000000000000000 : ℝ)+(1226446581819669/20000000000000000000 : ℝ) ≤ ((6781878142343622411/6784000000000000000 : ℝ)+(1227993796031/678400000000000 : ℝ)*((16247/100000 : ℝ)+(9463/100000 : ℝ)))^(8425/2048 : ℝ) := by
    rw [show (6781878142343622411/6784000000000000000 : ℝ)+(1227993796031/678400000000000 : ℝ)*((16247/100000 : ℝ)+(9463/100000 : ℝ))=(2000305222403661/2000000000000000 : ℝ) by norm_num, show 1+(56663416496325461/100000000000000000000 : ℝ)+(1226446581819669/20000000000000000000 : ℝ)=(50031397824702711903/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(56663416496325461/100000000000000000000 : ℝ) ≤ ((6781878142343622411/6784000000000000000 : ℝ)+2*(1227993796031/678400000000000 : ℝ)*(16247/100000 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (6781878142343622411/6784000000000000000 : ℝ)+2*(1227993796031/678400000000000 : ℝ)*(16247/100000 : ℝ)=(156293032903349/156250000000000 : ℝ) by norm_num, show 1+2*(56663416496325461/100000000000000000000 : ℝ)=(50056663416496325461/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6781878142343622411/6784000000000000000 : ℝ)*(X 1 0+X 2 0)+(1227993796031/678400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (9463/100000 : ℝ)) (hi := (16247/100000 : ℝ)) (c := (6781878142343622411/6784000000000000000 : ℝ)) (alpha := (1227993796031/678400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6781878142343622411/6784000000000000000 : ℝ)*(X 0 1+X 2 1)+(1227993796031/678400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (9463/100000 : ℝ)) (hi := (16247/100000 : ℝ)) (c := (6781878142343622411/6784000000000000000 : ℝ)) (alpha := (1227993796031/678400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6781878142343622411/6784000000000000000 : ℝ)*(X 0 2+X 1 2)+(1227993796031/678400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (9463/100000 : ℝ)) (hi := (16247/100000 : ℝ)) (c := (6781878142343622411/6784000000000000000 : ℝ)) (alpha := (1227993796031/678400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2121190679/10000000000 : ℝ)*X 0 0+(2710227213/5000000000 : ℝ)*X 0 1+(5239919993/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337922561/2500000000 : ℝ)*X 1 0+(-553325901/2500000000 : ℝ)*X 1 1+(104798403/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351690139/10000000000 : ℝ)*X 2 0+(5239920561/10000000000 : ℝ)*X 2 1+(-1106651601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4350266189/10000000000 : ℝ)*X 0 0+(417120931/1000000000 : ℝ)*X 0 1+(567099821/1250000000 : ℝ)*X 0 2+(4350266189/10000000000 : ℝ)*X 1 0+(417120931/1000000000 : ℝ)*X 1 1+(567099821/1250000000 : ℝ)*X 1 2+(4350266189/10000000000 : ℝ)*X 2 0+(417120931/1000000000 : ℝ)*X 2 1+(567099821/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-530301387/2500000000 : ℝ)*X 0 0+(5240580181/10000000000 : ℝ)*X 0 1+(5419790351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652829649/5000000000 : ℝ)*X 1 0+(-508358281/2500000000 : ℝ)*X 1 1+(2709895387/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305659857/10000000000 : ℝ)*X 2 0+(5419790611/10000000000 : ℝ)*X 2 1+(-1016716293/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087573809/2500000000 : ℝ)*X 0 0+(4535462887/10000000000 : ℝ)*X 0 1+(2086275969/5000000000 : ℝ)*X 0 2+(1087573809/2500000000 : ℝ)*X 1 0+(4535462887/10000000000 : ℝ)*X 1 1+(2086275969/5000000000 : ℝ)*X 1 2+(1087573809/2500000000 : ℝ)*X 2 0+(4535462887/10000000000 : ℝ)*X 2 1+(2086275969/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2196436532125305403457720889/339200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (407277339/50000000000000 : ℝ)*(base19) + (89731331/20000000000000 : ℝ)*(base23) + (78859361/50000000000000 : ℝ)*(lower2) + (15913023/25000000000000 : ℝ)*(upper5) + (4137247414077811/100000000000000 : ℝ)*(major0) + (4137247414077811/100000000000000 : ℝ)*(major1) + (4137247414077811/100000000000000 : ℝ)*(major2) + (5539135158033933/100000000000000 : ℝ)*(sp0) + (5539160734684347/100000000000000 : ℝ)*(sp1) + (692395682387571/12500000000000 : ℝ)*(sp2) + (1367659693461881/50000000000000 : ℝ)*(sp3) + (3074972329/10000000000000 : ℝ)*(sp4) + (2179259099/50000000000000 : ℝ)*(sp5) + (1863525969/20000000000000 : ℝ)*(sp7) + (1367664352276803/50000000000000 : ℝ)*(f.failure) + (5539165907757223/100000000000000 : ℝ)*(f.sum) + (199911069164979/33920000000000000000000000000 : ℝ)*base66 + (4874647216508367679/678400000000000000000000000000000 : ℝ)*base68 + (4763674545865167679/678400000000000000000000000000000 : ℝ)*base70 + (60773342985167679/678400000000000000000000000000000 : ℝ)*base72 + (19818227505741/33920000000000000000000000000 : ℝ)*base73 + (10465830095036367679/678400000000000000000000000000000 : ℝ)*base76 + (1820938640137167679/678400000000000000000000000000000 : ℝ)*base78 + (14666554571388367679/678400000000000000000000000000000 : ℝ)*base80 + (141828688996659/33920000000000000000000000000 : ℝ)*base82 + (13368041/2500000000000000000000 : ℝ)*base89 + (13368041/2500000000000000000000 : ℝ)*base91 + (13368041/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (361442076183312919376090709/84800000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (477521343/50000000000000 : ℝ)*(base19) + (1060465149/50000000000000 : ℝ)*(base23) + (150114733/100000000000000 : ℝ)*(upper2) + (159691667/50000000000000 : ℝ)*(upper3) + (1041942652326009/25000000000000 : ℝ)*(major0) + (1041942652326009/25000000000000 : ℝ)*(major1) + (1041942652326009/25000000000000 : ℝ)*(major2) + (3937069289/20000000000000 : ℝ)*(sp1) + (1073881539/2000000000000 : ℝ)*(sp2) + (2670141311/100000000000000 : ℝ)*(sp3) + (279001602655447/5000000000000 : ℝ)*(sp4) + (5580011412719809/100000000000000 : ℝ)*(sp5) + (1394994059525423/25000000000000 : ℝ)*(sp6) + (688876588320381/25000000000000 : ℝ)*(sp7) + (688877255855709/25000000000000 : ℝ)*(f.failure) + (279001602655447/5000000000000 : ℝ)*(f.sum) + (60982561611239/8480000000000000000000000000 : ℝ)*base65 + (1445288580548577699/169600000000000000000000000000000 : ℝ)*base67 + (576012131313377699/169600000000000000000000000000000 : ℝ)*base69 + (1053674248865377699/169600000000000000000000000000000 : ℝ)*base71 + (33660766685319/8480000000000000000000000000 : ℝ)*base73 + (2036646173783777699/169600000000000000000000000000000 : ℝ)*base75 + (1461705148398177699/169600000000000000000000000000000 : ℝ)*base77 + (2363152820657377699/169600000000000000000000000000000 : ℝ)*base79 + (3138341047239/8480000000000000000000000000 : ℝ)*base81 + (9623223/1250000000000000000000 : ℝ)*base89 + (9623223/1250000000000000000000 : ℝ)*base91 + (9623223/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1233_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1361/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1233_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1233_s4_0 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-424708359/2000000000 : ℝ)*x 0 + (2698929859/5000000000 : ℝ)*x 1 + (2630487019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (424708359/2000000000 : ℝ)^4213 ≤ (6455761702529/50000000000000 : ℝ)^3189 := by
    have hnat : (424708359 : ℕ)^4213*50000000000000^3189 ≤ 6455761702529^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424708359 2000000000 6455761702529 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698929859/5000000000 : ℝ)^4213 ≤ (44282989445371/100000000000000 : ℝ)^3189 := by
    have hnat : (2698929859 : ℕ)^4213*100000000000000^3189 ≤ 44282989445371^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698929859 5000000000 44282989445371 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630487019/5000000000 : ℝ)^4213 ≤ (8561097427829/20000000000000 : ℝ)^3189 := by
    have hnat : (2630487019 : ℕ)^4213*20000000000000^3189 ≤ 8561097427829^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630487019 5000000000 8561097427829 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-424708359/2000000000 : ℝ), (2698929859/5000000000 : ℝ), (2630487019/5000000000 : ℝ)] ![(6455761702529/50000000000000 : ℝ), (44282989445371/100000000000000 : ℝ), (8561097427829/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-424708359/2000000000 : ℝ)|^4213 ≤ (6455761702529/50000000000000 : ℝ)^3189
        have hw : |(-424708359/2000000000 : ℝ)|=(424708359/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698929859/5000000000 : ℝ)|^4213 ≤ (44282989445371/100000000000000 : ℝ)^3189
        have hw : |(2698929859/5000000000 : ℝ)|=(2698929859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630487019/5000000000 : ℝ)|^4213 ≤ (8561097427829/20000000000000 : ℝ)^3189
        have hw : |(2630487019/5000000000 : ℝ)|=(2630487019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s4_1 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336499587/2500000000 : ℝ)*x 0 + (-1096523019/5000000000 : ℝ)*x 1 + (82202719/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336499587/2500000000 : ℝ)^4213 ≤ (2732611299243/6250000000000 : ℝ)^3189 := by
    have hnat : (1336499587 : ℕ)^4213*6250000000000^3189 ≤ 2732611299243^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336499587 2500000000 2732611299243 6250000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1096523019/5000000000 : ℝ)^4213 ≤ (421022884507/3125000000000 : ℝ)^3189 := by
    have hnat : (1096523019 : ℕ)^4213*3125000000000^3189 ≤ 421022884507^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1096523019 5000000000 421022884507 3125000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82202719/156250000 : ℝ)^4213 ≤ (8561097380533/20000000000000 : ℝ)^3189 := by
    have hnat : (82202719 : ℕ)^4213*20000000000000^3189 ≤ 8561097380533^3189*156250000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82202719 156250000 8561097380533 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336499587/2500000000 : ℝ), (-1096523019/5000000000 : ℝ), (82202719/156250000 : ℝ)] ![(2732611299243/6250000000000 : ℝ), (421022884507/3125000000000 : ℝ), (8561097380533/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336499587/2500000000 : ℝ)|^4213 ≤ (2732611299243/6250000000000 : ℝ)^3189
        have hw : |(1336499587/2500000000 : ℝ)|=(1336499587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1096523019/5000000000 : ℝ)|^4213 ≤ (421022884507/3125000000000 : ℝ)^3189
        have hw : |(-1096523019/5000000000 : ℝ)|=(1096523019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(82202719/156250000 : ℝ)|^4213 ≤ (8561097380533/20000000000000 : ℝ)^3189
        have hw : |(82202719/156250000 : ℝ)|=(82202719/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s4_2 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345998319/10000000000 : ℝ)*x 0 + (5260973913/10000000000 : ℝ)*x 1 + (-548261553/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345998319/10000000000 : ℝ)^4213 ≤ (10930445118639/25000000000000 : ℝ)^3189 := by
    have hnat : (5345998319 : ℕ)^4213*25000000000000^3189 ≤ 10930445118639^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345998319 10000000000 10930445118639 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5260973913/10000000000 : ℝ)^4213 ≤ (42805485795513/100000000000000 : ℝ)^3189 := by
    have hnat : (5260973913 : ℕ)^4213*100000000000000^3189 ≤ 42805485795513^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5260973913 10000000000 42805485795513 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548261553/2500000000 : ℝ)^4213 ≤ (13472733716417/100000000000000 : ℝ)^3189 := by
    have hnat : (548261553 : ℕ)^4213*100000000000000^3189 ≤ 13472733716417^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548261553 2500000000 13472733716417 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345998319/10000000000 : ℝ), (5260973913/10000000000 : ℝ), (-548261553/2500000000 : ℝ)] ![(10930445118639/25000000000000 : ℝ), (42805485795513/100000000000000 : ℝ), (13472733716417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345998319/10000000000 : ℝ)|^4213 ≤ (10930445118639/25000000000000 : ℝ)^3189
        have hw : |(5345998319/10000000000 : ℝ)|=(5345998319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5260973913/10000000000 : ℝ)|^4213 ≤ (42805485795513/100000000000000 : ℝ)^3189
        have hw : |(5260973913/10000000000 : ℝ)|=(5260973913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-548261553/2500000000 : ℝ)|^4213 ≤ (13472733716417/100000000000000 : ℝ)^3189
        have hw : |(-548261553/2500000000 : ℝ)|=(548261553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s4_3 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4351674111/10000000000 : ℝ)*x 0 + (2107612043/5000000000 : ℝ)*x 1 + (4492423947/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351674111/10000000000 : ℝ)^4213 ≤ (33314059106463/100000000000000 : ℝ)^3189 := by
    have hnat : (4351674111 : ℕ)^4213*100000000000000^3189 ≤ 33314059106463^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351674111 10000000000 33314059106463 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2107612043/5000000000 : ℝ)^4213 ≤ (31941047882537/100000000000000 : ℝ)^3189 := by
    have hnat : (2107612043 : ℕ)^4213*100000000000000^3189 ≤ 31941047882537^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2107612043 5000000000 31941047882537 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4492423947/10000000000 : ℝ)^4213 ≤ (34744892999907/100000000000000 : ℝ)^3189 := by
    have hnat : (4492423947 : ℕ)^4213*100000000000000^3189 ≤ 34744892999907^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4492423947 10000000000 34744892999907 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351674111/10000000000 : ℝ), (2107612043/5000000000 : ℝ), (4492423947/10000000000 : ℝ)] ![(33314059106463/100000000000000 : ℝ), (31941047882537/100000000000000 : ℝ), (34744892999907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351674111/10000000000 : ℝ)|^4213 ≤ (33314059106463/100000000000000 : ℝ)^3189
        have hw : |(4351674111/10000000000 : ℝ)|=(4351674111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2107612043/5000000000 : ℝ)|^4213 ≤ (31941047882537/100000000000000 : ℝ)^3189
        have hw : |(2107612043/5000000000 : ℝ)|=(2107612043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4492423947/10000000000 : ℝ)|^4213 ≤ (34744892999907/100000000000000 : ℝ)^3189
        have hw : |(4492423947/10000000000 : ℝ)|=(4492423947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s4_4 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1061773897/5000000000 : ℝ)*x 0 + (5261354119/10000000000 : ℝ)*x 1 + (168671197/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061773897/5000000000 : ℝ)^4213 ≤ (12911571592367/100000000000000 : ℝ)^3189 := by
    have hnat : (1061773897 : ℕ)^4213*100000000000000^3189 ≤ 12911571592367^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061773897 5000000000 12911571592367 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5261354119/10000000000 : ℝ)^4213 ≤ (42809572697541/100000000000000 : ℝ)^3189 := by
    have hnat : (5261354119 : ℕ)^4213*100000000000000^3189 ≤ 42809572697541^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261354119 10000000000 42809572697541 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168671197/312500000 : ℝ)^4213 ≤ (8855771139507/20000000000000 : ℝ)^3189 := by
    have hnat : (168671197 : ℕ)^4213*20000000000000^3189 ≤ 8855771139507^3189*312500000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168671197 312500000 8855771139507 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1061773897/5000000000 : ℝ), (5261354119/10000000000 : ℝ), (168671197/312500000 : ℝ)] ![(12911571592367/100000000000000 : ℝ), (42809572697541/100000000000000 : ℝ), (8855771139507/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1061773897/5000000000 : ℝ)|^4213 ≤ (12911571592367/100000000000000 : ℝ)^3189
        have hw : |(-1061773897/5000000000 : ℝ)|=(1061773897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5261354119/10000000000 : ℝ)|^4213 ≤ (42809572697541/100000000000000 : ℝ)^3189
        have hw : |(5261354119/10000000000 : ℝ)|=(5261354119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168671197/312500000 : ℝ)|^4213 ≤ (8855771139507/20000000000000 : ℝ)^3189
        have hw : |(168671197/312500000 : ℝ)|=(168671197/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s4_5 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331943401/625000000 : ℝ)*x 0 + (-51413549/250000000 : ℝ)*x 1 + (2698739091/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331943401/625000000 : ℝ)^4213 ≤ (43345056034769/100000000000000 : ℝ)^3189 := by
    have hnat : (331943401 : ℕ)^4213*100000000000000^3189 ≤ 43345056034769^3189*625000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331943401 625000000 43345056034769 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (51413549/250000000 : ℝ)^4213 ≤ (12376089576713/100000000000000 : ℝ)^3189 := by
    have hnat : (51413549 : ℕ)^4213*100000000000000^3189 ≤ 12376089576713^3189*250000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51413549 250000000 12376089576713 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698739091/5000000000 : ℝ)^4213 ≤ (44278854375319/100000000000000 : ℝ)^3189 := by
    have hnat : (2698739091 : ℕ)^4213*100000000000000^3189 ≤ 44278854375319^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698739091 5000000000 44278854375319 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331943401/625000000 : ℝ), (-51413549/250000000 : ℝ), (2698739091/5000000000 : ℝ)] ![(43345056034769/100000000000000 : ℝ), (12376089576713/100000000000000 : ℝ), (44278854375319/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331943401/625000000 : ℝ)|^4213 ≤ (43345056034769/100000000000000 : ℝ)^3189
        have hw : |(331943401/625000000 : ℝ)|=(331943401/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-51413549/250000000 : ℝ)|^4213 ≤ (12376089576713/100000000000000 : ℝ)^3189
        have hw : |(-51413549/250000000 : ℝ)|=(51413549/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698739091/5000000000 : ℝ)|^4213 ≤ (44278854375319/100000000000000 : ℝ)^3189
        have hw : |(2698739091/5000000000 : ℝ)|=(2698739091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s4_6 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2655547019/5000000000 : ℝ)*x 0 + (5397478673/10000000000 : ℝ)*x 1 + (-1028270901/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655547019/5000000000 : ℝ)^4213 ≤ (43345051959237/100000000000000 : ℝ)^3189 := by
    have hnat : (2655547019 : ℕ)^4213*100000000000000^3189 ≤ 43345051959237^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655547019 5000000000 43345051959237 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5397478673/10000000000 : ℝ)^4213 ≤ (8855771939339/20000000000000 : ℝ)^3189 := by
    have hnat : (5397478673 : ℕ)^4213*20000000000000^3189 ≤ 8855771939339^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5397478673 10000000000 8855771939339 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1028270901/5000000000 : ℝ)^4213 ≤ (12376088320567/100000000000000 : ℝ)^3189 := by
    have hnat : (1028270901 : ℕ)^4213*100000000000000^3189 ≤ 12376088320567^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028270901 5000000000 12376088320567 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655547019/5000000000 : ℝ), (5397478673/10000000000 : ℝ), (-1028270901/5000000000 : ℝ)] ![(43345051959237/100000000000000 : ℝ), (8855771939339/20000000000000 : ℝ), (12376088320567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655547019/5000000000 : ℝ)|^4213 ≤ (43345051959237/100000000000000 : ℝ)^3189
        have hw : |(2655547019/5000000000 : ℝ)|=(2655547019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5397478673/10000000000 : ℝ)|^4213 ≤ (8855771939339/20000000000000 : ℝ)^3189
        have hw : |(5397478673/10000000000 : ℝ)|=(5397478673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1028270901/5000000000 : ℝ)|^4213 ≤ (12376088320567/100000000000000 : ℝ)^3189
        have hw : |(-1028270901/5000000000 : ℝ)|=(1028270901/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s4_7 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (174067473/400000000 : ℝ)*x 0 + (561456851/1250000000 : ℝ)*x 1 + (4215996227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174067473/400000000 : ℝ)^4213 ≤ (33314187691531/100000000000000 : ℝ)^3189 := by
    have hnat : (174067473 : ℕ)^4213*100000000000000^3189 ≤ 33314187691531^3189*400000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174067473 400000000 33314187691531 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (561456851/1250000000 : ℝ)^4213 ≤ (34737034492267/100000000000000 : ℝ)^3189 := by
    have hnat : (561456851 : ℕ)^4213*100000000000000^3189 ≤ 34737034492267^3189*1250000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      561456851 1250000000 34737034492267 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4215996227/10000000000 : ℝ)^4213 ≤ (1996798612457/6250000000000 : ℝ)^3189 := by
    have hnat : (4215996227 : ℕ)^4213*6250000000000^3189 ≤ 1996798612457^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215996227 10000000000 1996798612457 6250000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174067473/400000000 : ℝ), (561456851/1250000000 : ℝ), (4215996227/10000000000 : ℝ)] ![(33314187691531/100000000000000 : ℝ), (34737034492267/100000000000000 : ℝ), (1996798612457/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174067473/400000000 : ℝ)|^4213 ≤ (33314187691531/100000000000000 : ℝ)^3189
        have hw : |(174067473/400000000 : ℝ)|=(174067473/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(561456851/1250000000 : ℝ)|^4213 ≤ (34737034492267/100000000000000 : ℝ)^3189
        have hw : |(561456851/1250000000 : ℝ)|=(561456851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4215996227/10000000000 : ℝ)|^4213 ≤ (1996798612457/6250000000000 : ℝ)^3189
        have hw : |(4215996227/10000000000 : ℝ)|=(4215996227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1233_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1361/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11337/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14709/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1361/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14709/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1361/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1361/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14709/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1361/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1361/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14709/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1361/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1361/12500 : ℝ) ^ (8425/2048 : ℝ) ≤ (10920096769690227/100000000000000000000 : ℝ) := by
    have hpowers : (1361/12500 : ℝ)^8425 ≤ (10920096769690227/100000000000000000000 : ℝ)^2048 := by
      have hnat : (1361 : ℕ)^8425*100000000000000000000^2048 ≤ 10920096769690227^2048*12500^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1361 12500 10920096769690227 100000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1361/12500 : ℝ)) (X := (10920096769690227/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14709/100000 : ℝ) ^ (8425/2048 : ℝ) ≤ (37638206165641797/100000000000000000000 : ℝ) := by
    have hpowers : (14709/100000 : ℝ)^8425 ≤ (37638206165641797/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14709 : ℕ)^8425*100000000000000000000^2048 ≤ 37638206165641797^2048*100000^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14709 100000 37638206165641797 100000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14709/100000 : ℝ)) (X := (37638206165641797/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010920096769690227/50000000000000000000 : ℝ) ≤ (625033178798039/625000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (50010920096769690227/50000000000000000000 : ℝ)^2048 ≤ (625033178798039/625000000000000 : ℝ)^8425 := by
      have hnat : (50010920096769690227 : ℕ)^2048*625000000000000^8425 ≤ 625033178798039^8425*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010920096769690227 50000000000000000000 625033178798039 625000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625033178798039/625000000000000 : ℝ)) (X := (50010920096769690227/50000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506069787866916503/12500000000000000000 : ℝ) ≤ (2000236033552357/2000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (12506069787866916503/12500000000000000000 : ℝ)^2048 ≤ (2000236033552357/2000000000000000 : ℝ)^8425 := by
      have hnat : (12506069787866916503 : ℕ)^2048*2000000000000000^8425 ≤ 2000236033552357^8425*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506069787866916503 12500000000000000000 2000236033552357 2000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000236033552357/2000000000000000 : ℝ)) (X := (12506069787866916503/12500000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50037638206165641797/50000000000000000000 : ℝ) ≤ (5000914737377473/5000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (50037638206165641797/50000000000000000000 : ℝ)^2048 ≤ (5000914737377473/5000000000000000 : ℝ)^8425 := by
      have hnat : (50037638206165641797 : ℕ)^2048*5000000000000000^8425 ≤ 5000914737377473^8425*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50037638206165641797 50000000000000000000 5000914737377473 5000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000914737377473/5000000000000000 : ℝ)) (X := (50037638206165641797/50000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10920096769690227/100000000000000000000 : ℝ) ≤ ((1193684034684807449/1194062500000000000 : ℝ)+2*(649306993161/382100000000000 : ℝ)*(1361/12500 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (1193684034684807449/1194062500000000000 : ℝ)+2*(649306993161/382100000000000 : ℝ)*(1361/12500 : ℝ)=(625033178798039/625000000000000 : ℝ) by norm_num, show 1+2*(10920096769690227/100000000000000000000 : ℝ)=(50010920096769690227/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(37638206165641797/100000000000000000000 : ℝ)+(10920096769690227/100000000000000000000 : ℝ) ≤ ((1193684034684807449/1194062500000000000 : ℝ)+(649306993161/382100000000000 : ℝ)*((14709/100000 : ℝ)+(1361/12500 : ℝ)))^(8425/2048 : ℝ) := by
    rw [show (1193684034684807449/1194062500000000000 : ℝ)+(649306993161/382100000000000 : ℝ)*((14709/100000 : ℝ)+(1361/12500 : ℝ))=(2000236033552357/2000000000000000 : ℝ) by norm_num, show 1+(37638206165641797/100000000000000000000 : ℝ)+(10920096769690227/100000000000000000000 : ℝ)=(12506069787866916503/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(37638206165641797/100000000000000000000 : ℝ) ≤ ((1193684034684807449/1194062500000000000 : ℝ)+2*(649306993161/382100000000000 : ℝ)*(14709/100000 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (1193684034684807449/1194062500000000000 : ℝ)+2*(649306993161/382100000000000 : ℝ)*(14709/100000 : ℝ)=(5000914737377473/5000000000000000 : ℝ) by norm_num, show 1+2*(37638206165641797/100000000000000000000 : ℝ)=(50037638206165641797/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1193684034684807449/1194062500000000000 : ℝ)*(X 1 0+X 2 0)+(649306993161/382100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (1361/12500 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (1193684034684807449/1194062500000000000 : ℝ)) (alpha := (649306993161/382100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1193684034684807449/1194062500000000000 : ℝ)*(X 0 1+X 2 1)+(649306993161/382100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (1361/12500 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (1193684034684807449/1194062500000000000 : ℝ)) (alpha := (649306993161/382100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1193684034684807449/1194062500000000000 : ℝ)*(X 0 2+X 1 2)+(649306993161/382100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (1361/12500 : ℝ)) (hi := (14709/100000 : ℝ)) (c := (1193684034684807449/1194062500000000000 : ℝ)) (alpha := (649306993161/382100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-424708359/2000000000 : ℝ)*X 0 0+(2698929859/5000000000 : ℝ)*X 0 1+(2630487019/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336499587/2500000000 : ℝ)*X 1 0+(-1096523019/5000000000 : ℝ)*X 1 1+(82202719/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345998319/10000000000 : ℝ)*X 2 0+(5260973913/10000000000 : ℝ)*X 2 1+(-548261553/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351674111/10000000000 : ℝ)*X 0 0+(2107612043/5000000000 : ℝ)*X 0 1+(4492423947/10000000000 : ℝ)*X 0 2+(4351674111/10000000000 : ℝ)*X 1 0+(2107612043/5000000000 : ℝ)*X 1 1+(4492423947/10000000000 : ℝ)*X 1 2+(4351674111/10000000000 : ℝ)*X 2 0+(2107612043/5000000000 : ℝ)*X 2 1+(4492423947/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1061773897/5000000000 : ℝ)*X 0 0+(5261354119/10000000000 : ℝ)*X 0 1+(168671197/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((331943401/625000000 : ℝ)*X 1 0+(-51413549/250000000 : ℝ)*X 1 1+(2698739091/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655547019/5000000000 : ℝ)*X 2 0+(5397478673/10000000000 : ℝ)*X 2 1+(-1028270901/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174067473/400000000 : ℝ)*X 0 0+(561456851/1250000000 : ℝ)*X 0 1+(4215996227/10000000000 : ℝ)*X 0 2+(174067473/400000000 : ℝ)*X 1 0+(561456851/1250000000 : ℝ)*X 1 1+(4215996227/10000000000 : ℝ)*X 1 2+(174067473/400000000 : ℝ)*X 2 0+(561456851/1250000000 : ℝ)*X 2 1+(4215996227/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8654275722793571124850257/1865722656250000000000000000000 : ℝ) := by norm_num
    linear_combination (798937687/50000000000000 : ℝ)*(base19) + (368580499/25000000000000 : ℝ)*(base23) + (35091609/100000000000000 : ℝ)*(upper2) + (329940363/100000000000000 : ℝ)*(upper3) + (79957451/100000000000000 : ℝ)*(upper4) + (682061492743249/12500000000000 : ℝ)*(major0) + (682061492743249/12500000000000 : ℝ)*(major1) + (682061492743249/12500000000000 : ℝ)*(major2) + (1826352585274483/25000000000000 : ℝ)*(sp0) + (58443510949213/800000000000 : ℝ)*(sp1) + (3652719496102501/50000000000000 : ℝ)*(sp2) + (1803760554139927/50000000000000 : ℝ)*(sp3) + (15062714533/50000000000000 : ℝ)*(sp4) + (22154466291/100000000000000 : ℝ)*(sp7) + (1803771631373073/50000000000000 : ℝ)*(f.failure) + (3652720233263499/50000000000000 : ℝ)*(f.sum) + (8745901004413/19105000000000000000000000000 : ℝ)*base66 + (25225130047635773/29851562500000000000000000000000 : ℝ)*base68 + (100813110181724671/59703125000000000000000000000000 : ℝ)*base70 + (166419862799931579/59703125000000000000000000000000 : ℝ)*base71 + (4342394891799/9552500000000000000000000000 : ℝ)*base74 + (1234438287196099671/59703125000000000000000000000000 : ℝ)*base76 + (252519163998400329/59703125000000000000000000000000 : ℝ)*base77 + (496664492137604523/29851562500000000000000000000000 : ℝ)*base80 + (53265668202243/19105000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (30539731/2500000000000000000000 : ℝ)*base89 + (30539731/2500000000000000000000 : ℝ)*base91 + (30539731/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (316970667760324719205267269/59703125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (183861313/25000000000000 : ℝ)*(base19) + (505927919/100000000000000 : ℝ)*(base23) + (197965487/100000000000000 : ℝ)*(upper3) + (4704801/5000000000000 : ℝ)*(lower4) + (2743474359217199/50000000000000 : ℝ)*(major0) + (2743474359217199/50000000000000 : ℝ)*(major1) + (2743474359217199/50000000000000 : ℝ)*(major2) + (745778567/20000000000000 : ℝ)*(sp1) + (5350881177/25000000000000 : ℝ)*(sp2) + (350098051/25000000000000 : ℝ)*(sp3) + (7346217590832033/100000000000000 : ℝ)*(sp4) + (3673106563246973/50000000000000 : ℝ)*(sp5) + (3673097840689703/50000000000000 : ℝ)*(sp6) + (3627678268674103/100000000000000 : ℝ)*(sp7) + (3627679669066307/100000000000000 : ℝ)*(f.failure) + (7346217590832033/100000000000000 : ℝ)*(f.sum) + (81248993695293/19105000000000000000000000000 : ℝ)*base65 + (58583250740565351/59703125000000000000000000000000 : ℝ)*base67 + (519233975741090899/59703125000000000000000000000000 : ℝ)*base70 + (36588079774315351/59703125000000000000000000000000 : ℝ)*base71 + (4210564960757/1194062500000000000000000000 : ℝ)*base74 + (259402960733278399/59703125000000000000000000000000 : ℝ)*base76 + (846872613654877851/59703125000000000000000000000000 : ℝ)*base77 + (2143329037934859/932861328125000000000000000000 : ℝ)*base79 + (45743412592673/19105000000000000000000000000 : ℝ)*base81 + (14070871/5000000000000000000000 : ℝ)*base90 + (14070871/5000000000000000000000 : ℝ)*base92 + (14070871/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1233_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14709/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1361/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1233_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1233_s5_0 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-13275037/62500000 : ℝ)*x 0 + (337039071/625000000 : ℝ)*x 1 + (2632951783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (13275037/62500000 : ℝ)^4213 ≤ (12915251644653/100000000000000 : ℝ)^3189 := by
    have hnat : (13275037 : ℕ)^4213*100000000000000^3189 ≤ 12915251644653^3189*62500000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13275037 62500000 12915251644653 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (337039071/625000000 : ℝ)^4213 ≤ (8845253094327/20000000000000 : ℝ)^3189 := by
    have hnat : (337039071 : ℕ)^4213*20000000000000^3189 ≤ 8845253094327^3189*625000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337039071 625000000 8845253094327 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632951783/5000000000 : ℝ)^4213 ≤ (857169657381/2000000000000 : ℝ)^3189 := by
    have hnat : (2632951783 : ℕ)^4213*2000000000000^3189 ≤ 857169657381^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632951783 5000000000 857169657381 2000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-13275037/62500000 : ℝ), (337039071/625000000 : ℝ), (2632951783/5000000000 : ℝ)] ![(12915251644653/100000000000000 : ℝ), (8845253094327/20000000000000 : ℝ), (857169657381/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-13275037/62500000 : ℝ)|^4213 ≤ (12915251644653/100000000000000 : ℝ)^3189
        have hw : |(-13275037/62500000 : ℝ)|=(13275037/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(337039071/625000000 : ℝ)|^4213 ≤ (8845253094327/20000000000000 : ℝ)^3189
        have hw : |(337039071/625000000 : ℝ)|=(337039071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632951783/5000000000 : ℝ)|^4213 ≤ (857169657381/2000000000000 : ℝ)^3189
        have hw : |(2632951783/5000000000 : ℝ)|=(2632951783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s5_1 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672337339/5000000000 : ℝ)*x 0 + (-34191823/156250000 : ℝ)*x 1 + (2632951783/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672337339/5000000000 : ℝ)^4213 ≤ (43707479721509/100000000000000 : ℝ)^3189 := by
    have hnat : (2672337339 : ℕ)^4213*100000000000000^3189 ≤ 43707479721509^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672337339 5000000000 43707479721509 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (34191823/156250000 : ℝ)^4213 ≤ (6717018699721/50000000000000 : ℝ)^3189 := by
    have hnat : (34191823 : ℕ)^4213*50000000000000^3189 ≤ 6717018699721^3189*156250000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      34191823 156250000 6717018699721 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632951783/5000000000 : ℝ)^4213 ≤ (857169657381/2000000000000 : ℝ)^3189 := by
    have hnat : (2632951783 : ℕ)^4213*2000000000000^3189 ≤ 857169657381^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632951783 5000000000 857169657381 2000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672337339/5000000000 : ℝ), (-34191823/156250000 : ℝ), (2632951783/5000000000 : ℝ)] ![(43707479721509/100000000000000 : ℝ), (6717018699721/50000000000000 : ℝ), (857169657381/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672337339/5000000000 : ℝ)|^4213 ≤ (43707479721509/100000000000000 : ℝ)^3189
        have hw : |(2672337339/5000000000 : ℝ)|=(2672337339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-34191823/156250000 : ℝ)|^4213 ≤ (6717018699721/50000000000000 : ℝ)^3189
        have hw : |(-34191823/156250000 : ℝ)|=(34191823/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632951783/5000000000 : ℝ)|^4213 ≤ (857169657381/2000000000000 : ℝ)^3189
        have hw : |(2632951783/5000000000 : ℝ)|=(2632951783/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s5_2 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2672337339/5000000000 : ℝ)*x 0 + (1316475891/2500000000 : ℝ)*x 1 + (-2188276673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672337339/5000000000 : ℝ)^4213 ≤ (43707479721509/100000000000000 : ℝ)^3189 := by
    have hnat : (2672337339 : ℕ)^4213*100000000000000^3189 ≤ 43707479721509^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672337339 5000000000 43707479721509 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316475891/2500000000 : ℝ)^4213 ≤ (21429241423773/50000000000000 : ℝ)^3189 := by
    have hnat : (1316475891 : ℕ)^4213*50000000000000^3189 ≤ 21429241423773^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316475891 2500000000 21429241423773 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2188276673/10000000000 : ℝ)^4213 ≤ (209906834493/1562500000000 : ℝ)^3189 := by
    have hnat : (2188276673 : ℕ)^4213*1562500000000^3189 ≤ 209906834493^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2188276673 10000000000 209906834493 1562500000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672337339/5000000000 : ℝ), (1316475891/2500000000 : ℝ), (-2188276673/10000000000 : ℝ)] ![(43707479721509/100000000000000 : ℝ), (21429241423773/50000000000000 : ℝ), (209906834493/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672337339/5000000000 : ℝ)|^4213 ≤ (43707479721509/100000000000000 : ℝ)^3189
        have hw : |(2672337339/5000000000 : ℝ)|=(2672337339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316475891/2500000000 : ℝ)|^4213 ≤ (21429241423773/50000000000000 : ℝ)^3189
        have hw : |(1316475891/2500000000 : ℝ)|=(1316475891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2188276673/10000000000 : ℝ)|^4213 ≤ (209906834493/1562500000000 : ℝ)^3189
        have hw : |(-2188276673/10000000000 : ℝ)|=(2188276673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s5_3 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4351946451/10000000000 : ℝ)*x 0 + (1056370169/2500000000 : ℝ)*x 1 + (4482097673/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351946451/10000000000 : ℝ)^4213 ≤ (16658406743447/50000000000000 : ℝ)^3189 := by
    have hnat : (4351946451 : ℕ)^4213*50000000000000^3189 ≤ 16658406743447^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351946451 10000000000 16658406743447 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1056370169/2500000000 : ℝ)^4213 ≤ (8010940962581/25000000000000 : ℝ)^3189 := by
    have hnat : (1056370169 : ℕ)^4213*25000000000000^3189 ≤ 8010940962581^3189*2500000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1056370169 2500000000 8010940962581 25000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4482097673/10000000000 : ℝ)^4213 ≤ (34639422636481/100000000000000 : ℝ)^3189 := by
    have hnat : (4482097673 : ℕ)^4213*100000000000000^3189 ≤ 34639422636481^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4482097673 10000000000 34639422636481 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351946451/10000000000 : ℝ), (1056370169/2500000000 : ℝ), (4482097673/10000000000 : ℝ)] ![(16658406743447/50000000000000 : ℝ), (8010940962581/25000000000000 : ℝ), (34639422636481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351946451/10000000000 : ℝ)|^4213 ≤ (16658406743447/50000000000000 : ℝ)^3189
        have hw : |(4351946451/10000000000 : ℝ)|=(4351946451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1056370169/2500000000 : ℝ)|^4213 ≤ (8010940962581/25000000000000 : ℝ)^3189
        have hw : |(1056370169/2500000000 : ℝ)|=(1056370169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4482097673/10000000000 : ℝ)|^4213 ≤ (34639422636481/100000000000000 : ℝ)^3189
        have hw : |(4482097673/10000000000 : ℝ)|=(4482097673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s5_4 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-53100271/250000000 : ℝ)*x 0 + (658278661/1250000000 : ℝ)*x 1 + (5392298237/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53100271/250000000 : ℝ)^4213 ≤ (12915291167603/100000000000000 : ℝ)^3189 := by
    have hnat : (53100271 : ℕ)^4213*100000000000000^3189 ≤ 12915291167603^3189*250000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53100271 250000000 12915291167603 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658278661/1250000000 : ℝ)^4213 ≤ (342895881281/800000000000 : ℝ)^3189 := by
    have hnat : (658278661 : ℕ)^4213*800000000000^3189 ≤ 342895881281^3189*1250000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658278661 1250000000 342895881281 800000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392298237/10000000000 : ℝ)^4213 ≤ (44222723652811/100000000000000 : ℝ)^3189 := by
    have hnat : (5392298237 : ℕ)^4213*100000000000000^3189 ≤ 44222723652811^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392298237 10000000000 44222723652811 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-53100271/250000000 : ℝ), (658278661/1250000000 : ℝ), (5392298237/10000000000 : ℝ)] ![(12915291167603/100000000000000 : ℝ), (342895881281/800000000000 : ℝ), (44222723652811/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-53100271/250000000 : ℝ)|^4213 ≤ (12915291167603/100000000000000 : ℝ)^3189
        have hw : |(-53100271/250000000 : ℝ)|=(53100271/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658278661/1250000000 : ℝ)|^4213 ≤ (342895881281/800000000000 : ℝ)^3189
        have hw : |(658278661/1250000000 : ℝ)|=(658278661/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392298237/10000000000 : ℝ)|^4213 ≤ (44222723652811/100000000000000 : ℝ)^3189
        have hw : |(5392298237/10000000000 : ℝ)|=(5392298237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s5_5 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062472227/2000000000 : ℝ)*x 0 + (-2061882033/10000000000 : ℝ)*x 1 + (2696149111/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062472227/2000000000 : ℝ)^4213 ≤ (43358714106847/100000000000000 : ℝ)^3189 := by
    have hnat : (1062472227 : ℕ)^4213*100000000000000^3189 ≤ 43358714106847^3189*2000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062472227 2000000000 43358714106847 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2061882033/10000000000 : ℝ)^4213 ≤ (12418562378763/100000000000000 : ℝ)^3189 := by
    have hnat : (2061882033 : ℕ)^4213*100000000000000^3189 ≤ 12418562378763^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061882033 10000000000 12418562378763 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696149111/5000000000 : ℝ)^4213 ≤ (22111361745147/50000000000000 : ℝ)^3189 := by
    have hnat : (2696149111 : ℕ)^4213*50000000000000^3189 ≤ 22111361745147^3189*5000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696149111 5000000000 22111361745147 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062472227/2000000000 : ℝ), (-2061882033/10000000000 : ℝ), (2696149111/5000000000 : ℝ)] ![(43358714106847/100000000000000 : ℝ), (12418562378763/100000000000000 : ℝ), (22111361745147/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062472227/2000000000 : ℝ)|^4213 ≤ (43358714106847/100000000000000 : ℝ)^3189
        have hw : |(1062472227/2000000000 : ℝ)|=(1062472227/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2061882033/10000000000 : ℝ)|^4213 ≤ (12418562378763/100000000000000 : ℝ)^3189
        have hw : |(-2061882033/10000000000 : ℝ)|=(2061882033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696149111/5000000000 : ℝ)|^4213 ≤ (22111361745147/50000000000000 : ℝ)^3189
        have hw : |(2696149111/5000000000 : ℝ)|=(2696149111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s5_6 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312361153/10000000000 : ℝ)*x 0 + (674037277/1250000000 : ℝ)*x 1 + (-2061882017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312361153/10000000000 : ℝ)^4213 ≤ (8671742860187/20000000000000 : ℝ)^3189 := by
    have hnat : (5312361153 : ℕ)^4213*20000000000000^3189 ≤ 8671742860187^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312361153 10000000000 8671742860187 20000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (674037277/1250000000 : ℝ)^4213 ≤ (44222723425287/100000000000000 : ℝ)^3189 := by
    have hnat : (674037277 : ℕ)^4213*100000000000000^3189 ≤ 44222723425287^3189*1250000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674037277 1250000000 44222723425287 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2061882017/10000000000 : ℝ)^4213 ≤ (12418562251453/100000000000000 : ℝ)^3189 := by
    have hnat : (2061882017 : ℕ)^4213*100000000000000^3189 ≤ 12418562251453^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061882017 10000000000 12418562251453 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312361153/10000000000 : ℝ), (674037277/1250000000 : ℝ), (-2061882017/10000000000 : ℝ)] ![(8671742860187/20000000000000 : ℝ), (44222723425287/100000000000000 : ℝ), (12418562251453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312361153/10000000000 : ℝ)|^4213 ≤ (8671742860187/20000000000000 : ℝ)^3189
        have hw : |(5312361153/10000000000 : ℝ)|=(5312361153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(674037277/1250000000 : ℝ)|^4213 ≤ (44222723425287/100000000000000 : ℝ)^3189
        have hw : |(674037277/1250000000 : ℝ)|=(674037277/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2061882017/10000000000 : ℝ)|^4213 ≤ (12418562251453/100000000000000 : ℝ)^3189
        have hw : |(-2061882017/10000000000 : ℝ)|=(2061882017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1233_s5_7 (p : ℝ) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8703913/20000000 : ℝ)*x 0 + (4481438083/10000000000 : ℝ)*x 1 + (4226142697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8703913/20000000 : ℝ)^4213 ≤ (33316915121091/100000000000000 : ℝ)^3189 := by
    have hnat : (8703913 : ℕ)^4213*100000000000000^3189 ≤ 33316915121091^3189*20000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8703913 20000000 33316915121091 100000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481438083/10000000000 : ℝ)^4213 ≤ (17316344186771/50000000000000 : ℝ)^3189 := by
    have hnat : (4481438083 : ℕ)^4213*50000000000000^3189 ≤ 17316344186771^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481438083 10000000000 17316344186771 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4226142697/10000000000 : ℝ)^4213 ≤ (16025198249793/50000000000000 : ℝ)^3189 := by
    have hnat : (4226142697 : ℕ)^4213*50000000000000^3189 ≤ 16025198249793^3189*10000000000^4213 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4226142697 10000000000 16025198249793 50000000000000 4213 3189 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4213/1024 : ℝ)) 4213 3189 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8703913/20000000 : ℝ), (4481438083/10000000000 : ℝ), (4226142697/10000000000 : ℝ)] ![(33316915121091/100000000000000 : ℝ), (17316344186771/50000000000000 : ℝ), (16025198249793/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8703913/20000000 : ℝ)|^4213 ≤ (33316915121091/100000000000000 : ℝ)^3189
        have hw : |(8703913/20000000 : ℝ)|=(8703913/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481438083/10000000000 : ℝ)|^4213 ≤ (17316344186771/50000000000000 : ℝ)^3189
        have hw : |(4481438083/10000000000 : ℝ)|=(4481438083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4226142697/10000000000 : ℝ)|^4213 ≤ (16025198249793/50000000000000 : ℝ)^3189
        have hw : |(4226142697/10000000000 : ℝ)|=(4226142697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1233_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5721/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7063/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11337/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11337/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11337/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11337/100000 : ℝ) ^ (8425/2048 : ℝ) ≤ (3223764381417741/25000000000000000000 : ℝ) := by
    have hpowers : (11337/100000 : ℝ)^8425 ≤ (3223764381417741/25000000000000000000 : ℝ)^2048 := by
      have hnat : (11337 : ℕ)^8425*25000000000000000000^2048 ≤ 3223764381417741^2048*100000^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11337 100000 3223764381417741 25000000000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11337/100000 : ℝ)) (X := (3223764381417741/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (8425/2048 : ℝ) ≤ (514106731766933/1562500000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^8425 ≤ (514106731766933/1562500000000000000 : ℝ)^2048 := by
      have hnat : (3559 : ℕ)^8425*1562500000000000000^2048 ≤ 514106731766933^2048*25000^8425 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 514106731766933 1562500000000000000 8425 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (514106731766933/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503223764381417741/12500000000000000000 : ℝ) ≤ (5000313430273677/5000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (12503223764381417741/12500000000000000000 : ℝ)^2048 ≤ (5000313430273677/5000000000000000 : ℝ)^8425 := by
      have hnat : (12503223764381417741 : ℕ)^2048*5000000000000000^8425 ≤ 5000313430273677^8425*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503223764381417741 12500000000000000000 5000313430273677 5000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000313430273677/5000000000000000 : ℝ)) (X := (12503223764381417741/12500000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011449472089688669/25000000000000000000 : ℝ) ≤ (10001113089885237/10000000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (25011449472089688669/25000000000000000000 : ℝ)^2048 ≤ (10001113089885237/10000000000000000 : ℝ)^8425 := by
      have hnat : (25011449472089688669 : ℕ)^2048*10000000000000000^8425 ≤ 10001113089885237^8425*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011449472089688669 25000000000000000000 10001113089885237 10000000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001113089885237/10000000000000000 : ℝ)) (X := (25011449472089688669/25000000000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (781764106731766933/781250000000000000 : ℝ) ≤ (125019991490289/125000000000000 : ℝ) ^ (8425/2048 : ℝ) := by
    have hpowers : (781764106731766933/781250000000000000 : ℝ)^2048 ≤ (125019991490289/125000000000000 : ℝ)^8425 := by
      have hnat : (781764106731766933 : ℕ)^2048*125000000000000^8425 ≤ 125019991490289^8425*781250000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781764106731766933 781250000000000000 125019991490289 125000000000000 2048 8425 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125019991490289/125000000000000 : ℝ)) (X := (781764106731766933/781250000000000000 : ℝ)) (by norm_num) 8425 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3223764381417741/25000000000000000000 : ℝ) ≤ ((3622599063089952513/3623750000000000000 : ℝ)+2*(486229337883/289900000000000 : ℝ)*(11337/100000 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (3622599063089952513/3623750000000000000 : ℝ)+2*(486229337883/289900000000000 : ℝ)*(11337/100000 : ℝ)=(5000313430273677/5000000000000000 : ℝ) by norm_num, show 1+2*(3223764381417741/25000000000000000000 : ℝ)=(12503223764381417741/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(514106731766933/1562500000000000000 : ℝ)+(3223764381417741/25000000000000000000 : ℝ) ≤ ((3622599063089952513/3623750000000000000 : ℝ)+(486229337883/289900000000000 : ℝ)*((3559/25000 : ℝ)+(11337/100000 : ℝ)))^(8425/2048 : ℝ) := by
    rw [show (3622599063089952513/3623750000000000000 : ℝ)+(486229337883/289900000000000 : ℝ)*((3559/25000 : ℝ)+(11337/100000 : ℝ))=(10001113089885237/10000000000000000 : ℝ) by norm_num, show 1+(514106731766933/1562500000000000000 : ℝ)+(3223764381417741/25000000000000000000 : ℝ)=(25011449472089688669/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(514106731766933/1562500000000000000 : ℝ) ≤ ((3622599063089952513/3623750000000000000 : ℝ)+2*(486229337883/289900000000000 : ℝ)*(3559/25000 : ℝ))^(8425/2048 : ℝ) := by
    rw [show (3622599063089952513/3623750000000000000 : ℝ)+2*(486229337883/289900000000000 : ℝ)*(3559/25000 : ℝ)=(125019991490289/125000000000000 : ℝ) by norm_num, show 1+2*(514106731766933/1562500000000000000 : ℝ)=(781764106731766933/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3622599063089952513/3623750000000000000 : ℝ)*(X 1 0+X 2 0)+(486229337883/289900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3622599063089952513/3623750000000000000 : ℝ)) (alpha := (486229337883/289900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3622599063089952513/3623750000000000000 : ℝ)*(X 0 1+X 2 1)+(486229337883/289900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3622599063089952513/3623750000000000000 : ℝ)) (alpha := (486229337883/289900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3622599063089952513/3623750000000000000 : ℝ)*(X 0 2+X 1 2)+(486229337883/289900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8425/2048 : ℝ)) (lo := (11337/100000 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (3622599063089952513/3623750000000000000 : ℝ)) (alpha := (486229337883/289900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-13275037/62500000 : ℝ)*X 0 0+(337039071/625000000 : ℝ)*X 0 1+(2632951783/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2672337339/5000000000 : ℝ)*X 1 0+(-34191823/156250000 : ℝ)*X 1 1+(2632951783/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672337339/5000000000 : ℝ)*X 2 0+(1316475891/2500000000 : ℝ)*X 2 1+(-2188276673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351946451/10000000000 : ℝ)*X 0 0+(1056370169/2500000000 : ℝ)*X 0 1+(4482097673/10000000000 : ℝ)*X 0 2+(4351946451/10000000000 : ℝ)*X 1 0+(1056370169/2500000000 : ℝ)*X 1 1+(4482097673/10000000000 : ℝ)*X 1 2+(4351946451/10000000000 : ℝ)*X 2 0+(1056370169/2500000000 : ℝ)*X 2 1+(4482097673/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-53100271/250000000 : ℝ)*X 0 0+(658278661/1250000000 : ℝ)*X 0 1+(5392298237/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062472227/2000000000 : ℝ)*X 1 0+(-2061882033/10000000000 : ℝ)*X 1 1+(2696149111/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312361153/10000000000 : ℝ)*X 2 0+(674037277/1250000000 : ℝ)*X 2 1+(-2061882017/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((8703913/20000000 : ℝ)*X 0 0+(4481438083/10000000000 : ℝ)*X 0 1+(4226142697/10000000000 : ℝ)*X 0 2+(8703913/20000000 : ℝ)*X 1 0+(4481438083/10000000000 : ℝ)*X 1 1+(4226142697/10000000000 : ℝ)*X 1 2+(8703913/20000000 : ℝ)*X 2 0+(4481438083/10000000000 : ℝ)*X 2 1+(4226142697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1233_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (237617728749760456499833017/36237500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (634981017/50000000000000 : ℝ)*(base19) + (591935317/50000000000000 : ℝ)*(base23) + (23006527/50000000000000 : ℝ)*(lower2) + (4158071/2500000000000 : ℝ)*(upper3) + (50078427/50000000000000 : ℝ)*(upper5) + (1178828010523701/20000000000000 : ℝ)*(major0) + (1178828010523701/20000000000000 : ℝ)*(major1) + (1178828010523701/20000000000000 : ℝ)*(major2) + (7891352482448131/100000000000000 : ℝ)*(sp0) + (3945692809873193/50000000000000 : ℝ)*(sp1) + (3945692852918893/50000000000000 : ℝ)*(sp2) + (3896874548708543/100000000000000 : ℝ)*(sp3) + (34407260289/100000000000000 : ℝ)*(sp4) + (18448245609/100000000000000 : ℝ)*(sp7) + (487111624619269/12500000000000 : ℝ)*(f.failure) + (394569344485421/5000000000000 : ℝ)*(f.sum) + (3605081052099/724750000000000000000000000 : ℝ)*base65 + (262071224212626887/72475000000000000000000000000000 : ℝ)*base68 + (922320350445426887/72475000000000000000000000000000 : ℝ)*base70 + (1279326369831676887/72475000000000000000000000000000 : ℝ)*base72 + (7614769576753/1449500000000000000000000000 : ℝ)*base73 + (359571314457001887/72475000000000000000000000000000 : ℝ)*base76 + (233770797601676887/72475000000000000000000000000000 : ℝ)*base78 + (920528650166226887/72475000000000000000000000000000 : ℝ)*base80 + (1387432478317/2899000000000000000000000000 : ℝ)*base81 + (176543/625000000000000000000 : ℝ)*base89 + (176543/625000000000000000000 : ℝ)*base91 + (176543/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43103405354061375698679693/18118750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2886689/1000000000000 : ℝ)*(base19) + (107707157/25000000000000 : ℝ)*(base23) + (7536717/25000000000000 : ℝ)*(upper3) + (50024987/100000000000000 : ℝ)*(lower4) + (41014691/100000000000000 : ℝ)*(upper5) + (592459883811963/10000000000000 : ℝ)*(major0) + (592459883811963/10000000000000 : ℝ)*(major1) + (592459883811963/10000000000000 : ℝ)*(major2) + (3598447263/50000000000000 : ℝ)*(sp1) + (1066835333/10000000000000 : ℝ)*(sp2) + (7932166865414237/100000000000000 : ℝ)*(sp4) + (793215937985081/10000000000000 : ℝ)*(sp5) + (7932155766232279/100000000000000 : ℝ)*(sp6) + (6120360518011/156250000000 : ℝ)*(sp7) + (6120360518011/156250000000 : ℝ)*(f.failure) + (7932166865414237/100000000000000 : ℝ)*(f.sum) + (2088277375789/1449500000000000000000000000 : ℝ)*base65 + (154113900110125519/36237500000000000000000000000000 : ℝ)*base67 + (1876920332288019/36237500000000000000000000000000 : ℝ)*base69 + (100192340592650519/36237500000000000000000000000000 : ℝ)*base71 + (114659878643/90593750000000000000000000 : ℝ)*base73 + (270909534979374481/36237500000000000000000000000000 : ℝ)*base76 + (156325914984513019/36237500000000000000000000000000 : ℝ)*base77 + (368068805665774481/36237500000000000000000000000000 : ℝ)*base80 + (1819406576281/579800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (60133/7812500000000000000 : ℝ)*base90 + (60133/7812500000000000000 : ℝ)*base92 + (60133/7812500000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1233_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11337/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5721/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1233_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1233_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5721/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1233_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1233_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1233_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8425/2048 : ℝ) ≤ p) (hpb : p ≤ (4213/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (75626147/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16247/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9463/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5721/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7063/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1233_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
