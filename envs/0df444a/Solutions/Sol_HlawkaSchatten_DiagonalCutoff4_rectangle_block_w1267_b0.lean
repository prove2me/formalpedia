-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1267_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:19:53.589865+00:00
-- url     : https://prove2.me/submissions/0d646b5c-d32a-4560-a2d5-728bb6db5e03

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
theorem support_rectangle_w1267_s0_0 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1852870543/10000000000 : ℝ)*x 0 + (1205177689/2000000000 : ℝ)*x 1 + (1199018751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1852870543/10000000000 : ℝ)^2115 ≤ (10814189420741/100000000000000 : ℝ)^1603 := by
    have hnat : (1852870543 : ℕ)^2115*100000000000000^1603 ≤ 10814189420741^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1852870543 10000000000 10814189420741 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1205177689/2000000000 : ℝ)^2115 ≤ (12814438599051/25000000000000 : ℝ)^1603 := by
    have hnat : (1205177689 : ℕ)^2115*25000000000000^1603 ≤ 12814438599051^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1205177689 2000000000 12814438599051 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1199018751/2500000000 : ℝ)^2115 ≤ (18964028087171/50000000000000 : ℝ)^1603 := by
    have hnat : (1199018751 : ℕ)^2115*50000000000000^1603 ≤ 18964028087171^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199018751 2500000000 18964028087171 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1852870543/10000000000 : ℝ), (1205177689/2000000000 : ℝ), (1199018751/2500000000 : ℝ)] ![(10814189420741/100000000000000 : ℝ), (12814438599051/25000000000000 : ℝ), (18964028087171/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1852870543/10000000000 : ℝ)|^2115 ≤ (10814189420741/100000000000000 : ℝ)^1603
        have hw : |(-1852870543/10000000000 : ℝ)|=(1852870543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1205177689/2000000000 : ℝ)|^2115 ≤ (12814438599051/25000000000000 : ℝ)^1603
        have hw : |(1205177689/2000000000 : ℝ)|=(1205177689/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1199018751/2500000000 : ℝ)|^2115 ≤ (18964028087171/50000000000000 : ℝ)^1603
        have hw : |(1199018751/2500000000 : ℝ)|=(1199018751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s0_1 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1377437771/2500000000 : ℝ)*x 0 + (-2555259251/10000000000 : ℝ)*x 1 + (4796074979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377437771/2500000000 : ℝ)^2115 ≤ (455458951921/1000000000000 : ℝ)^1603 := by
    have hnat : (1377437771 : ℕ)^2115*1000000000000^1603 ≤ 455458951921^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377437771 2500000000 455458951921 1000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2555259251/10000000000 : ℝ)^2115 ≤ (16526048884199/100000000000000 : ℝ)^1603 := by
    have hnat : (2555259251 : ℕ)^2115*100000000000000^1603 ≤ 16526048884199^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2555259251 10000000000 16526048884199 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4796074979/10000000000 : ℝ)^2115 ≤ (37928055913491/100000000000000 : ℝ)^1603 := by
    have hnat : (4796074979 : ℕ)^2115*100000000000000^1603 ≤ 37928055913491^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796074979 10000000000 37928055913491 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377437771/2500000000 : ℝ), (-2555259251/10000000000 : ℝ), (4796074979/10000000000 : ℝ)] ![(455458951921/1000000000000 : ℝ), (16526048884199/100000000000000 : ℝ), (37928055913491/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377437771/2500000000 : ℝ)|^2115 ≤ (455458951921/1000000000000 : ℝ)^1603
        have hw : |(1377437771/2500000000 : ℝ)|=(1377437771/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2555259251/10000000000 : ℝ)|^2115 ≤ (16526048884199/100000000000000 : ℝ)^1603
        have hw : |(-2555259251/10000000000 : ℝ)|=(2555259251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4796074979/10000000000 : ℝ)|^2115 ≤ (37928055913491/100000000000000 : ℝ)^1603
        have hw : |(4796074979/10000000000 : ℝ)|=(4796074979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s0_2 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2754875553/5000000000 : ℝ)*x 0 + (4796074977/10000000000 : ℝ)*x 1 + (-319407403/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2754875553/5000000000 : ℝ)^2115 ≤ (2846618464503/6250000000000 : ℝ)^1603 := by
    have hnat : (2754875553 : ℕ)^2115*6250000000000^1603 ≤ 2846618464503^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2754875553 5000000000 2846618464503 6250000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4796074977/10000000000 : ℝ)^2115 ≤ (37928055892623/100000000000000 : ℝ)^1603 := by
    have hnat : (4796074977 : ℕ)^2115*100000000000000^1603 ≤ 37928055892623^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4796074977 10000000000 37928055892623 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (319407403/1250000000 : ℝ)^2115 ≤ (16526048653803/100000000000000 : ℝ)^1603 := by
    have hnat : (319407403 : ℕ)^2115*100000000000000^1603 ≤ 16526048653803^1603*1250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      319407403 1250000000 16526048653803 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2754875553/5000000000 : ℝ), (4796074977/10000000000 : ℝ), (-319407403/1250000000 : ℝ)] ![(2846618464503/6250000000000 : ℝ), (37928055892623/100000000000000 : ℝ), (16526048653803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2754875553/5000000000 : ℝ)|^2115 ≤ (2846618464503/6250000000000 : ℝ)^1603
        have hw : |(2754875553/5000000000 : ℝ)|=(2754875553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4796074977/10000000000 : ℝ)|^2115 ≤ (37928055892623/100000000000000 : ℝ)^1603
        have hw : |(4796074977/10000000000 : ℝ)|=(4796074977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-319407403/1250000000 : ℝ)|^2115 ≤ (16526048653803/100000000000000 : ℝ)^1603
        have hw : |(-319407403/1250000000 : ℝ)|=(319407403/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s0_3 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (167642601/400000000 : ℝ)*x 0 + (1557989777/5000000000 : ℝ)*x 1 + (562279103/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (167642601/400000000 : ℝ)^2115 ≤ (7936598245501/25000000000000 : ℝ)^1603 := by
    have hnat : (167642601 : ℕ)^2115*25000000000000^1603 ≤ 7936598245501^1603*400000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      167642601 400000000 7936598245501 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1557989777/5000000000 : ℝ)^2115 ≤ (21470796004857/100000000000000 : ℝ)^1603 := by
    have hnat : (1557989777 : ℕ)^2115*100000000000000^1603 ≤ 21470796004857^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1557989777 5000000000 21470796004857 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562279103/1000000000 : ℝ)^2115 ≤ (23391405495041/50000000000000 : ℝ)^1603 := by
    have hnat : (562279103 : ℕ)^2115*50000000000000^1603 ≤ 23391405495041^1603*1000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562279103 1000000000 23391405495041 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(167642601/400000000 : ℝ), (1557989777/5000000000 : ℝ), (562279103/1000000000 : ℝ)] ![(7936598245501/25000000000000 : ℝ), (21470796004857/100000000000000 : ℝ), (23391405495041/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(167642601/400000000 : ℝ)|^2115 ≤ (7936598245501/25000000000000 : ℝ)^1603
        have hw : |(167642601/400000000 : ℝ)|=(167642601/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1557989777/5000000000 : ℝ)|^2115 ≤ (21470796004857/100000000000000 : ℝ)^1603
        have hw : |(1557989777/5000000000 : ℝ)|=(1557989777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562279103/1000000000 : ℝ)|^2115 ≤ (23391405495041/50000000000000 : ℝ)^1603
        have hw : |(562279103/1000000000 : ℝ)|=(562279103/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s0_4 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-928828673/5000000000 : ℝ)*x 0 + (4827728583/10000000000 : ℝ)*x 1 + (5993115341/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (928828673/5000000000 : ℝ)^2115 ≤ (10851065975371/100000000000000 : ℝ)^1603 := by
    have hnat : (928828673 : ℕ)^2115*100000000000000^1603 ≤ 10851065975371^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928828673 5000000000 10851065975371 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4827728583/10000000000 : ℝ)^2115 ≤ (38258677692581/100000000000000 : ℝ)^1603 := by
    have hnat : (4827728583 : ℕ)^2115*100000000000000^1603 ≤ 38258677692581^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4827728583 10000000000 38258677692581 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5993115341/10000000000 : ℝ)^2115 ≤ (50890256320387/100000000000000 : ℝ)^1603 := by
    have hnat : (5993115341 : ℕ)^2115*100000000000000^1603 ≤ 50890256320387^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5993115341 10000000000 50890256320387 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-928828673/5000000000 : ℝ), (4827728583/10000000000 : ℝ), (5993115341/10000000000 : ℝ)] ![(10851065975371/100000000000000 : ℝ), (38258677692581/100000000000000 : ℝ), (50890256320387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-928828673/5000000000 : ℝ)|^2115 ≤ (10851065975371/100000000000000 : ℝ)^1603
        have hw : |(-928828673/5000000000 : ℝ)|=(928828673/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4827728583/10000000000 : ℝ)|^2115 ≤ (38258677692581/100000000000000 : ℝ)^1603
        have hw : |(4827728583/10000000000 : ℝ)|=(4827728583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5993115341/10000000000 : ℝ)|^2115 ≤ (50890256320387/100000000000000 : ℝ)^1603
        have hw : |(5993115341/10000000000 : ℝ)|=(5993115341/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s0_5 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2587516577/5000000000 : ℝ)*x 0 + (-1358216449/10000000000 : ℝ)*x 1 + (1498279449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587516577/5000000000 : ℝ)^2115 ≤ (41931140104447/100000000000000 : ℝ)^1603 := by
    have hnat : (2587516577 : ℕ)^2115*100000000000000^1603 ≤ 41931140104447^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587516577 5000000000 41931140104447 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358216449/10000000000 : ℝ)^2115 ≤ (7178576059847/100000000000000 : ℝ)^1603 := by
    have hnat : (1358216449 : ℕ)^2115*100000000000000^1603 ≤ 7178576059847^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358216449 10000000000 7178576059847 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1498279449/2500000000 : ℝ)^2115 ≤ (25445141912653/50000000000000 : ℝ)^1603 := by
    have hnat : (1498279449 : ℕ)^2115*50000000000000^1603 ≤ 25445141912653^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1498279449 2500000000 25445141912653 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587516577/5000000000 : ℝ), (-1358216449/10000000000 : ℝ), (1498279449/2500000000 : ℝ)] ![(41931140104447/100000000000000 : ℝ), (7178576059847/100000000000000 : ℝ), (25445141912653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587516577/5000000000 : ℝ)|^2115 ≤ (41931140104447/100000000000000 : ℝ)^1603
        have hw : |(2587516577/5000000000 : ℝ)|=(2587516577/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1358216449/10000000000 : ℝ)|^2115 ≤ (7178576059847/100000000000000 : ℝ)^1603
        have hw : |(-1358216449/10000000000 : ℝ)|=(1358216449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1498279449/2500000000 : ℝ)|^2115 ≤ (25445141912653/50000000000000 : ℝ)^1603
        have hw : |(1498279449/2500000000 : ℝ)|=(1498279449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s0_6 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5175034251/10000000000 : ℝ)*x 0 + (1198623151/2000000000 : ℝ)*x 1 + (-1358218047/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175034251/10000000000 : ℝ)^2115 ≤ (4193115183199/10000000000000 : ℝ)^1603 := by
    have hnat : (5175034251 : ℕ)^2115*10000000000000^1603 ≤ 4193115183199^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175034251 10000000000 4193115183199 10000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1198623151/2000000000 : ℝ)^2115 ≤ (50890260958691/100000000000000 : ℝ)^1603 := by
    have hnat : (1198623151 : ℕ)^2115*100000000000000^1603 ≤ 50890260958691^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1198623151 2000000000 50890260958691 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358218047/10000000000 : ℝ)^2115 ≤ (7178587203383/100000000000000 : ℝ)^1603 := by
    have hnat : (1358218047 : ℕ)^2115*100000000000000^1603 ≤ 7178587203383^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358218047 10000000000 7178587203383 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175034251/10000000000 : ℝ), (1198623151/2000000000 : ℝ), (-1358218047/10000000000 : ℝ)] ![(4193115183199/10000000000000 : ℝ), (50890260958691/100000000000000 : ℝ), (7178587203383/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175034251/10000000000 : ℝ)|^2115 ≤ (4193115183199/10000000000000 : ℝ)^1603
        have hw : |(5175034251/10000000000 : ℝ)|=(5175034251/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1198623151/2000000000 : ℝ)|^2115 ≤ (50890260958691/100000000000000 : ℝ)^1603
        have hw : |(1198623151/2000000000 : ℝ)|=(1198623151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1358218047/10000000000 : ℝ)|^2115 ≤ (7178587203383/100000000000000 : ℝ)^1603
        have hw : |(-1358218047/10000000000 : ℝ)|=(1358218047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s0_7 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4200825137/10000000000 : ℝ)*x 0 + (1111655089/2000000000 : ℝ)*x 1 + (198923563/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4200825137/10000000000 : ℝ)^2115 ≤ (3184397348277/10000000000000 : ℝ)^1603 := by
    have hnat : (4200825137 : ℕ)^2115*10000000000000^1603 ≤ 3184397348277^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4200825137 10000000000 3184397348277 10000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1111655089/2000000000 : ℝ)^2115 ≤ (89991952413/195312500000 : ℝ)^1603 := by
    have hnat : (1111655089 : ℕ)^2115*195312500000^1603 ≤ 89991952413^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1111655089 2000000000 89991952413 195312500000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (198923563/625000000 : ℝ)^2115 ≤ (22080146875449/100000000000000 : ℝ)^1603 := by
    have hnat : (198923563 : ℕ)^2115*100000000000000^1603 ≤ 22080146875449^1603*625000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      198923563 625000000 22080146875449 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4200825137/10000000000 : ℝ), (1111655089/2000000000 : ℝ), (198923563/625000000 : ℝ)] ![(3184397348277/10000000000000 : ℝ), (89991952413/195312500000 : ℝ), (22080146875449/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4200825137/10000000000 : ℝ)|^2115 ≤ (3184397348277/10000000000000 : ℝ)^1603
        have hw : |(4200825137/10000000000 : ℝ)|=(4200825137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1111655089/2000000000 : ℝ)|^2115 ≤ (89991952413/195312500000 : ℝ)^1603
        have hw : |(1111655089/2000000000 : ℝ)|=(1111655089/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(198923563/625000000 : ℝ)|^2115 ≤ (22080146875449/100000000000000 : ℝ)^1603
        have hw : |(198923563/625000000 : ℝ)|=(198923563/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1267_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (917/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27343/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (8459/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8459 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8459*1^2048 ≤ 0^2048*1^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8459/2048 : ℝ) ≤ (2271747669164637067/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8459 ≤ (2271747669164637067/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8459*100000000000000000000^2048 ≤ 2271747669164637067^2048*5^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2271747669164637067 100000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2271747669164637067/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8459 := by
      have hnat : (1 : ℕ)^2048*1^8459 ≤ 1^8459*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102271747669164637067/100000000000000000000 : ℝ) ≤ (10054533773829659/10000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (102271747669164637067/100000000000000000000 : ℝ)^2048 ≤ (10054533773829659/10000000000000000 : ℝ)^8459 := by
      have hnat : (102271747669164637067 : ℕ)^2048*10000000000000000^8459 ≤ 10054533773829659^8459*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102271747669164637067 100000000000000000000 10054533773829659 10000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10054533773829659/10000000000000000 : ℝ)) (X := (102271747669164637067/100000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52271747669164637067/50000000000000000000 : ℝ) ≤ (5054533773829659/5000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (52271747669164637067/50000000000000000000 : ℝ)^2048 ≤ (5054533773829659/5000000000000000 : ℝ)^8459 := by
      have hnat : (52271747669164637067 : ℕ)^2048*5000000000000000^8459 ≤ 5054533773829659^8459*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52271747669164637067 50000000000000000000 5054533773829659 5000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5054533773829659/5000000000000000 : ℝ)) (X := (52271747669164637067/50000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(54533773829659/4000000000000000 : ℝ)*(0 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(54533773829659/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2271747669164637067/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(54533773829659/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8459/2048 : ℝ) := by
    rw [show (1 : ℝ)+(54533773829659/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10054533773829659/10000000000000000 : ℝ) by norm_num, show 1+(2271747669164637067/100000000000000000000 : ℝ)+(0 : ℝ)=(102271747669164637067/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2271747669164637067/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(54533773829659/4000000000000000 : ℝ)*(2/5 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(54533773829659/4000000000000000 : ℝ)*(2/5 : ℝ)=(5054533773829659/5000000000000000 : ℝ) by norm_num, show 1+2*(2271747669164637067/100000000000000000000 : ℝ)=(52271747669164637067/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(54533773829659/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54533773829659/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(54533773829659/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54533773829659/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(54533773829659/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (54533773829659/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1852870543/10000000000 : ℝ)*X 0 0+(1205177689/2000000000 : ℝ)*X 0 1+(1199018751/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1377437771/2500000000 : ℝ)*X 1 0+(-2555259251/10000000000 : ℝ)*X 1 1+(4796074979/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2754875553/5000000000 : ℝ)*X 2 0+(4796074977/10000000000 : ℝ)*X 2 1+(-319407403/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((167642601/400000000 : ℝ)*X 0 0+(1557989777/5000000000 : ℝ)*X 0 1+(562279103/1000000000 : ℝ)*X 0 2+(167642601/400000000 : ℝ)*X 1 0+(1557989777/5000000000 : ℝ)*X 1 1+(562279103/1000000000 : ℝ)*X 1 2+(167642601/400000000 : ℝ)*X 2 0+(1557989777/5000000000 : ℝ)*X 2 1+(562279103/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-928828673/5000000000 : ℝ)*X 0 0+(4827728583/10000000000 : ℝ)*X 0 1+(5993115341/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587516577/5000000000 : ℝ)*X 1 0+(-1358216449/10000000000 : ℝ)*X 1 1+(1498279449/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5175034251/10000000000 : ℝ)*X 2 0+(1198623151/2000000000 : ℝ)*X 2 1+(-1358218047/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4200825137/10000000000 : ℝ)*X 0 0+(1111655089/2000000000 : ℝ)*X 0 1+(198923563/625000000 : ℝ)*X 0 2+(4200825137/10000000000 : ℝ)*X 1 0+(1111655089/2000000000 : ℝ)*X 1 1+(198923563/625000000 : ℝ)*X 1 2+(4200825137/10000000000 : ℝ)*X 2 0+(1111655089/2000000000 : ℝ)*X 2 1+(198923563/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42166291777627669115103/8000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59869923/100000000000000 : ℝ)*(base1) + (1281984633/100000000000000 : ℝ)*(base19) + (321307857/25000000000000 : ℝ)*(base23) + (14581019/10000000000000 : ℝ)*(upper3) + (153397013/100000000000000 : ℝ)*(upper5) + (121205656682961/20000000000000 : ℝ)*(major0) + (121205656682961/20000000000000 : ℝ)*(major1) + (121205656682961/20000000000000 : ℝ)*(major2) + (813135295256461/100000000000000 : ℝ)*(sp0) + (203284512915131/25000000000000 : ℝ)*(sp1) + (25410564012929/3125000000000 : ℝ)*(sp2) + (199457509320961/50000000000000 : ℝ)*(sp3) + (2049129309/50000000000000 : ℝ)*(sp4) + (989489859/50000000000000 : ℝ)*(sp7) + (398917057491563/100000000000000 : ℝ)*(f.failure) + (203284833411289/25000000000000 : ℝ)*(f.sum) + (70951251140299/40000000000000000000000000000 : ℝ)*base65 + (467431082780299/80000000000000000000000000000 : ℝ)*base67 + (464448342860299/80000000000000000000000000000 : ℝ)*base69 + (100895187180299/80000000000000000000000000000 : ℝ)*base71 + (266092590780299/40000000000000000000000000000 : ℝ)*base73 + (436797210259701/80000000000000000000000000000 : ℝ)*base76 + (158129175020299/80000000000000000000000000000 : ℝ)*base77 + (218798057420299/80000000000000000000000000000 : ℝ)*base79 + (271577528460299/40000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2352213/312500000000000000000 : ℝ)*base90 + (2352213/312500000000000000000 : ℝ)*base92 + (2352213/312500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1304356113470164130388711/200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (54196267/20000000000000 : ℝ)*(base1) + (281202683/20000000000000 : ℝ)*(base19) + (98687819/6250000000000 : ℝ)*(base23) + (155406851/50000000000000 : ℝ)*(upper3) + (639523874254857/100000000000000 : ℝ)*(major0) + (639523874254857/100000000000000 : ℝ)*(major1) + (639523874254857/100000000000000 : ℝ)*(major2) + (628248657/25000000000000 : ℝ)*(sp1) + (9278689/390625000000 : ℝ)*(sp2) + (2016031/25000000000000 : ℝ)*(sp3) + (429041165263453/50000000000000 : ℝ)*(sp4) + (107259767567191/12500000000000 : ℝ)*(sp5) + (858078105196083/100000000000000 : ℝ)*(sp6) + (105241298131499/25000000000000 : ℝ)*(sp7) + (210482735785727/50000000000000 : ℝ)*(f.failure) + (858082059545571/100000000000000 : ℝ)*(f.sum) + (265198743796237/200000000000000000000000000000 : ℝ)*base66 + (803281374196237/400000000000000000000000000000 : ℝ)*base68 + (1427786817803763/400000000000000000000000000000 : ℝ)*base69 + (1227054025003763/400000000000000000000000000000 : ℝ)*base71 + (637061571796237/200000000000000000000000000000 : ℝ)*base74 + (302588356203763/400000000000000000000000000000 : ℝ)*base75 + (34835035803763/400000000000000000000000000000 : ℝ)*base77 + (514833571803763/400000000000000000000000000000 : ℝ)*base79 + (492535917203763/200000000000000000000000000000 : ℝ)*base81 + (202077/156250000000000000000 : ℝ)*base90 + (202077/156250000000000000000 : ℝ)*base92 + (202077/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1267_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (917/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27343/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1267_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1267_s1_0 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1024230113/5000000000 : ℝ)*x 0 + (1417346713/2500000000 : ℝ)*x 1 + (5027375619/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024230113/5000000000 : ℝ)^2115 ≤ (6172579923879/50000000000000 : ℝ)^1603 := by
    have hnat : (1024230113 : ℕ)^2115*50000000000000^1603 ≤ 6172579923879^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024230113 5000000000 6172579923879 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1417346713/2500000000 : ℝ)^2115 ≤ (23647500734103/50000000000000 : ℝ)^1603 := by
    have hnat : (1417346713 : ℕ)^2115*50000000000000^1603 ≤ 23647500734103^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1417346713 2500000000 23647500734103 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5027375619/10000000000 : ℝ)^2115 ≤ (788278099/1953125000 : ℝ)^1603 := by
    have hnat : (5027375619 : ℕ)^2115*1953125000^1603 ≤ 788278099^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027375619 10000000000 788278099 1953125000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1024230113/5000000000 : ℝ), (1417346713/2500000000 : ℝ), (5027375619/10000000000 : ℝ)] ![(6172579923879/50000000000000 : ℝ), (23647500734103/50000000000000 : ℝ), (788278099/1953125000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1024230113/5000000000 : ℝ)|^2115 ≤ (6172579923879/50000000000000 : ℝ)^1603
        have hw : |(-1024230113/5000000000 : ℝ)|=(1024230113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1417346713/2500000000 : ℝ)|^2115 ≤ (23647500734103/50000000000000 : ℝ)^1603
        have hw : |(1417346713/2500000000 : ℝ)|=(1417346713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5027375619/10000000000 : ℝ)|^2115 ≤ (788278099/1953125000 : ℝ)^1603
        have hw : |(5027375619/10000000000 : ℝ)|=(5027375619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s1_1 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2706152239/5000000000 : ℝ)*x 0 + (-2392804481/10000000000 : ℝ)*x 1 + (5027375441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2706152239/5000000000 : ℝ)^2115 ≤ (44486086546171/100000000000000 : ℝ)^1603 := by
    have hnat : (2706152239 : ℕ)^2115*100000000000000^1603 ≤ 44486086546171^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706152239 5000000000 44486086546171 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2392804481/10000000000 : ℝ)^2115 ≤ (947129791151/6250000000000 : ℝ)^1603 := by
    have hnat : (2392804481 : ℕ)^2115*6250000000000^1603 ≤ 947129791151^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2392804481 10000000000 947129791151 6250000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5027375441/10000000000 : ℝ)^2115 ≤ (20179918391697/50000000000000 : ℝ)^1603 := by
    have hnat : (5027375441 : ℕ)^2115*50000000000000^1603 ≤ 20179918391697^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5027375441 10000000000 20179918391697 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2706152239/5000000000 : ℝ), (-2392804481/10000000000 : ℝ), (5027375441/10000000000 : ℝ)] ![(44486086546171/100000000000000 : ℝ), (947129791151/6250000000000 : ℝ), (20179918391697/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2706152239/5000000000 : ℝ)|^2115 ≤ (44486086546171/100000000000000 : ℝ)^1603
        have hw : |(2706152239/5000000000 : ℝ)|=(2706152239/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2392804481/10000000000 : ℝ)|^2115 ≤ (947129791151/6250000000000 : ℝ)^1603
        have hw : |(-2392804481/10000000000 : ℝ)|=(2392804481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5027375441/10000000000 : ℝ)|^2115 ≤ (20179918391697/50000000000000 : ℝ)^1603
        have hw : |(5027375441/10000000000 : ℝ)|=(5027375441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s1_2 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1082460857/2000000000 : ℝ)*x 0 + (2513687807/5000000000 : ℝ)*x 1 + (-74775141/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082460857/2000000000 : ℝ)^2115 ≤ (44486084453137/100000000000000 : ℝ)^1603 := by
    have hnat : (1082460857 : ℕ)^2115*100000000000000^1603 ≤ 44486084453137^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082460857 2000000000 44486084453137 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2513687807/5000000000 : ℝ)^2115 ≤ (40359838615839/100000000000000 : ℝ)^1603 := by
    have hnat : (2513687807 : ℕ)^2115*100000000000000^1603 ≤ 40359838615839^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2513687807 5000000000 40359838615839 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (74775141/312500000 : ℝ)^2115 ≤ (15154076917453/100000000000000 : ℝ)^1603 := by
    have hnat : (74775141 : ℕ)^2115*100000000000000^1603 ≤ 15154076917453^1603*312500000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74775141 312500000 15154076917453 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082460857/2000000000 : ℝ), (2513687807/5000000000 : ℝ), (-74775141/312500000 : ℝ)] ![(44486084453137/100000000000000 : ℝ), (40359838615839/100000000000000 : ℝ), (15154076917453/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082460857/2000000000 : ℝ)|^2115 ≤ (44486084453137/100000000000000 : ℝ)^1603
        have hw : |(1082460857/2000000000 : ℝ)|=(1082460857/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2513687807/5000000000 : ℝ)|^2115 ≤ (40359838615839/100000000000000 : ℝ)^1603
        have hw : |(2513687807/5000000000 : ℝ)|=(2513687807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-74775141/312500000 : ℝ)|^2115 ≤ (15154076917453/100000000000000 : ℝ)^1603
        have hw : |(-74775141/312500000 : ℝ)|=(74775141/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s1_3 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (269167313/625000000 : ℝ)*x 0 + (924980571/2500000000 : ℝ)*x 1 + (2504288523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269167313/625000000 : ℝ)^2115 ≤ (16453448890533/50000000000000 : ℝ)^1603 := by
    have hnat : (269167313 : ℕ)^2115*50000000000000^1603 ≤ 16453448890533^1603*625000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269167313 625000000 16453448890533 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (924980571/2500000000 : ℝ)^2115 ≤ (13466131105541/50000000000000 : ℝ)^1603 := by
    have hnat : (924980571 : ℕ)^2115*50000000000000^1603 ≤ 13466131105541^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      924980571 2500000000 13466131105541 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2504288523/5000000000 : ℝ)^2115 ≤ (40160839996577/100000000000000 : ℝ)^1603 := by
    have hnat : (2504288523 : ℕ)^2115*100000000000000^1603 ≤ 40160839996577^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2504288523 5000000000 40160839996577 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269167313/625000000 : ℝ), (924980571/2500000000 : ℝ), (2504288523/5000000000 : ℝ)] ![(16453448890533/50000000000000 : ℝ), (13466131105541/50000000000000 : ℝ), (40160839996577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269167313/625000000 : ℝ)|^2115 ≤ (16453448890533/50000000000000 : ℝ)^1603
        have hw : |(269167313/625000000 : ℝ)|=(269167313/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(924980571/2500000000 : ℝ)|^2115 ≤ (13466131105541/50000000000000 : ℝ)^1603
        have hw : |(924980571/2500000000 : ℝ)|=(924980571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2504288523/5000000000 : ℝ)|^2115 ≤ (40160839996577/100000000000000 : ℝ)^1603
        have hw : |(2504288523/5000000000 : ℝ)|=(2504288523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s1_4 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-409821543/2000000000 : ℝ)*x 0 + (5035726721/10000000000 : ℝ)*x 1 + (5660878291/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (409821543/2000000000 : ℝ)^2115 ≤ (12350308580467/100000000000000 : ℝ)^1603 := by
    have hnat : (409821543 : ℕ)^2115*100000000000000^1603 ≤ 12350308580467^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409821543 2000000000 12350308580467 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5035726721/10000000000 : ℝ)^2115 ≤ (40448318416709/100000000000000 : ℝ)^1603 := by
    have hnat : (5035726721 : ℕ)^2115*100000000000000^1603 ≤ 40448318416709^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5035726721 10000000000 40448318416709 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5660878291/10000000000 : ℝ)^2115 ≤ (11800343246733/25000000000000 : ℝ)^1603 := by
    have hnat : (5660878291 : ℕ)^2115*25000000000000^1603 ≤ 11800343246733^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660878291 10000000000 11800343246733 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-409821543/2000000000 : ℝ), (5035726721/10000000000 : ℝ), (5660878291/10000000000 : ℝ)] ![(12350308580467/100000000000000 : ℝ), (40448318416709/100000000000000 : ℝ), (11800343246733/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-409821543/2000000000 : ℝ)|^2115 ≤ (12350308580467/100000000000000 : ℝ)^1603
        have hw : |(-409821543/2000000000 : ℝ)|=(409821543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5035726721/10000000000 : ℝ)|^2115 ≤ (40448318416709/100000000000000 : ℝ)^1603
        have hw : |(5035726721/10000000000 : ℝ)|=(5035726721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5660878291/10000000000 : ℝ)|^2115 ≤ (11800343246733/25000000000000 : ℝ)^1603
        have hw : |(5660878291/10000000000 : ℝ)|=(5660878291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s1_5 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5246709773/10000000000 : ℝ)*x 0 + (-1759301483/10000000000 : ℝ)*x 1 + (5660878801/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5246709773/10000000000 : ℝ)^2115 ≤ (21349546398769/50000000000000 : ℝ)^1603 := by
    have hnat : (5246709773 : ℕ)^2115*50000000000000^1603 ≤ 21349546398769^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246709773 10000000000 21349546398769 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1759301483/10000000000 : ℝ)^2115 ≤ (5049764298397/50000000000000 : ℝ)^1603 := by
    have hnat : (1759301483 : ℕ)^2115*50000000000000^1603 ≤ 5049764298397^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1759301483 10000000000 5049764298397 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5660878801/10000000000 : ℝ)^2115 ≤ (47201378597643/100000000000000 : ℝ)^1603 := by
    have hnat : (5660878801 : ℕ)^2115*100000000000000^1603 ≤ 47201378597643^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660878801 10000000000 47201378597643 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5246709773/10000000000 : ℝ), (-1759301483/10000000000 : ℝ), (5660878801/10000000000 : ℝ)] ![(21349546398769/50000000000000 : ℝ), (5049764298397/50000000000000 : ℝ), (47201378597643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5246709773/10000000000 : ℝ)|^2115 ≤ (21349546398769/50000000000000 : ℝ)^1603
        have hw : |(5246709773/10000000000 : ℝ)|=(5246709773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1759301483/10000000000 : ℝ)|^2115 ≤ (5049764298397/50000000000000 : ℝ)^1603
        have hw : |(-1759301483/10000000000 : ℝ)|=(1759301483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5660878801/10000000000 : ℝ)|^2115 ≤ (47201378597643/100000000000000 : ℝ)^1603
        have hw : |(5660878801/10000000000 : ℝ)|=(5660878801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s1_6 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (655838711/1250000000 : ℝ)*x 0 + (5660878487/10000000000 : ℝ)*x 1 + (-879651029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (655838711/1250000000 : ℝ)^2115 ≤ (1067477297121/2500000000000 : ℝ)^1603 := by
    have hnat : (655838711 : ℕ)^2115*2500000000000^1603 ≤ 1067477297121^1603*1250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655838711 1250000000 1067477297121 2500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5660878487/10000000000 : ℝ)^2115 ≤ (9440275028641/20000000000000 : ℝ)^1603 := by
    have hnat : (5660878487 : ℕ)^2115*20000000000000^1603 ≤ 9440275028641^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5660878487 10000000000 9440275028641 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (879651029/5000000000 : ℝ)^2115 ≤ (10099532951969/100000000000000 : ℝ)^1603 := by
    have hnat : (879651029 : ℕ)^2115*100000000000000^1603 ≤ 10099532951969^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      879651029 5000000000 10099532951969 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(655838711/1250000000 : ℝ), (5660878487/10000000000 : ℝ), (-879651029/5000000000 : ℝ)] ![(1067477297121/2500000000000 : ℝ), (9440275028641/20000000000000 : ℝ), (10099532951969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(655838711/1250000000 : ℝ)|^2115 ≤ (1067477297121/2500000000000 : ℝ)^1603
        have hw : |(655838711/1250000000 : ℝ)|=(655838711/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5660878487/10000000000 : ℝ)|^2115 ≤ (9440275028641/20000000000000 : ℝ)^1603
        have hw : |(5660878487/10000000000 : ℝ)|=(5660878487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-879651029/5000000000 : ℝ)|^2115 ≤ (10099532951969/100000000000000 : ℝ)^1603
        have hw : |(-879651029/5000000000 : ℝ)|=(879651029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s1_7 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4307996273/10000000000 : ℝ)*x 0 + (4991554601/10000000000 : ℝ)*x 1 + (1858632739/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4307996273/10000000000 : ℝ)^2115 ≤ (32920198489541/100000000000000 : ℝ)^1603 := by
    have hnat : (4307996273 : ℕ)^2115*100000000000000^1603 ≤ 32920198489541^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4307996273 10000000000 32920198489541 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4991554601/10000000000 : ℝ)^2115 ≤ (39980848805501/100000000000000 : ℝ)^1603 := by
    have hnat : (4991554601 : ℕ)^2115*100000000000000^1603 ≤ 39980848805501^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4991554601 10000000000 39980848805501 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1858632739/5000000000 : ℝ)^2115 ≤ (27098952694051/100000000000000 : ℝ)^1603 := by
    have hnat : (1858632739 : ℕ)^2115*100000000000000^1603 ≤ 27098952694051^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1858632739 5000000000 27098952694051 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4307996273/10000000000 : ℝ), (4991554601/10000000000 : ℝ), (1858632739/5000000000 : ℝ)] ![(32920198489541/100000000000000 : ℝ), (39980848805501/100000000000000 : ℝ), (27098952694051/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4307996273/10000000000 : ℝ)|^2115 ≤ (32920198489541/100000000000000 : ℝ)^1603
        have hw : |(4307996273/10000000000 : ℝ)|=(4307996273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4991554601/10000000000 : ℝ)|^2115 ≤ (39980848805501/100000000000000 : ℝ)^1603
        have hw : |(4991554601/10000000000 : ℝ)|=(4991554601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1858632739/5000000000 : ℝ)|^2115 ≤ (27098952694051/100000000000000 : ℝ)^1603
        have hw : |(1858632739/5000000000 : ℝ)|=(1858632739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1267_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27343/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (917/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (6321/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9947/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27343/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (917/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27343/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (917/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27343/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (917/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27343/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (917/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27343/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (917/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27343/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (917/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (917/100000 : ℝ) ^ (8459/2048 : ℝ) ≤ (191778186999/50000000000000000000 : ℝ) := by
    have hpowers : (917/100000 : ℝ)^8459 ≤ (191778186999/50000000000000000000 : ℝ)^2048 := by
      have hnat : (917 : ℕ)^8459*50000000000000000000^2048 ≤ 191778186999^2048*100000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        917 100000 191778186999 50000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (917/100000 : ℝ)) (X := (191778186999/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27343/100000 : ℝ) ^ (8459/2048 : ℝ) ≤ (472025725151578449/100000000000000000000 : ℝ) := by
    have hpowers : (27343/100000 : ℝ)^8459 ≤ (472025725151578449/100000000000000000000 : ℝ)^2048 := by
      have hnat : (27343 : ℕ)^8459*100000000000000000000^2048 ≤ 472025725151578449^2048*100000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27343 100000 472025725151578449 100000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27343/100000 : ℝ)) (X := (472025725151578449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000191778186999/25000000000000000000 : ℝ) ≤ (1000000001857249/1000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (25000000191778186999/25000000000000000000 : ℝ)^2048 ≤ (1000000001857249/1000000000000000 : ℝ)^8459 := by
      have hnat : (25000000191778186999 : ℕ)^2048*1000000000000000^8459 ≤ 1000000001857249^8459*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000191778186999 25000000000000000000 1000000001857249 1000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000000001857249/1000000000000000 : ℝ)) (X := (25000000191778186999/25000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100472026108707952447/100000000000000000000 : ℝ) ≤ (2502851947817813/2500000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (100472026108707952447/100000000000000000000 : ℝ)^2048 ≤ (2502851947817813/2500000000000000 : ℝ)^8459 := by
      have hnat : (100472026108707952447 : ℕ)^2048*2500000000000000^8459 ≤ 2502851947817813^8459*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100472026108707952447 100000000000000000000 2502851947817813 2500000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2502851947817813/2500000000000000 : ℝ)) (X := (100472026108707952447/100000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50472025725151578449/50000000000000000000 : ℝ) ≤ (5011407781985007/5000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (50472025725151578449/50000000000000000000 : ℝ)^2048 ≤ (5011407781985007/5000000000000000 : ℝ)^8459 := by
      have hnat : (50472025725151578449 : ℕ)^2048*5000000000000000^8459 ≤ 5011407781985007^8459*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50472025725151578449 50000000000000000000 5011407781985007 5000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5011407781985007/5000000000000000 : ℝ)) (X := (50472025725151578449/50000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(191778186999/50000000000000000000 : ℝ) ≤ ((8257471207364596601/8258125000000000000 : ℝ)+2*(5703886349381/1321300000000000 : ℝ)*(917/100000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (8257471207364596601/8258125000000000000 : ℝ)+2*(5703886349381/1321300000000000 : ℝ)*(917/100000 : ℝ)=(1000000001857249/1000000000000000 : ℝ) by norm_num, show 1+2*(191778186999/50000000000000000000 : ℝ)=(25000000191778186999/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(472025725151578449/100000000000000000000 : ℝ)+(191778186999/50000000000000000000 : ℝ) ≤ ((8257471207364596601/8258125000000000000 : ℝ)+(5703886349381/1321300000000000 : ℝ)*((27343/100000 : ℝ)+(917/100000 : ℝ)))^(8459/2048 : ℝ) := by
    rw [show (8257471207364596601/8258125000000000000 : ℝ)+(5703886349381/1321300000000000 : ℝ)*((27343/100000 : ℝ)+(917/100000 : ℝ))=(2502851947817813/2500000000000000 : ℝ) by norm_num, show 1+(472025725151578449/100000000000000000000 : ℝ)+(191778186999/50000000000000000000 : ℝ)=(100472026108707952447/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(472025725151578449/100000000000000000000 : ℝ) ≤ ((8257471207364596601/8258125000000000000 : ℝ)+2*(5703886349381/1321300000000000 : ℝ)*(27343/100000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (8257471207364596601/8258125000000000000 : ℝ)+2*(5703886349381/1321300000000000 : ℝ)*(27343/100000 : ℝ)=(5011407781985007/5000000000000000 : ℝ) by norm_num, show 1+2*(472025725151578449/100000000000000000000 : ℝ)=(50472025725151578449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8257471207364596601/8258125000000000000 : ℝ)*(X 1 0+X 2 0)+(5703886349381/1321300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (917/100000 : ℝ)) (hi := (27343/100000 : ℝ)) (c := (8257471207364596601/8258125000000000000 : ℝ)) (alpha := (5703886349381/1321300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8257471207364596601/8258125000000000000 : ℝ)*(X 0 1+X 2 1)+(5703886349381/1321300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (917/100000 : ℝ)) (hi := (27343/100000 : ℝ)) (c := (8257471207364596601/8258125000000000000 : ℝ)) (alpha := (5703886349381/1321300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8257471207364596601/8258125000000000000 : ℝ)*(X 0 2+X 1 2)+(5703886349381/1321300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (917/100000 : ℝ)) (hi := (27343/100000 : ℝ)) (c := (8257471207364596601/8258125000000000000 : ℝ)) (alpha := (5703886349381/1321300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1024230113/5000000000 : ℝ)*X 0 0+(1417346713/2500000000 : ℝ)*X 0 1+(5027375619/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2706152239/5000000000 : ℝ)*X 1 0+(-2392804481/10000000000 : ℝ)*X 1 1+(5027375441/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1082460857/2000000000 : ℝ)*X 2 0+(2513687807/5000000000 : ℝ)*X 2 1+(-74775141/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((269167313/625000000 : ℝ)*X 0 0+(924980571/2500000000 : ℝ)*X 0 1+(2504288523/5000000000 : ℝ)*X 0 2+(269167313/625000000 : ℝ)*X 1 0+(924980571/2500000000 : ℝ)*X 1 1+(2504288523/5000000000 : ℝ)*X 1 2+(269167313/625000000 : ℝ)*X 2 0+(924980571/2500000000 : ℝ)*X 2 1+(2504288523/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-409821543/2000000000 : ℝ)*X 0 0+(5035726721/10000000000 : ℝ)*X 0 1+(5660878291/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5246709773/10000000000 : ℝ)*X 1 0+(-1759301483/10000000000 : ℝ)*X 1 1+(5660878801/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((655838711/1250000000 : ℝ)*X 2 0+(5660878487/10000000000 : ℝ)*X 2 1+(-879651029/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4307996273/10000000000 : ℝ)*X 0 0+(4991554601/10000000000 : ℝ)*X 0 1+(1858632739/5000000000 : ℝ)*X 0 2+(4307996273/10000000000 : ℝ)*X 1 0+(4991554601/10000000000 : ℝ)*X 1 1+(1858632739/5000000000 : ℝ)*X 1 2+(4307996273/10000000000 : ℝ)*X 2 0+(4991554601/10000000000 : ℝ)*X 2 1+(1858632739/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (99420778478893245886672173/25806640625000000000000000000000 : ℝ) := by norm_num
    linear_combination (45942861/100000000000000 : ℝ)*(base1) + (402042839/50000000000000 : ℝ)*(base19) + (93567751/12500000000000 : ℝ)*(base23) + (9249281/10000000000000 : ℝ)*(upper3) + (1332571/2000000000000 : ℝ)*(upper5) + (580440313797211/50000000000000 : ℝ)*(major0) + (580440313797211/50000000000000 : ℝ)*(major1) + (580440313797211/50000000000000 : ℝ)*(major2) + (389402370221571/25000000000000 : ℝ)*(sp0) + (311522536037389/20000000000000 : ℝ)*(sp1) + (194701591966327/12500000000000 : ℝ)*(sp2) + (764145479376593/100000000000000 : ℝ)*(sp3) + (10123323/250000000000 : ℝ)*(sp4) + (1058589597/50000000000000 : ℝ)*(sp7) + (764147642498649/100000000000000 : ℝ)*(f.failure) + (1557613484272623/100000000000000 : ℝ)*(f.sum) + (49759446707963/16516250000000000000000000000 : ℝ)*base65 + (1350571147384386061/412906250000000000000000000000000 : ℝ)*base67 + (4370610884408886061/412906250000000000000000000000000 : ℝ)*base69 + (1865838408461073561/412906250000000000000000000000000 : ℝ)*base71 + (203446308311817/66065000000000000000000000000 : ℝ)*base73 + (3339868574204604811/412906250000000000000000000000000 : ℝ)*base75 + (1336554593834511061/412906250000000000000000000000000 : ℝ)*base77 + (1527099294207113939/412906250000000000000000000000000 : ℝ)*base80 + (163220962584903/16516250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (53599/312500000000000000000 : ℝ)*base90 + (53599/312500000000000000000 : ℝ)*base92 + (53599/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39466444082743635006807537/5161328125000000000000000000000 : ℝ) := by norm_num
    linear_combination (4558743/25000000000000 : ℝ)*(base1) + (91428287/6250000000000 : ℝ)*(base19) + (700041099/50000000000000 : ℝ)*(base23) + (52489257/25000000000000 : ℝ)*(upper3) + (165182107/100000000000000 : ℝ)*(upper5) + (59609076419933/5000000000000 : ℝ)*(major0) + (59609076419933/5000000000000 : ℝ)*(major1) + (59609076419933/5000000000000 : ℝ)*(major2) + (7830266719/100000000000000 : ℝ)*(sp1) + (6662533299/100000000000000 : ℝ)*(sp2) + (799805707222639/50000000000000 : ℝ)*(sp4) + (399900525772749/25000000000000 : ℝ)*(sp5) + (1599603333594809/100000000000000 : ℝ)*(sp6) + (784751387466451/100000000000000 : ℝ)*(sp7) + (784751405701423/100000000000000 : ℝ)*(f.failure) + (799805698105153/50000000000000 : ℝ)*(f.sum) + (990802960703/13213000000000000000000000000 : ℝ)*base65 + (132282944636980821/20645312500000000000000000000000 : ℝ)*base68 + (498864337680933517/41290625000000000000000000000000 : ℝ)*base70 + (170300136092780821/20645312500000000000000000000000 : ℝ)*base72 + (1237614267761/660650000000000000000000000 : ℝ)*base73 + (195196189196874571/20645312500000000000000000000000 : ℝ)*base76 + (92035838683127267/41290625000000000000000000000000 : ℝ)*base78 + (78903108682591483/41290625000000000000000000000000 : ℝ)*base79 + (15445376766773/3303250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2419927/312500000000000000000 : ℝ)*base89 + (2419927/312500000000000000000 : ℝ)*base91 + (2419927/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1267_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27343/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (917/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (6321/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9947/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1267_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1267_s2_0 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-261908193/1250000000 : ℝ)*x 0 + (2744296683/5000000000 : ℝ)*x 1 + (5178297717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261908193/1250000000 : ℝ)^2115 ≤ (6359340405587/50000000000000 : ℝ)^1603 := by
    have hnat : (261908193 : ℕ)^2115*50000000000000^1603 ≤ 6359340405587^1603*1250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261908193 1250000000 6359340405587 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744296683/5000000000 : ℝ)^2115 ≤ (22657637776471/50000000000000 : ℝ)^1603 := by
    have hnat : (2744296683 : ℕ)^2115*50000000000000^1603 ≤ 22657637776471^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744296683 5000000000 22657637776471 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5178297717/10000000000 : ℝ)^2115 ≤ (4196604362079/10000000000000 : ℝ)^1603 := by
    have hnat : (5178297717 : ℕ)^2115*10000000000000^1603 ≤ 4196604362079^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5178297717 10000000000 4196604362079 10000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-261908193/1250000000 : ℝ), (2744296683/5000000000 : ℝ), (5178297717/10000000000 : ℝ)] ![(6359340405587/50000000000000 : ℝ), (22657637776471/50000000000000 : ℝ), (4196604362079/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-261908193/1250000000 : ℝ)|^2115 ≤ (6359340405587/50000000000000 : ℝ)^1603
        have hw : |(-261908193/1250000000 : ℝ)|=(261908193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744296683/5000000000 : ℝ)|^2115 ≤ (22657637776471/50000000000000 : ℝ)^1603
        have hw : |(2744296683/5000000000 : ℝ)|=(2744296683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5178297717/10000000000 : ℝ)|^2115 ≤ (4196604362079/10000000000000 : ℝ)^1603
        have hw : |(5178297717/10000000000 : ℝ)|=(5178297717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s2_1 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5368679833/10000000000 : ℝ)*x 0 + (-2255858769/10000000000 : ℝ)*x 1 + (2589148977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368679833/10000000000 : ℝ)^2115 ≤ (11003399764361/25000000000000 : ℝ)^1603 := by
    have hnat : (5368679833 : ℕ)^2115*25000000000000^1603 ≤ 11003399764361^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368679833 10000000000 11003399764361 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2255858769/10000000000 : ℝ)^2115 ≤ (7010177389241/50000000000000 : ℝ)^1603 := by
    have hnat : (2255858769 : ℕ)^2115*50000000000000^1603 ≤ 7010177389241^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2255858769 10000000000 7010177389241 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2589148977/5000000000 : ℝ)^2115 ≤ (41966046154963/100000000000000 : ℝ)^1603 := by
    have hnat : (2589148977 : ℕ)^2115*100000000000000^1603 ≤ 41966046154963^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589148977 5000000000 41966046154963 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368679833/10000000000 : ℝ), (-2255858769/10000000000 : ℝ), (2589148977/5000000000 : ℝ)] ![(11003399764361/25000000000000 : ℝ), (7010177389241/50000000000000 : ℝ), (41966046154963/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368679833/10000000000 : ℝ)|^2115 ≤ (11003399764361/25000000000000 : ℝ)^1603
        have hw : |(5368679833/10000000000 : ℝ)|=(5368679833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2255858769/10000000000 : ℝ)|^2115 ≤ (7010177389241/50000000000000 : ℝ)^1603
        have hw : |(-2255858769/10000000000 : ℝ)|=(2255858769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2589148977/5000000000 : ℝ)|^2115 ≤ (41966046154963/100000000000000 : ℝ)^1603
        have hw : |(2589148977/5000000000 : ℝ)|=(2589148977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s2_2 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5368679781/10000000000 : ℝ)*x 0 + (103565959/200000000 : ℝ)*x 1 + (-1127929421/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5368679781/10000000000 : ℝ)^2115 ≤ (44013598494973/100000000000000 : ℝ)^1603 := by
    have hnat : (5368679781 : ℕ)^2115*100000000000000^1603 ≤ 44013598494973^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5368679781 10000000000 44013598494973 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103565959/200000000 : ℝ)^2115 ≤ (655719470503/1562500000000 : ℝ)^1603 := by
    have hnat : (103565959 : ℕ)^2115*1562500000000^1603 ≤ 655719470503^1603*200000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103565959 200000000 655719470503 1562500000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1127929421/5000000000 : ℝ)^2115 ≤ (1752544422137/12500000000000 : ℝ)^1603 := by
    have hnat : (1127929421 : ℕ)^2115*12500000000000^1603 ≤ 1752544422137^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1127929421 5000000000 1752544422137 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5368679781/10000000000 : ℝ), (103565959/200000000 : ℝ), (-1127929421/5000000000 : ℝ)] ![(44013598494973/100000000000000 : ℝ), (655719470503/1562500000000 : ℝ), (1752544422137/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5368679781/10000000000 : ℝ)|^2115 ≤ (44013598494973/100000000000000 : ℝ)^1603
        have hw : |(5368679781/10000000000 : ℝ)|=(5368679781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(103565959/200000000 : ℝ)|^2115 ≤ (655719470503/1562500000000 : ℝ)^1603
        have hw : |(103565959/200000000 : ℝ)|=(103565959/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1127929421/5000000000 : ℝ)|^2115 ≤ (1752544422137/12500000000000 : ℝ)^1603
        have hw : |(-1127929421/5000000000 : ℝ)|=(1127929421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s2_3 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2169529799/5000000000 : ℝ)*x 0 + (403391193/1000000000 : ℝ)*x 1 + (4666407761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2169529799/5000000000 : ℝ)^2115 ≤ (33233751461227/100000000000000 : ℝ)^1603 := by
    have hnat : (2169529799 : ℕ)^2115*100000000000000^1603 ≤ 33233751461227^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169529799 5000000000 33233751461227 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (403391193/1000000000 : ℝ)^2115 ≤ (15092632246841/50000000000000 : ℝ)^1603 := by
    have hnat : (403391193 : ℕ)^2115*50000000000000^1603 ≤ 15092632246841^1603*1000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      403391193 1000000000 15092632246841 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4666407761/10000000000 : ℝ)^2115 ≤ (36580984030949/100000000000000 : ℝ)^1603 := by
    have hnat : (4666407761 : ℕ)^2115*100000000000000^1603 ≤ 36580984030949^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4666407761 10000000000 36580984030949 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2169529799/5000000000 : ℝ), (403391193/1000000000 : ℝ), (4666407761/10000000000 : ℝ)] ![(33233751461227/100000000000000 : ℝ), (15092632246841/50000000000000 : ℝ), (36580984030949/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2169529799/5000000000 : ℝ)|^2115 ≤ (33233751461227/100000000000000 : ℝ)^1603
        have hw : |(2169529799/5000000000 : ℝ)|=(2169529799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(403391193/1000000000 : ℝ)|^2115 ≤ (15092632246841/50000000000000 : ℝ)^1603
        have hw : |(403391193/1000000000 : ℝ)|=(403391193/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4666407761/10000000000 : ℝ)|^2115 ≤ (36580984030949/100000000000000 : ℝ)^1603
        have hw : |(4666407761/10000000000 : ℝ)|=(4666407761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s2_4 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2095338919/10000000000 : ℝ)*x 0 + (2590129213/5000000000 : ℝ)*x 1 + (1371653647/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2095338919/10000000000 : ℝ)^2115 ≤ (12719268476937/100000000000000 : ℝ)^1603 := by
    have hnat : (2095338919 : ℕ)^2115*100000000000000^1603 ≤ 12719268476937^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2095338919 10000000000 12719268476937 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2590129213/5000000000 : ℝ)^2115 ≤ (20993505092341/50000000000000 : ℝ)^1603 := by
    have hnat : (2590129213 : ℕ)^2115*50000000000000^1603 ≤ 20993505092341^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2590129213 5000000000 20993505092341 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1371653647/2500000000 : ℝ)^2115 ≤ (45293721324387/100000000000000 : ℝ)^1603 := by
    have hnat : (1371653647 : ℕ)^2115*100000000000000^1603 ≤ 45293721324387^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1371653647 2500000000 45293721324387 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2095338919/10000000000 : ℝ), (2590129213/5000000000 : ℝ), (1371653647/2500000000 : ℝ)] ![(12719268476937/100000000000000 : ℝ), (20993505092341/50000000000000 : ℝ), (45293721324387/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2095338919/10000000000 : ℝ)|^2115 ≤ (12719268476937/100000000000000 : ℝ)^1603
        have hw : |(-2095338919/10000000000 : ℝ)|=(2095338919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2590129213/5000000000 : ℝ)|^2115 ≤ (20993505092341/50000000000000 : ℝ)^1603
        have hw : |(2590129213/5000000000 : ℝ)|=(2590129213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1371653647/2500000000 : ℝ)|^2115 ≤ (45293721324387/100000000000000 : ℝ)^1603
        have hw : |(1371653647/2500000000 : ℝ)|=(1371653647/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s2_5 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2644658221/5000000000 : ℝ)*x 0 + (-1947541853/10000000000 : ℝ)*x 1 + (548661463/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2644658221/5000000000 : ℝ)^2115 ≤ (5394647461177/12500000000000 : ℝ)^1603 := by
    have hnat : (2644658221 : ℕ)^2115*12500000000000^1603 ≤ 5394647461177^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2644658221 5000000000 5394647461177 12500000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1947541853/10000000000 : ℝ)^2115 ≤ (2887274625411/25000000000000 : ℝ)^1603 := by
    have hnat : (1947541853 : ℕ)^2115*25000000000000^1603 ≤ 2887274625411^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947541853 10000000000 2887274625411 25000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (548661463/1000000000 : ℝ)^2115 ≤ (22646860890927/50000000000000 : ℝ)^1603 := by
    have hnat : (548661463 : ℕ)^2115*50000000000000^1603 ≤ 22646860890927^1603*1000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      548661463 1000000000 22646860890927 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2644658221/5000000000 : ℝ), (-1947541853/10000000000 : ℝ), (548661463/1000000000 : ℝ)] ![(5394647461177/12500000000000 : ℝ), (2887274625411/25000000000000 : ℝ), (22646860890927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2644658221/5000000000 : ℝ)|^2115 ≤ (5394647461177/12500000000000 : ℝ)^1603
        have hw : |(2644658221/5000000000 : ℝ)|=(2644658221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1947541853/10000000000 : ℝ)|^2115 ≤ (2887274625411/25000000000000 : ℝ)^1603
        have hw : |(-1947541853/10000000000 : ℝ)|=(1947541853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(548661463/1000000000 : ℝ)|^2115 ≤ (22646860890927/50000000000000 : ℝ)^1603
        have hw : |(548661463/1000000000 : ℝ)|=(548661463/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s2_6 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1057863311/2000000000 : ℝ)*x 0 + (5486614749/10000000000 : ℝ)*x 1 + (-973770767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057863311/2000000000 : ℝ)^2115 ≤ (21578590452953/50000000000000 : ℝ)^1603 := by
    have hnat : (1057863311 : ℕ)^2115*50000000000000^1603 ≤ 21578590452953^1603*2000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057863311 2000000000 21578590452953 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5486614749/10000000000 : ℝ)^2115 ≤ (4529372307801/10000000000000 : ℝ)^1603 := by
    have hnat : (5486614749 : ℕ)^2115*10000000000000^1603 ≤ 4529372307801^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5486614749 10000000000 4529372307801 10000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (973770767/5000000000 : ℝ)^2115 ≤ (2309819201147/20000000000000 : ℝ)^1603 := by
    have hnat : (973770767 : ℕ)^2115*20000000000000^1603 ≤ 2309819201147^1603*5000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973770767 5000000000 2309819201147 20000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057863311/2000000000 : ℝ), (5486614749/10000000000 : ℝ), (-973770767/5000000000 : ℝ)] ![(21578590452953/50000000000000 : ℝ), (4529372307801/10000000000000 : ℝ), (2309819201147/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057863311/2000000000 : ℝ)|^2115 ≤ (21578590452953/50000000000000 : ℝ)^1603
        have hw : |(1057863311/2000000000 : ℝ)|=(1057863311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5486614749/10000000000 : ℝ)|^2115 ≤ (4529372307801/10000000000000 : ℝ)^1603
        have hw : |(5486614749/10000000000 : ℝ)|=(5486614749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-973770767/5000000000 : ℝ)|^2115 ≤ (2309819201147/20000000000000 : ℝ)^1603
        have hw : |(-973770767/5000000000 : ℝ)|=(973770767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1267_s2_7 (p : ℝ) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1084802189/2500000000 : ℝ)*x 0 + (4662411659/10000000000 : ℝ)*x 1 + (100948611/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1084802189/2500000000 : ℝ)^2115 ≤ (33235258795373/100000000000000 : ℝ)^1603 := by
    have hnat : (1084802189 : ℕ)^2115*100000000000000^1603 ≤ 33235258795373^1603*2500000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084802189 2500000000 33235258795373 100000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4662411659/10000000000 : ℝ)^2115 ≤ (18269828856979/50000000000000 : ℝ)^1603 := by
    have hnat : (4662411659 : ℕ)^2115*50000000000000^1603 ≤ 18269828856979^1603*10000000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4662411659 10000000000 18269828856979 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (100948611/250000000 : ℝ)^2115 ≤ (15112541739431/50000000000000 : ℝ)^1603 := by
    have hnat : (100948611 : ℕ)^2115*50000000000000^1603 ≤ 15112541739431^1603*250000000^2115 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100948611 250000000 15112541739431 50000000000000 2115 1603 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2115/512 : ℝ)) 2115 1603 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1084802189/2500000000 : ℝ), (4662411659/10000000000 : ℝ), (100948611/250000000 : ℝ)] ![(33235258795373/100000000000000 : ℝ), (18269828856979/50000000000000 : ℝ), (15112541739431/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1084802189/2500000000 : ℝ)|^2115 ≤ (33235258795373/100000000000000 : ℝ)^1603
        have hw : |(1084802189/2500000000 : ℝ)|=(1084802189/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4662411659/10000000000 : ℝ)|^2115 ≤ (18269828856979/50000000000000 : ℝ)^1603
        have hw : |(4662411659/10000000000 : ℝ)|=(4662411659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(100948611/250000000 : ℝ)|^2115 ≤ (15112541739431/50000000000000 : ℝ)^1603
        have hw : |(100948611/250000000 : ℝ)|=(100948611/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1267_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9947/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9599/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16159/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9947/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (6321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9947/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (6321/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9947/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (6321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9947/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (6321/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9947/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (6321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9947/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (6321/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (6321/100000 : ℝ) ^ (8459/2048 : ℝ) ≤ (556891125977389/50000000000000000000 : ℝ) := by
    have hpowers : (6321/100000 : ℝ)^8459 ≤ (556891125977389/50000000000000000000 : ℝ)^2048 := by
      have hnat : (6321 : ℕ)^8459*50000000000000000000^2048 ≤ 556891125977389^2048*100000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6321 100000 556891125977389 50000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (6321/100000 : ℝ)) (X := (556891125977389/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (9947/50000 : ℝ) ^ (8459/2048 : ℝ) ≤ (126900136531427293/100000000000000000000 : ℝ) := by
    have hpowers : (9947/50000 : ℝ)^8459 ≤ (126900136531427293/100000000000000000000 : ℝ)^2048 := by
      have hnat : (9947 : ℕ)^8459*100000000000000000000^2048 ≤ 126900136531427293^2048*50000^8459 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9947 50000 126900136531427293 100000000000000000000 8459 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9947/50000 : ℝ)) (X := (126900136531427293/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000556891125977389/25000000000000000000 : ℝ) ≤ (1000005393088539/1000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (25000556891125977389/25000000000000000000 : ℝ)^2048 ≤ (1000005393088539/1000000000000000 : ℝ)^8459 := by
      have hnat : (25000556891125977389 : ℕ)^2048*1000000000000000^8459 ≤ 1000005393088539^8459*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000556891125977389 25000000000000000000 1000005393088539 1000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000005393088539/1000000000000000 : ℝ)) (X := (25000556891125977389/25000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100128013918783382071/100000000000000000000 : ℝ) ≤ (10003097829770881/10000000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (100128013918783382071/100000000000000000000 : ℝ)^2048 ≤ (10003097829770881/10000000000000000 : ℝ)^8459 := by
      have hnat : (100128013918783382071 : ℕ)^2048*10000000000000000^8459 ≤ 10003097829770881^8459*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100128013918783382071 100000000000000000000 10003097829770881 10000000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003097829770881/10000000000000000 : ℝ)) (X := (100128013918783382071/100000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50126900136531427293/50000000000000000000 : ℝ) ≤ (2501535432164093/2500000000000000 : ℝ) ^ (8459/2048 : ℝ) := by
    have hpowers : (50126900136531427293/50000000000000000000 : ℝ)^2048 ≤ (2501535432164093/2500000000000000 : ℝ)^8459 := by
      have hnat : (50126900136531427293 : ℕ)^2048*2500000000000000^8459 ≤ 2501535432164093^8459*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50126900136531427293 50000000000000000000 2501535432164093 2500000000000000 2048 8459 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2501535432164093/2500000000000000 : ℝ)) (X := (50126900136531427293/50000000000000000000 : ℝ)) (by norm_num) 8459 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(556891125977389/50000000000000000000 : ℝ) ≤ ((43269212702231193/43281250000000000 : ℝ)+2*(3043898885491/1357300000000000 : ℝ)*(6321/100000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (43269212702231193/43281250000000000 : ℝ)+2*(3043898885491/1357300000000000 : ℝ)*(6321/100000 : ℝ)=(1000005393088539/1000000000000000 : ℝ) by norm_num, show 1+2*(556891125977389/50000000000000000000 : ℝ)=(25000556891125977389/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(126900136531427293/100000000000000000000 : ℝ)+(556891125977389/50000000000000000000 : ℝ) ≤ ((43269212702231193/43281250000000000 : ℝ)+(3043898885491/1357300000000000 : ℝ)*((9947/50000 : ℝ)+(6321/100000 : ℝ)))^(8459/2048 : ℝ) := by
    rw [show (43269212702231193/43281250000000000 : ℝ)+(3043898885491/1357300000000000 : ℝ)*((9947/50000 : ℝ)+(6321/100000 : ℝ))=(10003097829770881/10000000000000000 : ℝ) by norm_num, show 1+(126900136531427293/100000000000000000000 : ℝ)+(556891125977389/50000000000000000000 : ℝ)=(100128013918783382071/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(126900136531427293/100000000000000000000 : ℝ) ≤ ((43269212702231193/43281250000000000 : ℝ)+2*(3043898885491/1357300000000000 : ℝ)*(9947/50000 : ℝ))^(8459/2048 : ℝ) := by
    rw [show (43269212702231193/43281250000000000 : ℝ)+2*(3043898885491/1357300000000000 : ℝ)*(9947/50000 : ℝ)=(2501535432164093/2500000000000000 : ℝ) by norm_num, show 1+2*(126900136531427293/100000000000000000000 : ℝ)=(50126900136531427293/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (43269212702231193/43281250000000000 : ℝ)*(X 1 0+X 2 0)+(3043898885491/1357300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (6321/100000 : ℝ)) (hi := (9947/50000 : ℝ)) (c := (43269212702231193/43281250000000000 : ℝ)) (alpha := (3043898885491/1357300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (43269212702231193/43281250000000000 : ℝ)*(X 0 1+X 2 1)+(3043898885491/1357300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (6321/100000 : ℝ)) (hi := (9947/50000 : ℝ)) (c := (43269212702231193/43281250000000000 : ℝ)) (alpha := (3043898885491/1357300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (43269212702231193/43281250000000000 : ℝ)*(X 0 2+X 1 2)+(3043898885491/1357300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8459/2048 : ℝ)) (lo := (6321/100000 : ℝ)) (hi := (9947/50000 : ℝ)) (c := (43269212702231193/43281250000000000 : ℝ)) (alpha := (3043898885491/1357300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-261908193/1250000000 : ℝ)*X 0 0+(2744296683/5000000000 : ℝ)*X 0 1+(5178297717/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5368679833/10000000000 : ℝ)*X 1 0+(-2255858769/10000000000 : ℝ)*X 1 1+(2589148977/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5368679781/10000000000 : ℝ)*X 2 0+(103565959/200000000 : ℝ)*X 2 1+(-1127929421/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2169529799/5000000000 : ℝ)*X 0 0+(403391193/1000000000 : ℝ)*X 0 1+(4666407761/10000000000 : ℝ)*X 0 2+(2169529799/5000000000 : ℝ)*X 1 0+(403391193/1000000000 : ℝ)*X 1 1+(4666407761/10000000000 : ℝ)*X 1 2+(2169529799/5000000000 : ℝ)*X 2 0+(403391193/1000000000 : ℝ)*X 2 1+(4666407761/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2095338919/10000000000 : ℝ)*X 0 0+(2590129213/5000000000 : ℝ)*X 0 1+(1371653647/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2644658221/5000000000 : ℝ)*X 1 0+(-1947541853/10000000000 : ℝ)*X 1 1+(548661463/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1057863311/2000000000 : ℝ)*X 2 0+(5486614749/10000000000 : ℝ)*X 2 1+(-973770767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1084802189/2500000000 : ℝ)*X 0 0+(4662411659/10000000000 : ℝ)*X 0 1+(100948611/250000000 : ℝ)*X 0 2+(1084802189/2500000000 : ℝ)*X 1 0+(4662411659/10000000000 : ℝ)*X 1 1+(100948611/250000000 : ℝ)*X 1 2+(1084802189/2500000000 : ℝ)*X 2 0+(4662411659/10000000000 : ℝ)*X 2 1+(100948611/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1267_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2231644631929028085146368053/212078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122548139/6250000000000 : ℝ)*(base19) + (1829359757/100000000000000 : ℝ)*(base23) + (53791613/100000000000000 : ℝ)*(lower2) + (145063491/50000000000000 : ℝ)*(upper3) + (14728899/10000000000000 : ℝ)*(upper5) + (2401921923559503/100000000000000 : ℝ)*(major0) + (2401921923559503/100000000000000 : ℝ)*(major1) + (2401921923559503/100000000000000 : ℝ)*(major2) + (1611379430131553/50000000000000 : ℝ)*(sp0) + (805695157713869/25000000000000 : ℝ)*(sp1) + (1611390381132971/50000000000000 : ℝ)*(sp2) + (158104871068091/10000000000000 : ℝ)*(sp3) + (23731362593/100000000000000 : ℝ)*(sp4) + (762128383/6250000000000 : ℝ)*(sp7) + (1581060904735037/100000000000000 : ℝ)*(f.failure) + (32227825916257/1000000000000 : ℝ)*(f.sum) + (52918540309029/8483125000000000000000000000 : ℝ)*base66 + (2265556364276168133/424156250000000000000000000000000 : ℝ)*base68 + (586312629958980633/424156250000000000000000000000000 : ℝ)*base70 + (4965983772759605633/424156250000000000000000000000000 : ℝ)*base72 + (315695653615947/67865000000000000000000000000 : ℝ)*base74 + (989286694131293133/424156250000000000000000000000000 : ℝ)*base76 + (309385736889668133/424156250000000000000000000000000 : ℝ)*base78 + (1144853047447355633/424156250000000000000000000000000 : ℝ)*base80 + (545674262142117/67865000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (204387/312500000000000000000 : ℝ)*base90 + (204387/312500000000000000000 : ℝ)*base92 + (204387/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1315021772497037658594564861/212078125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (163788249/10000000000000 : ℝ)*(base19) + (375657451/20000000000000 : ℝ)*(base23) + (41862679/100000000000000 : ℝ)*(upper2) + (56508959/25000000000000 : ℝ)*(upper3) + (118465241/100000000000000 : ℝ)*(upper5) + (2432769413705717/100000000000000 : ℝ)*(major0) + (2432769413705717/100000000000000 : ℝ)*(major1) + (2432769413705717/100000000000000 : ℝ)*(major2) + (17089999229/100000000000000 : ℝ)*(sp1) + (23189822343/100000000000000 : ℝ)*(sp2) + (816043102389473/25000000000000 : ℝ)*(sp4) + (3264153681676173/100000000000000 : ℝ)*(sp5) + (3264147341448293/100000000000000 : ℝ)*(sp6) + (1601366211165273/100000000000000 : ℝ)*(sp7) + (1601366211165273/100000000000000 : ℝ)*(f.failure) + (816043102389473/25000000000000 : ℝ)*(f.sum) + (140974330303447/67865000000000000000000000000 : ℝ)*base65 + (123686528585805463/424156250000000000000000000000000 : ℝ)*base67 + (3450188169659225787/424156250000000000000000000000000 : ℝ)*base70 + (881569038242805463/424156250000000000000000000000000 : ℝ)*base71 + (176209685034021/33932500000000000000000000000 : ℝ)*base73 + (998039073942975787/424156250000000000000000000000000 : ℝ)*base76 + (1305236543599836713/424156250000000000000000000000000 : ℝ)*base77 + (4344901271351586713/424156250000000000000000000000000 : ℝ)*base79 + (127858765663933/67865000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1486423/312500000000000000000 : ℝ)*base90 + (1486423/312500000000000000000 : ℝ)*base92 + (1486423/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1267_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9947/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (6321/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9599/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1267_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1267_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9599/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1267_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1267_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1267_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8459/2048 : ℝ) ≤ p) (hpb : p ≤ (2115/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (4747449/3125000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9599/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16159/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1267_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
