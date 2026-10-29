-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1450_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:59:33.400387+00:00
-- url     : https://prove2.me/submissions/2dada91b-a4c7-4884-914a-e47419fcad88

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
theorem support_rectangle_w1450_s3_0 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1953283957/10000000000 : ℝ)*x 0 + (5415213279/10000000000 : ℝ)*x 1 + (5239895781/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1953283957/10000000000 : ℝ)^2205 ≤ (11920031925719/100000000000000 : ℝ)^1693 := by
    have hnat : (1953283957 : ℕ)^2205*100000000000000^1693 ≤ 11920031925719^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953283957 10000000000 11920031925719 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415213279/10000000000 : ℝ)^2205 ≤ (8996738938931/20000000000000 : ℝ)^1693 := by
    have hnat : (5415213279 : ℕ)^2205*20000000000000^1693 ≤ 8996738938931^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415213279 10000000000 8996738938931 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239895781/10000000000 : ℝ)^2205 ≤ (172385093451/400000000000 : ℝ)^1693 := by
    have hnat : (5239895781 : ℕ)^2205*400000000000^1693 ≤ 172385093451^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239895781 10000000000 172385093451 400000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1953283957/10000000000 : ℝ), (5415213279/10000000000 : ℝ), (5239895781/10000000000 : ℝ)] ![(11920031925719/100000000000000 : ℝ), (8996738938931/20000000000000 : ℝ), (172385093451/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1953283957/10000000000 : ℝ)|^2205 ≤ (11920031925719/100000000000000 : ℝ)^1693
        have hw : |(-1953283957/10000000000 : ℝ)|=(1953283957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415213279/10000000000 : ℝ)|^2205 ≤ (8996738938931/20000000000000 : ℝ)^1693
        have hw : |(5415213279/10000000000 : ℝ)|=(5415213279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239895781/10000000000 : ℝ)|^2205 ≤ (172385093451/400000000000 : ℝ)^1693
        have hw : |(5239895781/10000000000 : ℝ)|=(5239895781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s3_1 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674483987/5000000000 : ℝ)*x 0 + (-12766743/62500000 : ℝ)*x 1 + (5239895689/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674483987/5000000000 : ℝ)^2205 ≤ (8853661916627/20000000000000 : ℝ)^1693 := by
    have hnat : (2674483987 : ℕ)^2205*20000000000000^1693 ≤ 8853661916627^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674483987 5000000000 8853661916627 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12766743/62500000 : ℝ)^2205 ≤ (2527083605081/20000000000000 : ℝ)^1693 := by
    have hnat : (12766743 : ℕ)^2205*20000000000000^1693 ≤ 2527083605081^1693*62500000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12766743 62500000 2527083605081 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5239895689/10000000000 : ℝ)^2205 ≤ (172385089509/400000000000 : ℝ)^1693 := by
    have hnat : (5239895689 : ℕ)^2205*400000000000^1693 ≤ 172385089509^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239895689 10000000000 172385089509 400000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674483987/5000000000 : ℝ), (-12766743/62500000 : ℝ), (5239895689/10000000000 : ℝ)] ![(8853661916627/20000000000000 : ℝ), (2527083605081/20000000000000 : ℝ), (172385089509/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674483987/5000000000 : ℝ)|^2205 ≤ (8853661916627/20000000000000 : ℝ)^1693
        have hw : |(2674483987/5000000000 : ℝ)|=(2674483987/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-12766743/62500000 : ℝ)|^2205 ≤ (2527083605081/20000000000000 : ℝ)^1693
        have hw : |(-12766743/62500000 : ℝ)|=(12766743/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5239895689/10000000000 : ℝ)|^2205 ≤ (172385089509/400000000000 : ℝ)^1693
        have hw : |(5239895689/10000000000 : ℝ)|=(5239895689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s3_2 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2674483759/5000000000 : ℝ)*x 0 + (5239896103/10000000000 : ℝ)*x 1 + (-2042678939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674483759/5000000000 : ℝ)^2205 ≤ (8853660933591/20000000000000 : ℝ)^1693 := by
    have hnat : (2674483759 : ℕ)^2205*20000000000000^1693 ≤ 8853660933591^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674483759 5000000000 8853660933591 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5239896103/10000000000 : ℝ)^2205 ≤ (43096276811999/100000000000000 : ℝ)^1693 := by
    have hnat : (5239896103 : ℕ)^2205*100000000000000^1693 ≤ 43096276811999^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239896103 10000000000 43096276811999 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2042678939/10000000000 : ℝ)^2205 ≤ (3158854625183/25000000000000 : ℝ)^1693 := by
    have hnat : (2042678939 : ℕ)^2205*25000000000000^1693 ≤ 3158854625183^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2042678939 10000000000 3158854625183 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674483759/5000000000 : ℝ), (5239896103/10000000000 : ℝ), (-2042678939/10000000000 : ℝ)] ![(8853660933591/20000000000000 : ℝ), (43096276811999/100000000000000 : ℝ), (3158854625183/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674483759/5000000000 : ℝ)|^2205 ≤ (8853660933591/20000000000000 : ℝ)^1693
        have hw : |(2674483759/5000000000 : ℝ)|=(2674483759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5239896103/10000000000 : ℝ)|^2205 ≤ (43096276811999/100000000000000 : ℝ)^1693
        have hw : |(5239896103/10000000000 : ℝ)|=(5239896103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2042678939/10000000000 : ℝ)|^2205 ≤ (3158854625183/25000000000000 : ℝ)^1693
        have hw : |(-2042678939/10000000000 : ℝ)|=(2042678939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s3_3 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4298577963/10000000000 : ℝ)*x 0 + (256954231/625000000 : ℝ)*x 1 + (4493458043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4298577963/10000000000 : ℝ)^2205 ≤ (2081202202893/6250000000000 : ℝ)^1693 := by
    have hnat : (4298577963 : ℕ)^2205*6250000000000^1693 ≤ 2081202202893^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4298577963 10000000000 2081202202893 6250000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (256954231/625000000 : ℝ)^2205 ≤ (7855496549687/25000000000000 : ℝ)^1693 := by
    have hnat : (256954231 : ℕ)^2205*25000000000000^1693 ≤ 7855496549687^1693*625000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256954231 625000000 7855496549687 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4493458043/10000000000 : ℝ)^2205 ≤ (35278778540011/100000000000000 : ℝ)^1693 := by
    have hnat : (4493458043 : ℕ)^2205*100000000000000^1693 ≤ 35278778540011^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493458043 10000000000 35278778540011 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4298577963/10000000000 : ℝ), (256954231/625000000 : ℝ), (4493458043/10000000000 : ℝ)] ![(2081202202893/6250000000000 : ℝ), (7855496549687/25000000000000 : ℝ), (35278778540011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4298577963/10000000000 : ℝ)|^2205 ≤ (2081202202893/6250000000000 : ℝ)^1693
        have hw : |(4298577963/10000000000 : ℝ)|=(4298577963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(256954231/625000000 : ℝ)|^2205 ≤ (7855496549687/25000000000000 : ℝ)^1693
        have hw : |(256954231/625000000 : ℝ)|=(256954231/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4493458043/10000000000 : ℝ)|^2205 ≤ (35278778540011/100000000000000 : ℝ)^1693
        have hw : |(4493458043/10000000000 : ℝ)|=(4493458043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s3_4 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1953298407/10000000000 : ℝ)*x 0 + (5240590669/10000000000 : ℝ)*x 1 + (5414514631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1953298407/10000000000 : ℝ)^2205 ≤ (2384029355197/20000000000000 : ℝ)^1693 := by
    have hnat : (1953298407 : ℕ)^2205*20000000000000^1693 ≤ 2384029355197^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1953298407 10000000000 2384029355197 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240590669/10000000000 : ℝ)^2205 ≤ (336747790003/781250000000 : ℝ)^1693 := by
    have hnat : (5240590669 : ℕ)^2205*781250000000^1693 ≤ 336747790003^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240590669 10000000000 336747790003 781250000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5414514631/10000000000 : ℝ)^2205 ≤ (2248806804927/5000000000000 : ℝ)^1693 := by
    have hnat : (5414514631 : ℕ)^2205*5000000000000^1693 ≤ 2248806804927^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414514631 10000000000 2248806804927 5000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1953298407/10000000000 : ℝ), (5240590669/10000000000 : ℝ), (5414514631/10000000000 : ℝ)] ![(2384029355197/20000000000000 : ℝ), (336747790003/781250000000 : ℝ), (2248806804927/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1953298407/10000000000 : ℝ)|^2205 ≤ (2384029355197/20000000000000 : ℝ)^1693
        have hw : |(-1953298407/10000000000 : ℝ)|=(1953298407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240590669/10000000000 : ℝ)|^2205 ≤ (336747790003/781250000000 : ℝ)^1693
        have hw : |(5240590669/10000000000 : ℝ)|=(5240590669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5414514631/10000000000 : ℝ)|^2205 ≤ (2248806804927/5000000000000 : ℝ)^1693
        have hw : |(5414514631/10000000000 : ℝ)|=(5414514631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s3_5 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1325824689/2500000000 : ℝ)*x 0 + (-1868060509/10000000000 : ℝ)*x 1 + (1082902919/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325824689/2500000000 : ℝ)^2205 ≤ (8755336458417/20000000000000 : ℝ)^1693 := by
    have hnat : (1325824689 : ℕ)^2205*20000000000000^1693 ≤ 8755336458417^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325824689 2500000000 8755336458417 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1868060509/10000000000 : ℝ)^2205 ≤ (11247181981313/100000000000000 : ℝ)^1693 := by
    have hnat : (1868060509 : ℕ)^2205*100000000000000^1693 ≤ 11247181981313^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868060509 10000000000 11247181981313 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082902919/2000000000 : ℝ)^2205 ≤ (11244033927267/25000000000000 : ℝ)^1693 := by
    have hnat : (1082902919 : ℕ)^2205*25000000000000^1693 ≤ 11244033927267^1693*2000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082902919 2000000000 11244033927267 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325824689/2500000000 : ℝ), (-1868060509/10000000000 : ℝ), (1082902919/2000000000 : ℝ)] ![(8755336458417/20000000000000 : ℝ), (11247181981313/100000000000000 : ℝ), (11244033927267/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325824689/2500000000 : ℝ)|^2205 ≤ (8755336458417/20000000000000 : ℝ)^1693
        have hw : |(1325824689/2500000000 : ℝ)|=(1325824689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1868060509/10000000000 : ℝ)|^2205 ≤ (11247181981313/100000000000000 : ℝ)^1693
        have hw : |(-1868060509/10000000000 : ℝ)|=(1868060509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082902919/2000000000 : ℝ)|^2205 ≤ (11244033927267/25000000000000 : ℝ)^1693
        have hw : |(1082902919/2000000000 : ℝ)|=(1082902919/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s3_6 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1325824401/2500000000 : ℝ)*x 0 + (5414515507/10000000000 : ℝ)*x 1 + (-1868060831/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325824401/2500000000 : ℝ)^2205 ≤ (43776669906947/100000000000000 : ℝ)^1693 := by
    have hnat : (1325824401 : ℕ)^2205*100000000000000^1693 ≤ 43776669906947^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325824401 2500000000 43776669906947 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414515507/10000000000 : ℝ)^2205 ≤ (44976145575703/100000000000000 : ℝ)^1693 := by
    have hnat : (5414515507 : ℕ)^2205*100000000000000^1693 ≤ 44976145575703^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414515507 10000000000 44976145575703 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1868060831/10000000000 : ℝ)^2205 ≤ (11247184506307/100000000000000 : ℝ)^1693 := by
    have hnat : (1868060831 : ℕ)^2205*100000000000000^1693 ≤ 11247184506307^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868060831 10000000000 11247184506307 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325824401/2500000000 : ℝ), (5414515507/10000000000 : ℝ), (-1868060831/10000000000 : ℝ)] ![(43776669906947/100000000000000 : ℝ), (44976145575703/100000000000000 : ℝ), (11247184506307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325824401/2500000000 : ℝ)|^2205 ≤ (43776669906947/100000000000000 : ℝ)^1693
        have hw : |(1325824401/2500000000 : ℝ)|=(1325824401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414515507/10000000000 : ℝ)|^2205 ≤ (44976145575703/100000000000000 : ℝ)^1693
        have hw : |(5414515507/10000000000 : ℝ)|=(5414515507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1868060831/10000000000 : ℝ)|^2205 ≤ (11247184506307/100000000000000 : ℝ)^1693
        have hw : |(-1868060831/10000000000 : ℝ)|=(1868060831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s3_7 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074652263/2500000000 : ℝ)*x 0 + (2245971973/5000000000 : ℝ)*x 1 + (4112791373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074652263/2500000000 : ℝ)^2205 ≤ (8324887228229/25000000000000 : ℝ)^1693 := by
    have hnat : (1074652263 : ℕ)^2205*25000000000000^1693 ≤ 8324887228229^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074652263 2500000000 8324887228229 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2245971973/5000000000 : ℝ)^2205 ≤ (17631648466239/50000000000000 : ℝ)^1693 := by
    have hnat : (2245971973 : ℕ)^2205*50000000000000^1693 ≤ 17631648466239^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2245971973 5000000000 17631648466239 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4112791373/10000000000 : ℝ)^2205 ≤ (15718577072141/50000000000000 : ℝ)^1693 := by
    have hnat : (4112791373 : ℕ)^2205*50000000000000^1693 ≤ 15718577072141^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4112791373 10000000000 15718577072141 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074652263/2500000000 : ℝ), (2245971973/5000000000 : ℝ), (4112791373/10000000000 : ℝ)] ![(8324887228229/25000000000000 : ℝ), (17631648466239/50000000000000 : ℝ), (15718577072141/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074652263/2500000000 : ℝ)|^2205 ≤ (8324887228229/25000000000000 : ℝ)^1693
        have hw : |(1074652263/2500000000 : ℝ)|=(1074652263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2245971973/5000000000 : ℝ)|^2205 ≤ (17631648466239/50000000000000 : ℝ)^1693
        have hw : |(2245971973/5000000000 : ℝ)|=(2245971973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4112791373/10000000000 : ℝ)|^2205 ≤ (15718577072141/50000000000000 : ℝ)^1693
        have hw : |(4112791373/10000000000 : ℝ)|=(4112791373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1450_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11223/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14937/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15737/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10477/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15737/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10477/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15737/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10477/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10477/100000 : ℝ) ^ (4409/1024 : ℝ) ≤ (6046017774765199/100000000000000000000 : ℝ) := by
    have hpowers : (10477/100000 : ℝ)^4409 ≤ (6046017774765199/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10477 : ℕ)^4409*100000000000000000000^1024 ≤ 6046017774765199^1024*100000^4409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10477 100000 6046017774765199 100000000000000000000 4409 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10477/100000 : ℝ)) (X := (6046017774765199/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15737/100000 : ℝ) ^ (4409/1024 : ℝ) ≤ (4356379356933441/12500000000000000000 : ℝ) := by
    have hpowers : (15737/100000 : ℝ)^4409 ≤ (4356379356933441/12500000000000000000 : ℝ)^1024 := by
      have hnat : (15737 : ℕ)^4409*12500000000000000000^1024 ≤ 4356379356933441^1024*100000^4409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15737 100000 4356379356933441 12500000000000000000 4409 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15737/100000 : ℝ)) (X := (4356379356933441/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006046017774765199/50000000000000000000 : ℝ) ≤ (2000056165432899/2000000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (50006046017774765199/50000000000000000000 : ℝ)^1024 ≤ (2000056165432899/2000000000000000 : ℝ)^4409 := by
      have hnat : (50006046017774765199 : ℕ)^1024*2000000000000000^4409 ≤ 2000056165432899^4409*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006046017774765199 50000000000000000000 2000056165432899 2000000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000056165432899/2000000000000000 : ℝ)) (X := (50006046017774765199/50000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100040897052630232727/100000000000000000000 : ℝ) ≤ (250023742350209/250000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (100040897052630232727/100000000000000000000 : ℝ)^1024 ≤ (250023742350209/250000000000000 : ℝ)^4409 := by
      have hnat : (100040897052630232727 : ℕ)^1024*250000000000000^4409 ≤ 250023742350209^4409*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100040897052630232727 100000000000000000000 250023742350209 250000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250023742350209/250000000000000 : ℝ)) (X := (100040897052630232727/100000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6254356379356933441/6250000000000000000 : ℝ) ≤ (400064742434089/400000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (6254356379356933441/6250000000000000000 : ℝ)^1024 ≤ (400064742434089/400000000000000 : ℝ)^4409 := by
      have hnat : (6254356379356933441 : ℕ)^1024*400000000000000^4409 ≤ 400064742434089^4409*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6254356379356933441 6250000000000000000 400064742434089 400000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400064742434089/400000000000000 : ℝ)) (X := (6254356379356933441/6250000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6046017774765199/100000000000000000000 : ℝ) ≤ ((5258746171503889649/5260000000000000000 : ℝ)+2*(133773368773/105200000000000 : ℝ)*(10477/100000 : ℝ))^(4409/1024 : ℝ) := by
    rw [show (5258746171503889649/5260000000000000000 : ℝ)+2*(133773368773/105200000000000 : ℝ)*(10477/100000 : ℝ)=(2000056165432899/2000000000000000 : ℝ) by norm_num, show 1+2*(6046017774765199/100000000000000000000 : ℝ)=(50006046017774765199/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4356379356933441/12500000000000000000 : ℝ)+(6046017774765199/100000000000000000000 : ℝ) ≤ ((5258746171503889649/5260000000000000000 : ℝ)+(133773368773/105200000000000 : ℝ)*((15737/100000 : ℝ)+(10477/100000 : ℝ)))^(4409/1024 : ℝ) := by
    rw [show (5258746171503889649/5260000000000000000 : ℝ)+(133773368773/105200000000000 : ℝ)*((15737/100000 : ℝ)+(10477/100000 : ℝ))=(250023742350209/250000000000000 : ℝ) by norm_num, show 1+(4356379356933441/12500000000000000000 : ℝ)+(6046017774765199/100000000000000000000 : ℝ)=(100040897052630232727/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4356379356933441/12500000000000000000 : ℝ) ≤ ((5258746171503889649/5260000000000000000 : ℝ)+2*(133773368773/105200000000000 : ℝ)*(15737/100000 : ℝ))^(4409/1024 : ℝ) := by
    rw [show (5258746171503889649/5260000000000000000 : ℝ)+2*(133773368773/105200000000000 : ℝ)*(15737/100000 : ℝ)=(400064742434089/400000000000000 : ℝ) by norm_num, show 1+2*(4356379356933441/12500000000000000000 : ℝ)=(6254356379356933441/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5258746171503889649/5260000000000000000 : ℝ)*(X 1 0+X 2 0)+(133773368773/105200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (10477/100000 : ℝ)) (hi := (15737/100000 : ℝ)) (c := (5258746171503889649/5260000000000000000 : ℝ)) (alpha := (133773368773/105200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5258746171503889649/5260000000000000000 : ℝ)*(X 0 1+X 2 1)+(133773368773/105200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (10477/100000 : ℝ)) (hi := (15737/100000 : ℝ)) (c := (5258746171503889649/5260000000000000000 : ℝ)) (alpha := (133773368773/105200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5258746171503889649/5260000000000000000 : ℝ)*(X 0 2+X 1 2)+(133773368773/105200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (10477/100000 : ℝ)) (hi := (15737/100000 : ℝ)) (c := (5258746171503889649/5260000000000000000 : ℝ)) (alpha := (133773368773/105200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1953283957/10000000000 : ℝ)*X 0 0+(5415213279/10000000000 : ℝ)*X 0 1+(5239895781/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2674483987/5000000000 : ℝ)*X 1 0+(-12766743/62500000 : ℝ)*X 1 1+(5239895689/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674483759/5000000000 : ℝ)*X 2 0+(5239896103/10000000000 : ℝ)*X 2 1+(-2042678939/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4298577963/10000000000 : ℝ)*X 0 0+(256954231/625000000 : ℝ)*X 0 1+(4493458043/10000000000 : ℝ)*X 0 2+(4298577963/10000000000 : ℝ)*X 1 0+(256954231/625000000 : ℝ)*X 1 1+(4493458043/10000000000 : ℝ)*X 1 2+(4298577963/10000000000 : ℝ)*X 2 0+(256954231/625000000 : ℝ)*X 2 1+(4493458043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1953298407/10000000000 : ℝ)*X 0 0+(5240590669/10000000000 : ℝ)*X 0 1+(5414514631/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325824689/2500000000 : ℝ)*X 1 0+(-1868060509/10000000000 : ℝ)*X 1 1+(1082902919/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1325824401/2500000000 : ℝ)*X 2 0+(5414515507/10000000000 : ℝ)*X 2 1+(-1868060831/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1074652263/2500000000 : ℝ)*X 0 0+(2245971973/5000000000 : ℝ)*X 0 1+(4112791373/10000000000 : ℝ)*X 0 2+(1074652263/2500000000 : ℝ)*X 1 0+(2245971973/5000000000 : ℝ)*X 1 1+(4112791373/10000000000 : ℝ)*X 1 2+(1074652263/2500000000 : ℝ)*X 2 0+(2245971973/5000000000 : ℝ)*X 2 1+(4112791373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (24702291071504883935543991/3287500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (676831789/50000000000000 : ℝ)*(base19) + (813817231/100000000000000 : ℝ)*(base23) + (3076773/3125000000000 : ℝ)*(lower2) + (191960103/100000000000000 : ℝ)*(upper3) + (69796679/100000000000000 : ℝ)*(lower4) + (104006434336547/2500000000000 : ℝ)*(major0) + (104006434336547/2500000000000 : ℝ)*(major1) + (104006434336547/2500000000000 : ℝ)*(major2) + (2851984844734443/50000000000000 : ℝ)*(sp0) + (570399123832407/10000000000000 : ℝ)*(sp1) + (2851995889085209/50000000000000 : ℝ)*(sp2) + (654127226945777/25000000000000 : ℝ)*(sp3) + (22902518763/100000000000000 : ℝ)*(sp4) + (2599337233/20000000000000 : ℝ)*(sp7) + (1308260952234637/50000000000000 : ℝ)*(f.failure) + (5703992591987649/100000000000000 : ℝ)*(f.sum) + (510085989421/263000000000000000000000000 : ℝ)*base66 + (43004779985402003/13150000000000000000000000000000 : ℝ)*base67 + (36638369112052003/13150000000000000000000000000000 : ℝ)*base69 + (42695717310652003/13150000000000000000000000000000 : ℝ)*base71 + (1716017231/8218750000000000000000000 : ℝ)*base74 + (153933176147402003/13150000000000000000000000000000 : ℝ)*base75 + (29460283412947997/13150000000000000000000000000000 : ℝ)*base78 + (307999353404452003/13150000000000000000000000000000 : ℝ)*base79 + (287718317981/263000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (4828197/1250000000000000000000 : ℝ)*base89 + (4828197/1250000000000000000000 : ℝ)*base91 + (4828197/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (244524497586724755448007331/13150000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (509645683/100000000000000 : ℝ)*(base19) + (134137917/100000000000000 : ℝ)*(upper2) + (20303877/20000000000000 : ℝ)*(upper3) + (133430281/50000000000000 : ℝ)*(lower4) + (136516277/100000000000000 : ℝ)*(upper5) + (209676906051327/5000000000000 : ℝ)*(major0) + (209676906051327/5000000000000 : ℝ)*(major1) + (209676906051327/5000000000000 : ℝ)*(major2) + (6384145979/100000000000000 : ℝ)*(sp1) + (4430395097/100000000000000 : ℝ)*(sp2) + (5749622367310909/100000000000000 : ℝ)*(sp4) + (5749615473519247/100000000000000 : ℝ)*(sp5) + (5749617936915811/100000000000000 : ℝ)*(sp6) + (2637453254908197/100000000000000 : ℝ)*(sp7) + (2637453254908197/100000000000000 : ℝ)*(f.failure) + (5749622367310909/100000000000000 : ℝ)*(f.sum) + (1438351396717/65750000000000000000000000 : ℝ)*base65 + (186142243876335777/26300000000000000000000000000000 : ℝ)*base68 + (164761282948564223/26300000000000000000000000000000 : ℝ)*base69 + (46549661397964223/26300000000000000000000000000000 : ℝ)*base71 + (252251062737/131500000000000000000000000 : ℝ)*base73 + (183242689631464223/26300000000000000000000000000000 : ℝ)*base75 + (1550477215442364223/26300000000000000000000000000000 : ℝ)*base77 + (175787409112435777/26300000000000000000000000000000 : ℝ)*base80 + (33423627129/13150000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3325443/2500000000000000000000 : ℝ)*base90 + (3325443/2500000000000000000000 : ℝ)*base92 + (3325443/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1450_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14937/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1450_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1450_s4_0 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-977041903/5000000000 : ℝ)*x 0 + (5408320747/10000000000 : ℝ)*x 1 + (1049252247/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (977041903/5000000000 : ℝ)^2205 ≤ (596319480213/5000000000000 : ℝ)^1693 := by
    have hnat : (977041903 : ℕ)^2205*5000000000000^1693 ≤ 596319480213^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      977041903 5000000000 596319480213 5000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5408320747/10000000000 : ℝ)^2205 ≤ (22454569024087/50000000000000 : ℝ)^1693 := by
    have hnat : (5408320747 : ℕ)^2205*50000000000000^1693 ≤ 22454569024087^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5408320747 10000000000 22454569024087 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049252247/2000000000 : ℝ)^2205 ≤ (43164472335697/100000000000000 : ℝ)^1693 := by
    have hnat : (1049252247 : ℕ)^2205*100000000000000^1693 ≤ 43164472335697^1693*2000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049252247 2000000000 43164472335697 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-977041903/5000000000 : ℝ), (5408320747/10000000000 : ℝ), (1049252247/2000000000 : ℝ)] ![(596319480213/5000000000000 : ℝ), (22454569024087/50000000000000 : ℝ), (43164472335697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-977041903/5000000000 : ℝ)|^2205 ≤ (596319480213/5000000000000 : ℝ)^1693
        have hw : |(-977041903/5000000000 : ℝ)|=(977041903/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5408320747/10000000000 : ℝ)|^2205 ≤ (22454569024087/50000000000000 : ℝ)^1693
        have hw : |(5408320747/10000000000 : ℝ)|=(5408320747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049252247/2000000000 : ℝ)|^2205 ≤ (43164472335697/100000000000000 : ℝ)^1693
        have hw : |(1049252247/2000000000 : ℝ)|=(1049252247/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s4_1 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (334199009/625000000 : ℝ)*x 0 + (-2036597307/10000000000 : ℝ)*x 1 + (2623130633/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334199009/625000000 : ℝ)^2205 ≤ (44249082821709/100000000000000 : ℝ)^1693 := by
    have hnat : (334199009 : ℕ)^2205*100000000000000^1693 ≤ 44249082821709^1693*625000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334199009 625000000 44249082821709 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2036597307/10000000000 : ℝ)^2205 ≤ (1573305562337/12500000000000 : ℝ)^1693 := by
    have hnat : (2036597307 : ℕ)^2205*12500000000000^1693 ≤ 1573305562337^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036597307 10000000000 1573305562337 12500000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2623130633/5000000000 : ℝ)^2205 ≤ (43164472667889/100000000000000 : ℝ)^1693 := by
    have hnat : (2623130633 : ℕ)^2205*100000000000000^1693 ≤ 43164472667889^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623130633 5000000000 43164472667889 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334199009/625000000 : ℝ), (-2036597307/10000000000 : ℝ), (2623130633/5000000000 : ℝ)] ![(44249082821709/100000000000000 : ℝ), (1573305562337/12500000000000 : ℝ), (43164472667889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334199009/625000000 : ℝ)|^2205 ≤ (44249082821709/100000000000000 : ℝ)^1693
        have hw : |(334199009/625000000 : ℝ)|=(334199009/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2036597307/10000000000 : ℝ)|^2205 ≤ (1573305562337/12500000000000 : ℝ)^1693
        have hw : |(-2036597307/10000000000 : ℝ)|=(2036597307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2623130633/5000000000 : ℝ)|^2205 ≤ (43164472667889/100000000000000 : ℝ)^1693
        have hw : |(2623130633/5000000000 : ℝ)|=(2623130633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s4_2 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1069436837/2000000000 : ℝ)*x 0 + (131156531/250000000 : ℝ)*x 1 + (-2036597287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069436837/2000000000 : ℝ)^2205 ≤ (44249083263599/100000000000000 : ℝ)^1693 := by
    have hnat : (1069436837 : ℕ)^2205*100000000000000^1693 ≤ 44249083263599^1693*2000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069436837 2000000000 44249083263599 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131156531/250000000 : ℝ)^2205 ≤ (10791118097319/25000000000000 : ℝ)^1693 := by
    have hnat : (131156531 : ℕ)^2205*25000000000000^1693 ≤ 10791118097319^1693*250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131156531 250000000 10791118097319 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2036597287/10000000000 : ℝ)^2205 ≤ (6293222168857/50000000000000 : ℝ)^1693 := by
    have hnat : (2036597287 : ℕ)^2205*50000000000000^1693 ≤ 6293222168857^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036597287 10000000000 6293222168857 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069436837/2000000000 : ℝ), (131156531/250000000 : ℝ), (-2036597287/10000000000 : ℝ)] ![(44249083263599/100000000000000 : ℝ), (10791118097319/25000000000000 : ℝ), (6293222168857/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069436837/2000000000 : ℝ)|^2205 ≤ (44249083263599/100000000000000 : ℝ)^1693
        have hw : |(1069436837/2000000000 : ℝ)|=(1069436837/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131156531/250000000 : ℝ)|^2205 ≤ (10791118097319/25000000000000 : ℝ)^1693
        have hw : |(131156531/250000000 : ℝ)|=(131156531/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2036597287/10000000000 : ℝ)|^2205 ≤ (6293222168857/50000000000000 : ℝ)^1693
        have hw : |(-2036597287/10000000000 : ℝ)|=(2036597287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s4_3 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2149534571/5000000000 : ℝ)*x 0 + (825132049/2000000000 : ℝ)*x 1 + (559868513/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149534571/5000000000 : ℝ)^2205 ≤ (2081511936549/6250000000000 : ℝ)^1693 := by
    have hnat : (2149534571 : ℕ)^2205*6250000000000^1693 ≤ 2081511936549^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149534571 5000000000 2081511936549 6250000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (825132049/2000000000 : ℝ)^2205 ≤ (31565329326777/100000000000000 : ℝ)^1693 := by
    have hnat : (825132049 : ℕ)^2205*100000000000000^1693 ≤ 31565329326777^1693*2000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      825132049 2000000000 31565329326777 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (559868513/1250000000 : ℝ)^2205 ≤ (35130479683111/100000000000000 : ℝ)^1693 := by
    have hnat : (559868513 : ℕ)^2205*100000000000000^1693 ≤ 35130479683111^1693*1250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559868513 1250000000 35130479683111 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2149534571/5000000000 : ℝ), (825132049/2000000000 : ℝ), (559868513/1250000000 : ℝ)] ![(2081511936549/6250000000000 : ℝ), (31565329326777/100000000000000 : ℝ), (35130479683111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2149534571/5000000000 : ℝ)|^2205 ≤ (2081511936549/6250000000000 : ℝ)^1693
        have hw : |(2149534571/5000000000 : ℝ)|=(2149534571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(825132049/2000000000 : ℝ)|^2205 ≤ (31565329326777/100000000000000 : ℝ)^1693
        have hw : |(825132049/2000000000 : ℝ)|=(825132049/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(559868513/1250000000 : ℝ)|^2205 ≤ (35130479683111/100000000000000 : ℝ)^1693
        have hw : |(559868513/1250000000 : ℝ)|=(559868513/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s4_4 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1954095311/10000000000 : ℝ)*x 0 + (5246855161/10000000000 : ℝ)*x 1 + (675965473/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1954095311/10000000000 : ℝ)^2205 ≤ (2981620264657/25000000000000 : ℝ)^1693 := by
    have hnat : (1954095311 : ℕ)^2205*25000000000000^1693 ≤ 2981620264657^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954095311 10000000000 2981620264657 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5246855161/10000000000 : ℝ)^2205 ≤ (863416737781/2000000000000 : ℝ)^1693 := by
    have hnat : (5246855161 : ℕ)^2205*2000000000000^1693 ≤ 863416737781^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246855161 10000000000 863416737781 2000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (675965473/1250000000 : ℝ)^2205 ≤ (8980536407973/20000000000000 : ℝ)^1693 := by
    have hnat : (675965473 : ℕ)^2205*20000000000000^1693 ≤ 8980536407973^1693*1250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675965473 1250000000 8980536407973 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1954095311/10000000000 : ℝ), (5246855161/10000000000 : ℝ), (675965473/1250000000 : ℝ)] ![(2981620264657/25000000000000 : ℝ), (863416737781/2000000000000 : ℝ), (8980536407973/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1954095311/10000000000 : ℝ)|^2205 ≤ (2981620264657/25000000000000 : ℝ)^1693
        have hw : |(-1954095311/10000000000 : ℝ)|=(1954095311/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5246855161/10000000000 : ℝ)|^2205 ≤ (863416737781/2000000000000 : ℝ)^1693
        have hw : |(5246855161/10000000000 : ℝ)|=(5246855161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(675965473/1250000000 : ℝ)|^2205 ≤ (8980536407973/20000000000000 : ℝ)^1693
        have hw : |(675965473/1250000000 : ℝ)|=(675965473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s4_5 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326242027/2500000000 : ℝ)*x 0 + (-937567431/5000000000 : ℝ)*x 1 + (1081544751/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326242027/2500000000 : ℝ)^2205 ≤ (43794630329989/100000000000000 : ℝ)^1693 := by
    have hnat : (1326242027 : ℕ)^2205*100000000000000^1693 ≤ 43794630329989^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326242027 2500000000 43794630329989 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (937567431/5000000000 : ℝ)^2205 ≤ (11302687932329/100000000000000 : ℝ)^1693 := by
    have hnat : (937567431 : ℕ)^2205*100000000000000^1693 ≤ 11302687932329^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      937567431 5000000000 11302687932329 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081544751/2000000000 : ℝ)^2205 ≤ (22451340863121/50000000000000 : ℝ)^1693 := by
    have hnat : (1081544751 : ℕ)^2205*50000000000000^1693 ≤ 22451340863121^1693*2000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081544751 2000000000 22451340863121 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326242027/2500000000 : ℝ), (-937567431/5000000000 : ℝ), (1081544751/2000000000 : ℝ)] ![(43794630329989/100000000000000 : ℝ), (11302687932329/100000000000000 : ℝ), (22451340863121/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326242027/2500000000 : ℝ)|^2205 ≤ (43794630329989/100000000000000 : ℝ)^1693
        have hw : |(1326242027/2500000000 : ℝ)|=(1326242027/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-937567431/5000000000 : ℝ)|^2205 ≤ (11302687932329/100000000000000 : ℝ)^1693
        have hw : |(-937567431/5000000000 : ℝ)|=(937567431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081544751/2000000000 : ℝ)|^2205 ≤ (22451340863121/50000000000000 : ℝ)^1693
        have hw : |(1081544751/2000000000 : ℝ)|=(1081544751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s4_6 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1060993633/2000000000 : ℝ)*x 0 + (675965467/1250000000 : ℝ)*x 1 + (-187513481/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060993633/2000000000 : ℝ)^2205 ≤ (21897315471427/50000000000000 : ℝ)^1693 := by
    have hnat : (1060993633 : ℕ)^2205*50000000000000^1693 ≤ 21897315471427^1693*2000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060993633 2000000000 21897315471427 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (675965467/1250000000 : ℝ)^2205 ≤ (8980536304153/20000000000000 : ℝ)^1693 := by
    have hnat : (675965467 : ℕ)^2205*20000000000000^1693 ≤ 8980536304153^1693*1250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      675965467 1250000000 8980536304153 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (187513481/1000000000 : ℝ)^2205 ≤ (113026875241/1000000000000 : ℝ)^1693 := by
    have hnat : (187513481 : ℕ)^2205*1000000000000^1693 ≤ 113026875241^1693*1000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      187513481 1000000000 113026875241 1000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060993633/2000000000 : ℝ), (675965467/1250000000 : ℝ), (-187513481/1000000000 : ℝ)] ![(21897315471427/50000000000000 : ℝ), (8980536304153/20000000000000 : ℝ), (113026875241/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060993633/2000000000 : ℝ)|^2205 ≤ (21897315471427/50000000000000 : ℝ)^1693
        have hw : |(1060993633/2000000000 : ℝ)|=(1060993633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(675965467/1250000000 : ℝ)|^2205 ≤ (8980536304153/20000000000000 : ℝ)^1693
        have hw : |(675965467/1250000000 : ℝ)|=(675965467/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-187513481/1000000000 : ℝ)|^2205 ≤ (113026875241/1000000000000 : ℝ)^1693
        have hw : |(-187513481/1000000000 : ℝ)|=(187513481/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s4_7 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4299094747/10000000000 : ℝ)*x 0 + (559706667/1250000000 : ℝ)*x 1 + (4126961541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299094747/10000000000 : ℝ)^2205 ≤ (33304449330501/100000000000000 : ℝ)^1693 := by
    have hnat : (4299094747 : ℕ)^2205*100000000000000^1693 ≤ 33304449330501^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299094747 10000000000 33304449330501 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559706667/1250000000 : ℝ)^2205 ≤ (1404690142283/4000000000000 : ℝ)^1693 := by
    have hnat : (559706667 : ℕ)^2205*4000000000000^1693 ≤ 1404690142283^1693*1250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559706667 1250000000 1404690142283 4000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4126961541/10000000000 : ℝ)^2205 ≤ (31578297096993/100000000000000 : ℝ)^1693 := by
    have hnat : (4126961541 : ℕ)^2205*100000000000000^1693 ≤ 31578297096993^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126961541 10000000000 31578297096993 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299094747/10000000000 : ℝ), (559706667/1250000000 : ℝ), (4126961541/10000000000 : ℝ)] ![(33304449330501/100000000000000 : ℝ), (1404690142283/4000000000000 : ℝ), (31578297096993/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299094747/10000000000 : ℝ)|^2205 ≤ (33304449330501/100000000000000 : ℝ)^1693
        have hw : |(4299094747/10000000000 : ℝ)|=(4299094747/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559706667/1250000000 : ℝ)|^2205 ≤ (1404690142283/4000000000000 : ℝ)^1693
        have hw : |(559706667/1250000000 : ℝ)|=(559706667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4126961541/10000000000 : ℝ)|^2205 ≤ (31578297096993/100000000000000 : ℝ)^1693
        have hw : |(4126961541/10000000000 : ℝ)|=(4126961541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1450_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11359/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1849/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14937/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14937/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11223/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14937/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14937/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11223/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14937/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14937/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11223/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11223/100000 : ℝ) ^ (4409/1024 : ℝ) ≤ (1625991586312233/20000000000000000000 : ℝ) := by
    have hpowers : (11223/100000 : ℝ)^4409 ≤ (1625991586312233/20000000000000000000 : ℝ)^1024 := by
      have hnat : (11223 : ℕ)^4409*20000000000000000000^1024 ≤ 1625991586312233^1024*100000^4409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11223 100000 1625991586312233 20000000000000000000 4409 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11223/100000 : ℝ)) (X := (1625991586312233/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14937/100000 : ℝ) ^ (4409/1024 : ℝ) ≤ (13919560366599769/50000000000000000000 : ℝ) := by
    have hpowers : (14937/100000 : ℝ)^4409 ≤ (13919560366599769/50000000000000000000 : ℝ)^1024 := by
      have hnat : (14937 : ℕ)^4409*50000000000000000000^1024 ≤ 13919560366599769^1024*100000^4409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14937 100000 13919560366599769 50000000000000000000 4409 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14937/100000 : ℝ)) (X := (13919560366599769/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001625991586312233/10000000000000000000 : ℝ) ≤ (5000188808286247/5000000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (10001625991586312233/10000000000000000000 : ℝ)^1024 ≤ (5000188808286247/5000000000000000 : ℝ)^4409 := by
      have hnat : (10001625991586312233 : ℕ)^1024*5000000000000000^4409 ≤ 5000188808286247^4409*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001625991586312233 10000000000000000000 5000188808286247 5000000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000188808286247/5000000000000000 : ℝ)) (X := (10001625991586312233/10000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035969078664760703/100000000000000000000 : ℝ) ≤ (500041763724169/500000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (100035969078664760703/100000000000000000000 : ℝ)^1024 ≤ (500041763724169/500000000000000 : ℝ)^4409 := by
      have hnat : (100035969078664760703 : ℕ)^1024*500000000000000^4409 ≤ 500041763724169^4409*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035969078664760703 100000000000000000000 500041763724169 500000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500041763724169/500000000000000 : ℝ)) (X := (100035969078664760703/100000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25013919560366599769/25000000000000000000 : ℝ) ≤ (5000646466197133/5000000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (25013919560366599769/25000000000000000000 : ℝ)^1024 ≤ (5000646466197133/5000000000000000 : ℝ)^4409 := by
      have hnat : (25013919560366599769 : ℕ)^1024*5000000000000000^4409 ≤ 5000646466197133^4409*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25013919560366599769 25000000000000000000 5000646466197133 5000000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000646466197133/5000000000000000 : ℝ)) (X := (25013919560366599769/25000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1625991586312233/20000000000000000000 : ℝ) ≤ ((309426082320687463/309500000000000000 : ℝ)+2*(76276318481/61900000000000 : ℝ)*(11223/100000 : ℝ))^(4409/1024 : ℝ) := by
    rw [show (309426082320687463/309500000000000000 : ℝ)+2*(76276318481/61900000000000 : ℝ)*(11223/100000 : ℝ)=(5000188808286247/5000000000000000 : ℝ) by norm_num, show 1+2*(1625991586312233/20000000000000000000 : ℝ)=(10001625991586312233/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(13919560366599769/50000000000000000000 : ℝ)+(1625991586312233/20000000000000000000 : ℝ) ≤ ((309426082320687463/309500000000000000 : ℝ)+(76276318481/61900000000000 : ℝ)*((14937/100000 : ℝ)+(11223/100000 : ℝ)))^(4409/1024 : ℝ) := by
    rw [show (309426082320687463/309500000000000000 : ℝ)+(76276318481/61900000000000 : ℝ)*((14937/100000 : ℝ)+(11223/100000 : ℝ))=(500041763724169/500000000000000 : ℝ) by norm_num, show 1+(13919560366599769/50000000000000000000 : ℝ)+(1625991586312233/20000000000000000000 : ℝ)=(100035969078664760703/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(13919560366599769/50000000000000000000 : ℝ) ≤ ((309426082320687463/309500000000000000 : ℝ)+2*(76276318481/61900000000000 : ℝ)*(14937/100000 : ℝ))^(4409/1024 : ℝ) := by
    rw [show (309426082320687463/309500000000000000 : ℝ)+2*(76276318481/61900000000000 : ℝ)*(14937/100000 : ℝ)=(5000646466197133/5000000000000000 : ℝ) by norm_num, show 1+2*(13919560366599769/50000000000000000000 : ℝ)=(25013919560366599769/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (309426082320687463/309500000000000000 : ℝ)*(X 1 0+X 2 0)+(76276318481/61900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (14937/100000 : ℝ)) (c := (309426082320687463/309500000000000000 : ℝ)) (alpha := (76276318481/61900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (309426082320687463/309500000000000000 : ℝ)*(X 0 1+X 2 1)+(76276318481/61900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (14937/100000 : ℝ)) (c := (309426082320687463/309500000000000000 : ℝ)) (alpha := (76276318481/61900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (309426082320687463/309500000000000000 : ℝ)*(X 0 2+X 1 2)+(76276318481/61900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (11223/100000 : ℝ)) (hi := (14937/100000 : ℝ)) (c := (309426082320687463/309500000000000000 : ℝ)) (alpha := (76276318481/61900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-977041903/5000000000 : ℝ)*X 0 0+(5408320747/10000000000 : ℝ)*X 0 1+(1049252247/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((334199009/625000000 : ℝ)*X 1 0+(-2036597307/10000000000 : ℝ)*X 1 1+(2623130633/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069436837/2000000000 : ℝ)*X 2 0+(131156531/250000000 : ℝ)*X 2 1+(-2036597287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2149534571/5000000000 : ℝ)*X 0 0+(825132049/2000000000 : ℝ)*X 0 1+(559868513/1250000000 : ℝ)*X 0 2+(2149534571/5000000000 : ℝ)*X 1 0+(825132049/2000000000 : ℝ)*X 1 1+(559868513/1250000000 : ℝ)*X 1 2+(2149534571/5000000000 : ℝ)*X 2 0+(825132049/2000000000 : ℝ)*X 2 1+(559868513/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1954095311/10000000000 : ℝ)*X 0 0+(5246855161/10000000000 : ℝ)*X 0 1+(675965473/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326242027/2500000000 : ℝ)*X 1 0+(-937567431/5000000000 : ℝ)*X 1 1+(1081544751/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060993633/2000000000 : ℝ)*X 2 0+(675965467/1250000000 : ℝ)*X 2 1+(-187513481/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4299094747/10000000000 : ℝ)*X 0 0+(559706667/1250000000 : ℝ)*X 0 1+(4126961541/10000000000 : ℝ)*X 0 2+(4299094747/10000000000 : ℝ)*X 1 0+(559706667/1250000000 : ℝ)*X 1 1+(4126961541/10000000000 : ℝ)*X 1 2+(4299094747/10000000000 : ℝ)*X 2 0+(559706667/1250000000 : ℝ)*X 2 1+(4126961541/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12211044048171095749812981/1934375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (556072463/50000000000000 : ℝ)*(base19) + (1020784739/100000000000000 : ℝ)*(base23) + (370637/250000000000 : ℝ)*(upper3) + (74151523/100000000000000 : ℝ)*(upper4) + (83993021/100000000000000 : ℝ)*(upper5) + (562574728759579/12500000000000 : ℝ)*(major0) + (562574728759579/12500000000000 : ℝ)*(major1) + (562574728759579/12500000000000 : ℝ)*(major2) + (77132469457381/1250000000000 : ℝ)*(sp0) + (1542655297666299/25000000000000 : ℝ)*(sp1) + (6170621282025383/100000000000000 : ℝ)*(sp2) + (707640549866771/25000000000000 : ℝ)*(sp3) + (12373109821/50000000000000 : ℝ)*(sp4) + (10947454181/100000000000000 : ℝ)*(sp7) + (1415286573460633/50000000000000 : ℝ)*(f.failure) + (3085311151405061/50000000000000 : ℝ)*(f.sum) + (13116500584343/3095000000000000000000000000 : ℝ)*base66 + (19902638906190577/3868750000000000000000000000000 : ℝ)*base67 + (25403655806765673/3868750000000000000000000000000 : ℝ)*base70 + (47849336958678173/3868750000000000000000000000000 : ℝ)*base72 + (1488282096589/386875000000000000000000000 : ℝ)*base73 + (34780306525215673/3868750000000000000000000000000 : ℝ)*base76 + (6768454443890577/3868750000000000000000000000000 : ℝ)*base77 + (26890255998571923/3868750000000000000000000000000 : ℝ)*base80 + (14859549351/24179687500000000000000000 : ℝ)*base82 + (19934673/1250000000000000000000 : ℝ)*base89 + (19934673/1250000000000000000000 : ℝ)*base91 + (19934673/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8483559120871032560768007/1934375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (268376373/50000000000000 : ℝ)*(base19) + (23163677/3125000000000 : ℝ)*(base23) + (899261/2000000000000 : ℝ)*(upper3) + (61923749/100000000000000 : ℝ)*(lower4) + (58181527/50000000000000 : ℝ)*(upper5) + (283367506502047/6250000000000 : ℝ)*(major0) + (283367506502047/6250000000000 : ℝ)*(major1) + (283367506502047/6250000000000 : ℝ)*(major2) + (5682480791/50000000000000 : ℝ)*(sp1) + (13999558397/100000000000000 : ℝ)*(sp2) + (6216254604518311/100000000000000 : ℝ)*(sp4) + (6216242702803983/100000000000000 : ℝ)*(sp5) + (24864959454889/400000000000 : ℝ)*(sp6) + (712876364339423/25000000000000 : ℝ)*(sp7) + (712876364339423/25000000000000 : ℝ)*(f.failure) + (6216254604518311/100000000000000 : ℝ)*(f.sum) + (12390836381427/3095000000000000000000000000 : ℝ)*base65 + (1166351661230483/241796875000000000000000000000 : ℝ)*base68 + (14809386169365739/1934375000000000000000000000000 : ℝ)*base70 + (198381604696761/1934375000000000000000000000000 : ℝ)*base71 + (272081477007/773750000000000000000000000 : ℝ)*base74 + (23792901998287557/967187500000000000000000000000 : ℝ)*base76 + (745719360964091/483593750000000000000000000000 : ℝ)*base78 + (5354908991003239/1934375000000000000000000000000 : ℝ)*base80 + (10670713442923/3095000000000000000000000000 : ℝ)*base82 + (7858663/625000000000000000000 : ℝ)*base89 + (7858663/625000000000000000000 : ℝ)*base91 + (7858663/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1450_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14937/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1849/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1450_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1450_s5_0 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-48855039/250000000 : ℝ)*x 0 + (540728597/1000000000 : ℝ)*x 1 + (5247218169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (48855039/250000000 : ℝ)^2205 ≤ (5963662824997/50000000000000 : ℝ)^1693 := by
    have hnat : (48855039 : ℕ)^2205*50000000000000^1693 ≤ 5963662824997^1693*250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      48855039 250000000 5963662824997 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540728597/1000000000 : ℝ)^2205 ≤ (44897947325921/100000000000000 : ℝ)^1693 := by
    have hnat : (540728597 : ℕ)^2205*100000000000000^1693 ≤ 44897947325921^1693*1000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540728597 1000000000 44897947325921 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247218169/10000000000 : ℝ)^2205 ≤ (43174727015937/100000000000000 : ℝ)^1693 := by
    have hnat : (5247218169 : ℕ)^2205*100000000000000^1693 ≤ 43174727015937^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247218169 10000000000 43174727015937 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-48855039/250000000 : ℝ), (540728597/1000000000 : ℝ), (5247218169/10000000000 : ℝ)] ![(5963662824997/50000000000000 : ℝ), (44897947325921/100000000000000 : ℝ), (43174727015937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-48855039/250000000 : ℝ)|^2205 ≤ (5963662824997/50000000000000 : ℝ)^1693
        have hw : |(-48855039/250000000 : ℝ)|=(48855039/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540728597/1000000000 : ℝ)|^2205 ≤ (44897947325921/100000000000000 : ℝ)^1693
        have hw : |(540728597/1000000000 : ℝ)|=(540728597/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247218169/10000000000 : ℝ)|^2205 ≤ (43174727015937/100000000000000 : ℝ)^1693
        have hw : |(5247218169/10000000000 : ℝ)|=(5247218169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s5_1 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5346915457/10000000000 : ℝ)*x 0 + (-1017841523/5000000000 : ℝ)*x 1 + (5247218169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346915457/10000000000 : ℝ)^2205 ≤ (44246186984641/100000000000000 : ℝ)^1693 := by
    have hnat : (5346915457 : ℕ)^2205*100000000000000^1693 ≤ 44246186984641^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346915457 10000000000 44246186984641 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1017841523/5000000000 : ℝ)^2205 ≤ (6289542991289/50000000000000 : ℝ)^1693 := by
    have hnat : (1017841523 : ℕ)^2205*50000000000000^1693 ≤ 6289542991289^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017841523 5000000000 6289542991289 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247218169/10000000000 : ℝ)^2205 ≤ (43174727015937/100000000000000 : ℝ)^1693 := by
    have hnat : (5247218169 : ℕ)^2205*100000000000000^1693 ≤ 43174727015937^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247218169 10000000000 43174727015937 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346915457/10000000000 : ℝ), (-1017841523/5000000000 : ℝ), (5247218169/10000000000 : ℝ)] ![(44246186984641/100000000000000 : ℝ), (6289542991289/50000000000000 : ℝ), (43174727015937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346915457/10000000000 : ℝ)|^2205 ≤ (44246186984641/100000000000000 : ℝ)^1693
        have hw : |(5346915457/10000000000 : ℝ)|=(5346915457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1017841523/5000000000 : ℝ)|^2205 ≤ (6289542991289/50000000000000 : ℝ)^1693
        have hw : |(-1017841523/5000000000 : ℝ)|=(1017841523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247218169/10000000000 : ℝ)|^2205 ≤ (43174727015937/100000000000000 : ℝ)^1693
        have hw : |(5247218169/10000000000 : ℝ)|=(5247218169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s5_2 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2673457729/5000000000 : ℝ)*x 0 + (5247218169/10000000000 : ℝ)*x 1 + (-1017841523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673457729/5000000000 : ℝ)^2205 ≤ (44246186995419/100000000000000 : ℝ)^1693 := by
    have hnat : (2673457729 : ℕ)^2205*100000000000000^1693 ≤ 44246186995419^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673457729 5000000000 44246186995419 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247218169/10000000000 : ℝ)^2205 ≤ (43174727015937/100000000000000 : ℝ)^1693 := by
    have hnat : (5247218169 : ℕ)^2205*100000000000000^1693 ≤ 43174727015937^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247218169 10000000000 43174727015937 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1017841523/5000000000 : ℝ)^2205 ≤ (6289542991289/50000000000000 : ℝ)^1693 := by
    have hnat : (1017841523 : ℕ)^2205*50000000000000^1693 ≤ 6289542991289^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1017841523 5000000000 6289542991289 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673457729/5000000000 : ℝ), (5247218169/10000000000 : ℝ), (-1017841523/5000000000 : ℝ)] ![(44246186995419/100000000000000 : ℝ), (43174727015937/100000000000000 : ℝ), (6289542991289/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673457729/5000000000 : ℝ)|^2205 ≤ (44246186995419/100000000000000 : ℝ)^1693
        have hw : |(2673457729/5000000000 : ℝ)|=(2673457729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247218169/10000000000 : ℝ)|^2205 ≤ (43174727015937/100000000000000 : ℝ)^1693
        have hw : |(5247218169/10000000000 : ℝ)|=(5247218169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1017841523/5000000000 : ℝ)|^2205 ≤ (6289542991289/50000000000000 : ℝ)^1693
        have hw : |(-1017841523/5000000000 : ℝ)|=(1017841523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s5_3 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1074784971/2500000000 : ℝ)*x 0 + (2063911233/5000000000 : ℝ)*x 1 + (1119192187/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074784971/2500000000 : ℝ)^2205 ≤ (33304904748569/100000000000000 : ℝ)^1693 := by
    have hnat : (1074784971 : ℕ)^2205*100000000000000^1693 ≤ 33304904748569^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074784971 2500000000 33304904748569 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2063911233/5000000000 : ℝ)^2205 ≤ (31586877129597/100000000000000 : ℝ)^1693 := by
    have hnat : (2063911233 : ℕ)^2205*100000000000000^1693 ≤ 31586877129597^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063911233 5000000000 31586877129597 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119192187/2500000000 : ℝ)^2205 ≤ (17554109053597/50000000000000 : ℝ)^1693 := by
    have hnat : (1119192187 : ℕ)^2205*50000000000000^1693 ≤ 17554109053597^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119192187 2500000000 17554109053597 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1074784971/2500000000 : ℝ), (2063911233/5000000000 : ℝ), (1119192187/2500000000 : ℝ)] ![(33304904748569/100000000000000 : ℝ), (31586877129597/100000000000000 : ℝ), (17554109053597/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1074784971/2500000000 : ℝ)|^2205 ≤ (33304904748569/100000000000000 : ℝ)^1693
        have hw : |(1074784971/2500000000 : ℝ)|=(1074784971/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2063911233/5000000000 : ℝ)|^2205 ≤ (31586877129597/100000000000000 : ℝ)^1693
        have hw : |(2063911233/5000000000 : ℝ)|=(2063911233/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119192187/2500000000 : ℝ)|^2205 ≤ (17554109053597/50000000000000 : ℝ)^1693
        have hw : |(1119192187/2500000000 : ℝ)|=(1119192187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s5_4 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1954212783/10000000000 : ℝ)*x 0 + (5247797677/10000000000 : ℝ)*x 1 + (1081340687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1954212783/10000000000 : ℝ)^2205 ≤ (596370743217/5000000000000 : ℝ)^1693 := by
    have hnat : (1954212783 : ℕ)^2205*5000000000000^1693 ≤ 596370743217^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1954212783 10000000000 596370743217 5000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247797677/10000000000 : ℝ)^2205 ≤ (8636187480983/20000000000000 : ℝ)^1693 := by
    have hnat : (5247797677 : ℕ)^2205*20000000000000^1693 ≤ 8636187480983^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247797677 10000000000 8636187480983 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1081340687/2000000000 : ℝ)^2205 ≤ (1795665908597/4000000000000 : ℝ)^1693 := by
    have hnat : (1081340687 : ℕ)^2205*4000000000000^1693 ≤ 1795665908597^1693*2000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081340687 2000000000 1795665908597 4000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1954212783/10000000000 : ℝ), (5247797677/10000000000 : ℝ), (1081340687/2000000000 : ℝ)] ![(596370743217/5000000000000 : ℝ), (8636187480983/20000000000000 : ℝ), (1795665908597/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1954212783/10000000000 : ℝ)|^2205 ≤ (596370743217/5000000000000 : ℝ)^1693
        have hw : |(-1954212783/10000000000 : ℝ)|=(1954212783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247797677/10000000000 : ℝ)|^2205 ≤ (8636187480983/20000000000000 : ℝ)^1693
        have hw : |(5247797677/10000000000 : ℝ)|=(5247797677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1081340687/2000000000 : ℝ)|^2205 ≤ (1795665908597/4000000000000 : ℝ)^1693
        have hw : |(1081340687/2000000000 : ℝ)|=(1081340687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s5_5 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1326304469/2500000000 : ℝ)*x 0 + (-234524747/1250000000 : ℝ)*x 1 + (2703351797/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326304469/2500000000 : ℝ)^2205 ≤ (21898657928767/50000000000000 : ℝ)^1693 := by
    have hnat : (1326304469 : ℕ)^2205*50000000000000^1693 ≤ 21898657928767^1693*2500000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326304469 2500000000 21898657928767 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (234524747/1250000000 : ℝ)^2205 ≤ (2827758673087/25000000000000 : ℝ)^1693 := by
    have hnat : (234524747 : ℕ)^2205*25000000000000^1693 ≤ 2827758673087^1693*1250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      234524747 1250000000 2827758673087 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703351797/5000000000 : ℝ)^2205 ≤ (8978329886869/20000000000000 : ℝ)^1693 := by
    have hnat : (2703351797 : ℕ)^2205*20000000000000^1693 ≤ 8978329886869^1693*5000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703351797 5000000000 8978329886869 20000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326304469/2500000000 : ℝ), (-234524747/1250000000 : ℝ), (2703351797/5000000000 : ℝ)] ![(21898657928767/50000000000000 : ℝ), (2827758673087/25000000000000 : ℝ), (8978329886869/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326304469/2500000000 : ℝ)|^2205 ≤ (21898657928767/50000000000000 : ℝ)^1693
        have hw : |(1326304469/2500000000 : ℝ)|=(1326304469/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-234524747/1250000000 : ℝ)|^2205 ≤ (2827758673087/25000000000000 : ℝ)^1693
        have hw : |(-234524747/1250000000 : ℝ)|=(234524747/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703351797/5000000000 : ℝ)|^2205 ≤ (8978329886869/20000000000000 : ℝ)^1693
        have hw : |(2703351797/5000000000 : ℝ)|=(2703351797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s5_6 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5305218301/10000000000 : ℝ)*x 0 + (5406703609/10000000000 : ℝ)*x 1 + (-1876197373/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305218301/10000000000 : ℝ)^2205 ≤ (10949330106801/25000000000000 : ℝ)^1693 := by
    have hnat : (5305218301 : ℕ)^2205*25000000000000^1693 ≤ 10949330106801^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305218301 10000000000 10949330106801 25000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406703609/10000000000 : ℝ)^2205 ≤ (22445824798277/50000000000000 : ℝ)^1693 := by
    have hnat : (5406703609 : ℕ)^2205*50000000000000^1693 ≤ 22445824798277^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406703609 10000000000 22445824798277 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1876197373/10000000000 : ℝ)^2205 ≤ (5655514978823/50000000000000 : ℝ)^1693 := by
    have hnat : (1876197373 : ℕ)^2205*50000000000000^1693 ≤ 5655514978823^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1876197373 10000000000 5655514978823 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305218301/10000000000 : ℝ), (5406703609/10000000000 : ℝ), (-1876197373/10000000000 : ℝ)] ![(10949330106801/25000000000000 : ℝ), (22445824798277/50000000000000 : ℝ), (5655514978823/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305218301/10000000000 : ℝ)|^2205 ≤ (10949330106801/25000000000000 : ℝ)^1693
        have hw : |(5305218301/10000000000 : ℝ)|=(5305218301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406703609/10000000000 : ℝ)|^2205 ≤ (22445824798277/50000000000000 : ℝ)^1693
        have hw : |(5406703609/10000000000 : ℝ)|=(5406703609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1876197373/10000000000 : ℝ)|^2205 ≤ (5655514978823/50000000000000 : ℝ)^1693
        have hw : |(-1876197373/10000000000 : ℝ)|=(1876197373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1450_s5_7 (p : ℝ) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4299164443/10000000000 : ℝ)*x 0 + (559438183/1250000000 : ℝ)*x 1 + (12903413/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4299164443/10000000000 : ℝ)^2205 ≤ (16652576270863/50000000000000 : ℝ)^1693 := by
    have hnat : (4299164443 : ℕ)^2205*50000000000000^1693 ≤ 16652576270863^1693*10000000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4299164443 10000000000 16652576270863 50000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559438183/1250000000 : ℝ)^2205 ≤ (35095315477737/100000000000000 : ℝ)^1693 := by
    have hnat : (559438183 : ℕ)^2205*100000000000000^1693 ≤ 35095315477737^1693*1250000000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559438183 1250000000 35095315477737 100000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (12903413/31250000 : ℝ)^2205 ≤ (631990639347/2000000000000 : ℝ)^1693 := by
    have hnat : (12903413 : ℕ)^2205*2000000000000^1693 ≤ 631990639347^1693*31250000^2205 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12903413 31250000 631990639347 2000000000000 2205 1693 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2205/512 : ℝ)) 2205 1693 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4299164443/10000000000 : ℝ), (559438183/1250000000 : ℝ), (12903413/31250000 : ℝ)] ![(16652576270863/50000000000000 : ℝ), (35095315477737/100000000000000 : ℝ), (631990639347/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4299164443/10000000000 : ℝ)|^2205 ≤ (16652576270863/50000000000000 : ℝ)^1693
        have hw : |(4299164443/10000000000 : ℝ)|=(4299164443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(559438183/1250000000 : ℝ)|^2205 ≤ (35095315477737/100000000000000 : ℝ)^1693
        have hw : |(559438183/1250000000 : ℝ)|=(559438183/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(12903413/31250000 : ℝ)|^2205 ≤ (631990639347/2000000000000 : ℝ)^1693
        have hw : |(12903413/31250000 : ℝ)|=(12903413/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1450_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1849/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11379/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14771/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1849/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1849/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1849/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1849/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1849/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1849/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11359/100000 : ℝ) ^ (4409/1024 : ℝ) ≤ (8562721428457907/100000000000000000000 : ℝ) := by
    have hpowers : (11359/100000 : ℝ)^4409 ≤ (8562721428457907/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11359 : ℕ)^4409*100000000000000000000^1024 ≤ 8562721428457907^1024*100000^4409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11359 100000 8562721428457907 100000000000000000000 4409 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11359/100000 : ℝ)) (X := (8562721428457907/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1849/12500 : ℝ) ^ (4409/1024 : ℝ) ≤ (26694060629097893/100000000000000000000 : ℝ) := by
    have hpowers : (1849/12500 : ℝ)^4409 ≤ (26694060629097893/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1849 : ℕ)^4409*100000000000000000000^1024 ≤ 26694060629097893^1024*12500^4409 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1849 12500 26694060629097893 100000000000000000000 4409 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1849/12500 : ℝ)) (X := (26694060629097893/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008562721428457907/50000000000000000000 : ℝ) ≤ (10000397716052473/10000000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (50008562721428457907/50000000000000000000 : ℝ)^1024 ≤ (10000397716052473/10000000000000000 : ℝ)^4409 := by
      have hnat : (50008562721428457907 : ℕ)^1024*10000000000000000^4409 ≤ 10000397716052473^4409*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008562721428457907 50000000000000000000 10000397716052473 10000000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000397716052473/10000000000000000 : ℝ)) (X := (50008562721428457907/50000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (500176283910287779/500000000000000000 : ℝ) ≤ (10000818735758951/10000000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (500176283910287779/500000000000000000 : ℝ)^1024 ≤ (10000818735758951/10000000000000000 : ℝ)^4409 := by
      have hnat : (500176283910287779 : ℕ)^1024*10000000000000000^4409 ≤ 10000818735758951^4409*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500176283910287779 500000000000000000 10000818735758951 10000000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000818735758951/10000000000000000 : ℝ)) (X := (500176283910287779/500000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026694060629097893/50000000000000000000 : ℝ) ≤ (10001239755465429/10000000000000000 : ℝ) ^ (4409/1024 : ℝ) := by
    have hpowers : (50026694060629097893/50000000000000000000 : ℝ)^1024 ≤ (10001239755465429/10000000000000000 : ℝ)^4409 := by
      have hnat : (50026694060629097893 : ℕ)^1024*10000000000000000^4409 ≤ 10001239755465429^4409*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026694060629097893 50000000000000000000 10001239755465429 10000000000000000 1024 4409 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001239755465429/10000000000000000 : ℝ)) (X := (50026694060629097893/50000000000000000000 : ℝ)) (by norm_num) 4409 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8562721428457907/100000000000000000000 : ℝ) ≤ ((6864360126703274521/6866000000000000000 : ℝ)+2*(210509853239/171650000000000 : ℝ)*(11359/100000 : ℝ))^(4409/1024 : ℝ) := by
    rw [show (6864360126703274521/6866000000000000000 : ℝ)+2*(210509853239/171650000000000 : ℝ)*(11359/100000 : ℝ)=(10000397716052473/10000000000000000 : ℝ) by norm_num, show 1+2*(8562721428457907/100000000000000000000 : ℝ)=(50008562721428457907/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26694060629097893/100000000000000000000 : ℝ)+(8562721428457907/100000000000000000000 : ℝ) ≤ ((6864360126703274521/6866000000000000000 : ℝ)+(210509853239/171650000000000 : ℝ)*((1849/12500 : ℝ)+(11359/100000 : ℝ)))^(4409/1024 : ℝ) := by
    rw [show (6864360126703274521/6866000000000000000 : ℝ)+(210509853239/171650000000000 : ℝ)*((1849/12500 : ℝ)+(11359/100000 : ℝ))=(10000818735758951/10000000000000000 : ℝ) by norm_num, show 1+(26694060629097893/100000000000000000000 : ℝ)+(8562721428457907/100000000000000000000 : ℝ)=(500176283910287779/500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26694060629097893/100000000000000000000 : ℝ) ≤ ((6864360126703274521/6866000000000000000 : ℝ)+2*(210509853239/171650000000000 : ℝ)*(1849/12500 : ℝ))^(4409/1024 : ℝ) := by
    rw [show (6864360126703274521/6866000000000000000 : ℝ)+2*(210509853239/171650000000000 : ℝ)*(1849/12500 : ℝ)=(10001239755465429/10000000000000000 : ℝ) by norm_num, show 1+2*(26694060629097893/100000000000000000000 : ℝ)=(50026694060629097893/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6864360126703274521/6866000000000000000 : ℝ)*(X 1 0+X 2 0)+(210509853239/171650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (1849/12500 : ℝ)) (c := (6864360126703274521/6866000000000000000 : ℝ)) (alpha := (210509853239/171650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6864360126703274521/6866000000000000000 : ℝ)*(X 0 1+X 2 1)+(210509853239/171650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (1849/12500 : ℝ)) (c := (6864360126703274521/6866000000000000000 : ℝ)) (alpha := (210509853239/171650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6864360126703274521/6866000000000000000 : ℝ)*(X 0 2+X 1 2)+(210509853239/171650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4409/1024 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (1849/12500 : ℝ)) (c := (6864360126703274521/6866000000000000000 : ℝ)) (alpha := (210509853239/171650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-48855039/250000000 : ℝ)*X 0 0+(540728597/1000000000 : ℝ)*X 0 1+(5247218169/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346915457/10000000000 : ℝ)*X 1 0+(-1017841523/5000000000 : ℝ)*X 1 1+(5247218169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673457729/5000000000 : ℝ)*X 2 0+(5247218169/10000000000 : ℝ)*X 2 1+(-1017841523/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1074784971/2500000000 : ℝ)*X 0 0+(2063911233/5000000000 : ℝ)*X 0 1+(1119192187/2500000000 : ℝ)*X 0 2+(1074784971/2500000000 : ℝ)*X 1 0+(2063911233/5000000000 : ℝ)*X 1 1+(1119192187/2500000000 : ℝ)*X 1 2+(1074784971/2500000000 : ℝ)*X 2 0+(2063911233/5000000000 : ℝ)*X 2 1+(1119192187/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1954212783/10000000000 : ℝ)*X 0 0+(5247797677/10000000000 : ℝ)*X 0 1+(1081340687/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1326304469/2500000000 : ℝ)*X 1 0+(-234524747/1250000000 : ℝ)*X 1 1+(2703351797/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305218301/10000000000 : ℝ)*X 2 0+(5406703609/10000000000 : ℝ)*X 2 1+(-1876197373/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4299164443/10000000000 : ℝ)*X 0 0+(559438183/1250000000 : ℝ)*X 0 1+(12903413/31250000 : ℝ)*X 0 2+(4299164443/10000000000 : ℝ)*X 1 0+(559438183/1250000000 : ℝ)*X 1 1+(12903413/31250000 : ℝ)*X 1 2+(4299164443/10000000000 : ℝ)*X 2 0+(559438183/1250000000 : ℝ)*X 2 1+(12903413/31250000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1450_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (903878955443283348968204823/85825000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1900678117/100000000000000 : ℝ)*(base19) + (443364077/25000000000000 : ℝ)*(base23) + (68649169/100000000000000 : ℝ)*(lower2) + (65318251/25000000000000 : ℝ)*(upper3) + (42266947/25000000000000 : ℝ)*(upper5) + (1139155460814993/25000000000000 : ℝ)*(major0) + (1139155460814993/25000000000000 : ℝ)*(major1) + (1139155460814993/25000000000000 : ℝ)*(major2) + (1249478919051817/20000000000000 : ℝ)*(sp0) + (3123716476981961/50000000000000 : ℝ)*(sp1) + (6247433081185731/100000000000000 : ℝ)*(sp2) + (1432894261850439/50000000000000 : ℝ)*(sp3) + (20129691477/50000000000000 : ℝ)*(sp4) + (19957121977/100000000000000 : ℝ)*(sp7) + (358226060102857/12500000000000 : ℝ)*(f.failure) + (6247434854642039/100000000000000 : ℝ)*(f.sum) + (38209661361249/17165000000000000000000000000 : ℝ)*base66 + (2804932750091173353/171650000000000000000000000000000 : ℝ)*base67 + (1007554594093423353/171650000000000000000000000000000 : ℝ)*base69 + (3028201074951723353/171650000000000000000000000000000 : ℝ)*base71 + (6385750852191/1072812500000000000000000000 : ℝ)*base73 + (4158647540219473353/171650000000000000000000000000000 : ℝ)*base75 + (3012617410189123353/171650000000000000000000000000000 : ℝ)*base77 + (3238072432290023353/171650000000000000000000000000000 : ℝ)*base79 + (19392653889827/8582500000000000000000000000 : ℝ)*base82 + (1010017/312500000000000000000 : ℝ)*base89 + (1010017/312500000000000000000 : ℝ)*base91 + (1010017/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (93181657833541462951197/8582500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1402080859/100000000000000 : ℝ)*(base19) + (586720083/25000000000000 : ℝ)*(base23) + (141463417/50000000000000 : ℝ)*(upper3) + (2440087/2500000000000 : ℝ)*(lower4) + (1768797/800000000000 : ℝ)*(upper5) + (4589883745448153/100000000000000 : ℝ)*(major0) + (4589883745448153/100000000000000 : ℝ)*(major1) + (4589883745448153/100000000000000 : ℝ)*(major2) + (5782970897/20000000000000 : ℝ)*(sp1) + (15393562107/25000000000000 : ℝ)*(sp2) + (629303915020239/10000000000000 : ℝ)*(sp4) + (3146504416633523/50000000000000 : ℝ)*(sp5) + (629297522907363/10000000000000 : ℝ)*(sp6) + (144336398939413/5000000000000 : ℝ)*(sp7) + (144336398939413/5000000000000 : ℝ)*(f.failure) + (629303915020239/10000000000000 : ℝ)*(f.sum) + (385472744121/4291250000000000000000000000 : ℝ)*base65 + (1799250361587910287/686600000000000000000000000000000 : ℝ)*base68 + (2280423450184089713/686600000000000000000000000000000 : ℝ)*base69 + (196745650555489713/686600000000000000000000000000000 : ℝ)*base71 + (1063041276381/4291250000000000000000000000 : ℝ)*base73 + (2901870850846689713/686600000000000000000000000000000 : ℝ)*base75 + (3157098784790310287/686600000000000000000000000000000 : ℝ)*base78 + (4989997950963110287/686600000000000000000000000000000 : ℝ)*base80 + (1578319608501/4291250000000000000000000000 : ℝ)*base81 + (1709853/125000000000000000000 : ℝ)*base89 + (1709853/125000000000000000000 : ℝ)*base91 + (1709853/125000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1450_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1849/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1450_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1450_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1450_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1450_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1450_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4409/1024 : ℝ) ≤ p) (hpb : p ≤ (2205/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (39749881/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15737/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10477/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11379/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14771/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1450_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
