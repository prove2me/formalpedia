-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1297_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:34:51.138326+00:00
-- url     : https://prove2.me/submissions/34a79031-89f3-433b-9540-f782892a907e

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
theorem support_rectangle_w1297_s0_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1836050611/10000000000 : ℝ)*x 0 + (3008289981/5000000000 : ℝ)*x 1 + (1200014919/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1836050611/10000000000 : ℝ)^4257 ≤ (10733271655579/100000000000000 : ℝ)^3233 := by
    have hnat : (1836050611 : ℕ)^4257*100000000000000^3233 ≤ 10733271655579^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1836050611 10000000000 10733271655579 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3008289981/5000000000 : ℝ)^4257 ≤ (51222681310241/100000000000000 : ℝ)^3233 := by
    have hnat : (3008289981 : ℕ)^4257*100000000000000^3233 ≤ 51222681310241^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3008289981 5000000000 51222681310241 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1200014919/2500000000 : ℝ)^4257 ≤ (38044047014667/100000000000000 : ℝ)^3233 := by
    have hnat : (1200014919 : ℕ)^4257*100000000000000^3233 ≤ 38044047014667^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1200014919 2500000000 38044047014667 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1836050611/10000000000 : ℝ), (3008289981/5000000000 : ℝ), (1200014919/2500000000 : ℝ)] ![(10733271655579/100000000000000 : ℝ), (51222681310241/100000000000000 : ℝ), (38044047014667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1836050611/10000000000 : ℝ)|^4257 ≤ (10733271655579/100000000000000 : ℝ)^3233
        have hw : |(-1836050611/10000000000 : ℝ)|=(1836050611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3008289981/5000000000 : ℝ)|^4257 ≤ (51222681310241/100000000000000 : ℝ)^3233
        have hw : |(3008289981/5000000000 : ℝ)|=(3008289981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1200014919/2500000000 : ℝ)|^4257 ≤ (38044047014667/100000000000000 : ℝ)^3233
        have hw : |(1200014919/2500000000 : ℝ)|=(1200014919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s0_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5506857383/10000000000 : ℝ)*x 0 + (-2529809193/10000000000 : ℝ)*x 1 + (2400029823/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5506857383/10000000000 : ℝ)^4257 ≤ (11396706217973/25000000000000 : ℝ)^3233 := by
    have hnat : (5506857383 : ℕ)^4257*25000000000000^3233 ≤ 11396706217973^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506857383 10000000000 11396706217973 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2529809193/10000000000 : ℝ)^4257 ≤ (1023070525889/6250000000000 : ℝ)^3233 := by
    have hnat : (2529809193 : ℕ)^4257*6250000000000^3233 ≤ 1023070525889^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2529809193 10000000000 1023070525889 6250000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2400029823/5000000000 : ℝ)^4257 ≤ (2377752918849/6250000000000 : ℝ)^3233 := by
    have hnat : (2400029823 : ℕ)^4257*6250000000000^3233 ≤ 2377752918849^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2400029823 5000000000 2377752918849 6250000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5506857383/10000000000 : ℝ), (-2529809193/10000000000 : ℝ), (2400029823/5000000000 : ℝ)] ![(11396706217973/25000000000000 : ℝ), (1023070525889/6250000000000 : ℝ), (2377752918849/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5506857383/10000000000 : ℝ)|^4257 ≤ (11396706217973/25000000000000 : ℝ)^3233
        have hw : |(5506857383/10000000000 : ℝ)|=(5506857383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2529809193/10000000000 : ℝ)|^4257 ≤ (1023070525889/6250000000000 : ℝ)^3233
        have hw : |(-2529809193/10000000000 : ℝ)|=(2529809193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2400029823/5000000000 : ℝ)|^4257 ≤ (2377752918849/6250000000000 : ℝ)^3233
        have hw : |(2400029823/5000000000 : ℝ)|=(2400029823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s0_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5506857361/10000000000 : ℝ)*x 0 + (2400029843/5000000000 : ℝ)*x 1 + (-632452293/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5506857361/10000000000 : ℝ)^4257 ≤ (5698353079011/12500000000000 : ℝ)^3233 := by
    have hnat : (5506857361 : ℕ)^4257*12500000000000^3233 ≤ 5698353079011^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5506857361 10000000000 5698353079011 12500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2400029843/5000000000 : ℝ)^4257 ≤ (9511011779757/25000000000000 : ℝ)^3233 := by
    have hnat : (2400029843 : ℕ)^4257*25000000000000^3233 ≤ 9511011779757^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2400029843 5000000000 9511011779757 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (632452293/2500000000 : ℝ)^4257 ≤ (3273825647061/20000000000000 : ℝ)^3233 := by
    have hnat : (632452293 : ℕ)^4257*20000000000000^3233 ≤ 3273825647061^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      632452293 2500000000 3273825647061 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5506857361/10000000000 : ℝ), (2400029843/5000000000 : ℝ), (-632452293/2500000000 : ℝ)] ![(5698353079011/12500000000000 : ℝ), (9511011779757/25000000000000 : ℝ), (3273825647061/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5506857361/10000000000 : ℝ)|^4257 ≤ (5698353079011/12500000000000 : ℝ)^3233
        have hw : |(5506857361/10000000000 : ℝ)|=(5506857361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2400029843/5000000000 : ℝ)|^4257 ≤ (9511011779757/25000000000000 : ℝ)^3233
        have hw : |(2400029843/5000000000 : ℝ)|=(2400029843/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-632452293/2500000000 : ℝ)|^4257 ≤ (3273825647061/20000000000000 : ℝ)^3233
        have hw : |(-632452293/2500000000 : ℝ)|=(632452293/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s0_3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4185563851/10000000000 : ℝ)*x 0 + (3109111497/10000000000 : ℝ)*x 1 + (5614126591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4185563851/10000000000 : ℝ)^4257 ≤ (992660487213/3125000000000 : ℝ)^3233 := by
    have hnat : (4185563851 : ℕ)^4257*3125000000000^3233 ≤ 992660487213^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4185563851 10000000000 992660487213 3125000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3109111497/10000000000 : ℝ)^4257 ≤ (21475195291103/100000000000000 : ℝ)^3233 := by
    have hnat : (3109111497 : ℕ)^4257*100000000000000^3233 ≤ 21475195291103^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3109111497 10000000000 21475195291103 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5614126591/10000000000 : ℝ)^4257 ≤ (4675966909537/10000000000000 : ℝ)^3233 := by
    have hnat : (5614126591 : ℕ)^4257*10000000000000^3233 ≤ 4675966909537^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5614126591 10000000000 4675966909537 10000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4185563851/10000000000 : ℝ), (3109111497/10000000000 : ℝ), (5614126591/10000000000 : ℝ)] ![(992660487213/3125000000000 : ℝ), (21475195291103/100000000000000 : ℝ), (4675966909537/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4185563851/10000000000 : ℝ)|^4257 ≤ (992660487213/3125000000000 : ℝ)^3233
        have hw : |(4185563851/10000000000 : ℝ)|=(4185563851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3109111497/10000000000 : ℝ)|^4257 ≤ (21475195291103/100000000000000 : ℝ)^3233
        have hw : |(3109111497/10000000000 : ℝ)|=(3109111497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5614126591/10000000000 : ℝ)|^4257 ≤ (4675966909537/10000000000000 : ℝ)^3233
        have hw : |(5614126591/10000000000 : ℝ)|=(5614126591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s0_4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1840746487/10000000000 : ℝ)*x 0 + (150982817/312500000 : ℝ)*x 1 + (5984073139/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1840746487/10000000000 : ℝ)^4257 ≤ (10769432437001/100000000000000 : ℝ)^3233 := by
    have hnat : (1840746487 : ℕ)^4257*100000000000000^3233 ≤ 10769432437001^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1840746487 10000000000 10769432437001 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (150982817/312500000 : ℝ)^4257 ≤ (9592994921847/25000000000000 : ℝ)^3233 := by
    have hnat : (150982817 : ℕ)^4257*25000000000000^3233 ≤ 9592994921847^3233*312500000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150982817 312500000 9592994921847 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5984073139/10000000000 : ℝ)^4257 ≤ (50858587855543/100000000000000 : ℝ)^3233 := by
    have hnat : (5984073139 : ℕ)^4257*100000000000000^3233 ≤ 50858587855543^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5984073139 10000000000 50858587855543 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1840746487/10000000000 : ℝ), (150982817/312500000 : ℝ), (5984073139/10000000000 : ℝ)] ![(10769432437001/100000000000000 : ℝ), (9592994921847/25000000000000 : ℝ), (50858587855543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1840746487/10000000000 : ℝ)|^4257 ≤ (10769432437001/100000000000000 : ℝ)^3233
        have hw : |(-1840746487/10000000000 : ℝ)|=(1840746487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(150982817/312500000 : ℝ)|^4257 ≤ (9592994921847/25000000000000 : ℝ)^3233
        have hw : |(150982817/312500000 : ℝ)|=(150982817/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5984073139/10000000000 : ℝ)|^4257 ≤ (50858587855543/100000000000000 : ℝ)^3233
        have hw : |(5984073139/10000000000 : ℝ)|=(5984073139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s0_5 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2587815347/5000000000 : ℝ)*x 0 + (-1345793009/10000000000 : ℝ)*x 1 + (1496018949/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2587815347/5000000000 : ℝ)^4257 ≤ (8402254100689/20000000000000 : ℝ)^3233 := by
    have hnat : (2587815347 : ℕ)^4257*20000000000000^3233 ≤ 8402254100689^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2587815347 5000000000 8402254100689 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1345793009/10000000000 : ℝ)^4257 ≤ (3565055952269/50000000000000 : ℝ)^3233 := by
    have hnat : (1345793009 : ℕ)^4257*50000000000000^3233 ≤ 3565055952269^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1345793009 10000000000 3565055952269 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1496018949/2500000000 : ℝ)^4257 ≤ (50858617589789/100000000000000 : ℝ)^3233 := by
    have hnat : (1496018949 : ℕ)^4257*100000000000000^3233 ≤ 50858617589789^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1496018949 2500000000 50858617589789 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2587815347/5000000000 : ℝ), (-1345793009/10000000000 : ℝ), (1496018949/2500000000 : ℝ)] ![(8402254100689/20000000000000 : ℝ), (3565055952269/50000000000000 : ℝ), (50858617589789/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2587815347/5000000000 : ℝ)|^4257 ≤ (8402254100689/20000000000000 : ℝ)^3233
        have hw : |(2587815347/5000000000 : ℝ)|=(2587815347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1345793009/10000000000 : ℝ)|^4257 ≤ (3565055952269/50000000000000 : ℝ)^3233
        have hw : |(-1345793009/10000000000 : ℝ)|=(1345793009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1496018949/2500000000 : ℝ)|^4257 ≤ (50858617589789/100000000000000 : ℝ)^3233
        have hw : |(1496018949/2500000000 : ℝ)|=(1496018949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s0_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5175632007/10000000000 : ℝ)*x 0 + (5984073501/10000000000 : ℝ)*x 1 + (-336448669/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5175632007/10000000000 : ℝ)^4257 ≤ (1050282113423/2500000000000 : ℝ)^3233 := by
    have hnat : (5175632007 : ℕ)^4257*2500000000000^3233 ≤ 1050282113423^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175632007 10000000000 1050282113423 2500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5984073501/10000000000 : ℝ)^4257 ≤ (12714647976663/25000000000000 : ℝ)^3233 := by
    have hnat : (5984073501 : ℕ)^4257*25000000000000^3233 ≤ 12714647976663^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5984073501 10000000000 12714647976663 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (336448669/2500000000 : ℝ)^4257 ≤ (1782530883447/25000000000000 : ℝ)^3233 := by
    have hnat : (336448669 : ℕ)^4257*25000000000000^3233 ≤ 1782530883447^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336448669 2500000000 1782530883447 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5175632007/10000000000 : ℝ), (5984073501/10000000000 : ℝ), (-336448669/2500000000 : ℝ)] ![(1050282113423/2500000000000 : ℝ), (12714647976663/25000000000000 : ℝ), (1782530883447/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5175632007/10000000000 : ℝ)|^4257 ≤ (1050282113423/2500000000000 : ℝ)^3233
        have hw : |(5175632007/10000000000 : ℝ)|=(5175632007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5984073501/10000000000 : ℝ)|^4257 ≤ (12714647976663/25000000000000 : ℝ)^3233
        have hw : |(5984073501/10000000000 : ℝ)|=(5984073501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-336448669/2500000000 : ℝ)|^4257 ≤ (1782530883447/25000000000000 : ℝ)^3233
        have hw : |(-336448669/2500000000 : ℝ)|=(336448669/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s0_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4195239319/10000000000 : ℝ)*x 0 + (2774748183/5000000000 : ℝ)*x 1 + (1588020361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4195239319/10000000000 : ℝ)^4257 ≤ (31861857652369/100000000000000 : ℝ)^3233 := by
    have hnat : (4195239319 : ℕ)^4257*100000000000000^3233 ≤ 31861857652369^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195239319 10000000000 31861857652369 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2774748183/5000000000 : ℝ)^4257 ≤ (11513041537019/25000000000000 : ℝ)^3233 := by
    have hnat : (2774748183 : ℕ)^4257*25000000000000^3233 ≤ 11513041537019^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2774748183 5000000000 11513041537019 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1588020361/5000000000 : ℝ)^4257 ≤ (22085976189333/100000000000000 : ℝ)^3233 := by
    have hnat : (1588020361 : ℕ)^4257*100000000000000^3233 ≤ 22085976189333^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1588020361 5000000000 22085976189333 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4195239319/10000000000 : ℝ), (2774748183/5000000000 : ℝ), (1588020361/5000000000 : ℝ)] ![(31861857652369/100000000000000 : ℝ), (11513041537019/25000000000000 : ℝ), (22085976189333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4195239319/10000000000 : ℝ)|^4257 ≤ (31861857652369/100000000000000 : ℝ)^3233
        have hw : |(4195239319/10000000000 : ℝ)|=(4195239319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2774748183/5000000000 : ℝ)|^4257 ≤ (11513041537019/25000000000000 : ℝ)^3233
        have hw : |(2774748183/5000000000 : ℝ)|=(2774748183/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1588020361/5000000000 : ℝ)|^4257 ≤ (22085976189333/100000000000000 : ℝ)^3233
        have hw : |(1588020361/5000000000 : ℝ)|=(1588020361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1297_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1071/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27199/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (133/32 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^133 ≤ (0 : ℝ)^32 := by
      have hnat : (0 : ℕ)^133*1^32 ≤ 0^32*1^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (133/32 : ℝ) ≤ (2218512290078805387/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^133 ≤ (2218512290078805387/100000000000000000000 : ℝ)^32 := by
      have hnat : (2 : ℕ)^133*100000000000000000000^32 ≤ 2218512290078805387^32*5^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2218512290078805387 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2218512290078805387/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (1 : ℝ)^32 ≤ (1 : ℝ)^133 := by
      have hnat : (1 : ℕ)^32*1^133 ≤ 1^133*1^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (102218512290078805387/100000000000000000000 : ℝ) ≤ (2513233466172037/2500000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (102218512290078805387/100000000000000000000 : ℝ)^32 ≤ (2513233466172037/2500000000000000 : ℝ)^133 := by
      have hnat : (102218512290078805387 : ℕ)^32*2500000000000000^133 ≤ 2513233466172037^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102218512290078805387 100000000000000000000 2513233466172037 2500000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2513233466172037/2500000000000000 : ℝ)) (X := (102218512290078805387/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (52218512290078805387/50000000000000000000 : ℝ) ≤ (1263233466172037/1250000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (52218512290078805387/50000000000000000000 : ℝ)^32 ≤ (1263233466172037/1250000000000000 : ℝ)^133 := by
      have hnat : (52218512290078805387 : ℕ)^32*1250000000000000^133 ≤ 1263233466172037^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52218512290078805387 50000000000000000000 1263233466172037 1250000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1263233466172037/1250000000000000 : ℝ)) (X := (52218512290078805387/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(13233466172037/1000000000000000 : ℝ)*(0 : ℝ))^(133/32 : ℝ) := by
    rw [show (1 : ℝ)+2*(13233466172037/1000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2218512290078805387/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(13233466172037/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(133/32 : ℝ) := by
    rw [show (1 : ℝ)+(13233466172037/1000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2513233466172037/2500000000000000 : ℝ) by norm_num, show 1+(2218512290078805387/100000000000000000000 : ℝ)+(0 : ℝ)=(102218512290078805387/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2218512290078805387/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(13233466172037/1000000000000000 : ℝ)*(2/5 : ℝ))^(133/32 : ℝ) := by
    rw [show (1 : ℝ)+2*(13233466172037/1000000000000000 : ℝ)*(2/5 : ℝ)=(1263233466172037/1250000000000000 : ℝ) by norm_num, show 1+2*(2218512290078805387/100000000000000000000 : ℝ)=(52218512290078805387/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(13233466172037/1000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13233466172037/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(13233466172037/1000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13233466172037/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(13233466172037/1000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (13233466172037/1000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1836050611/10000000000 : ℝ)*X 0 0+(3008289981/5000000000 : ℝ)*X 0 1+(1200014919/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5506857383/10000000000 : ℝ)*X 1 0+(-2529809193/10000000000 : ℝ)*X 1 1+(2400029823/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5506857361/10000000000 : ℝ)*X 2 0+(2400029843/5000000000 : ℝ)*X 2 1+(-632452293/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4185563851/10000000000 : ℝ)*X 0 0+(3109111497/10000000000 : ℝ)*X 0 1+(5614126591/10000000000 : ℝ)*X 0 2+(4185563851/10000000000 : ℝ)*X 1 0+(3109111497/10000000000 : ℝ)*X 1 1+(5614126591/10000000000 : ℝ)*X 1 2+(4185563851/10000000000 : ℝ)*X 2 0+(3109111497/10000000000 : ℝ)*X 2 1+(5614126591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1840746487/10000000000 : ℝ)*X 0 0+(150982817/312500000 : ℝ)*X 0 1+(5984073139/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2587815347/5000000000 : ℝ)*X 1 0+(-1345793009/10000000000 : ℝ)*X 1 1+(1496018949/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5175632007/10000000000 : ℝ)*X 2 0+(5984073501/10000000000 : ℝ)*X 2 1+(-336448669/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4195239319/10000000000 : ℝ)*X 0 0+(2774748183/5000000000 : ℝ)*X 0 1+(1588020361/5000000000 : ℝ)*X 0 2+(4195239319/10000000000 : ℝ)*X 1 0+(2774748183/5000000000 : ℝ)*X 1 1+(1588020361/5000000000 : ℝ)*X 1 2+(4195239319/10000000000 : ℝ)*X 2 0+(2774748183/5000000000 : ℝ)*X 2 1+(1588020361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5445785600324751427803/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (16353811/25000000000000 : ℝ)*(base1) + (1322158839/100000000000000 : ℝ)*(base19) + (32971871/2500000000000 : ℝ)*(base23) + (76294371/50000000000000 : ℝ)*(upper3) + (156715233/100000000000000 : ℝ)*(upper5) + (61061412066227/10000000000000 : ℝ)*(major0) + (61061412066227/10000000000000 : ℝ)*(major1) + (61061412066227/10000000000000 : ℝ)*(major2) + (411010348043067/50000000000000 : ℝ)*(sp0) + (822023540391177/100000000000000 : ℝ)*(sp1) + (102752942959397/12500000000000 : ℝ)*(sp2) + (39920111511429/10000000000000 : ℝ)*(sp3) + (2115939563/50000000000000 : ℝ)*(sp4) + (2016718801/100000000000000 : ℝ)*(sp7) + (79840639449667/20000000000000 : ℝ)*(f.failure) + (401379327417/48828125000 : ℝ)*(f.sum) + (1666374129399/5000000000000000000000000000 : ℝ)*base65 + (54349316014399/10000000000000000000000000000 : ℝ)*base67 + (21704131394399/10000000000000000000000000000 : ℝ)*base69 + (3597351505601/10000000000000000000000000000 : ℝ)*base72 + (24347023819399/5000000000000000000000000000 : ℝ)*base73 + (6257988954399/10000000000000000000000000000 : ℝ)*base75 + (34622041044399/10000000000000000000000000000 : ℝ)*base77 + (11921179174399/10000000000000000000000000000 : ℝ)*base79 + (19607492294399/5000000000000000000000000000 : ℝ)*base81 + (106963/125000000000000000000 : ℝ)*base89 + (106963/125000000000000000000 : ℝ)*base91 + (106963/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11363946111892528747647/1250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102799323/20000000000000 : ℝ)*(base1) + (89180999/5000000000000 : ℝ)*(base19) + (499941819/25000000000000 : ℝ)*(base23) + (8884779/2500000000000 : ℝ)*(upper3) + (80557009309927/12500000000000 : ℝ)*(major0) + (80557009309927/12500000000000 : ℝ)*(major1) + (80557009309927/12500000000000 : ℝ)*(major2) + (479444061/20000000000000 : ℝ)*(sp1) + (583882821/25000000000000 : ℝ)*(sp2) + (696069/25000000000000 : ℝ)*(sp3) + (867584197477299/100000000000000 : ℝ)*(sp4) + (433789751320199/50000000000000 : ℝ)*(sp5) + (216894837045531/25000000000000 : ℝ)*(sp6) + (421327645658689/100000000000000 : ℝ)*(sp7) + (21066408121979/5000000000000 : ℝ)*(f.failure) + (216895920870171/25000000000000 : ℝ)*(f.sum) + (13416747676201/6250000000000000000000000000 : ℝ)*base66 + (55053946113701/12500000000000000000000000000 : ℝ)*base68 + (76542217776201/12500000000000000000000000000 : ℝ)*base70 + (14583412736299/12500000000000000000000000000 : ℝ)*base71 + (16994890457451/6250000000000000000000000000 : ℝ)*base74 + (24764058738701/12500000000000000000000000000 : ℝ)*base76 + (87677666826201/12500000000000000000000000000 : ℝ)*base78 + (77306844763701/12500000000000000000000000000 : ℝ)*base80 + (12570540476201/6250000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (200331/31250000000000000000 : ℝ)*base89 + (200331/31250000000000000000 : ℝ)*base91 + (200331/31250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1297_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1071/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27199/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1297_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1297_s1_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2027366873/10000000000 : ℝ)*x 0 + (1415734623/2500000000 : ℝ)*x 1 + (1257803929/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2027366873/10000000000 : ℝ)^4257 ≤ (6114831286103/50000000000000 : ℝ)^3233 := by
    have hnat : (2027366873 : ℕ)^4257*50000000000000^3233 ≤ 6114831286103^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027366873 10000000000 6114831286103 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1415734623/2500000000 : ℝ)^4257 ≤ (11823931005957/25000000000000 : ℝ)^3233 := by
    have hnat : (1415734623 : ℕ)^4257*25000000000000^3233 ≤ 11823931005957^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1415734623 2500000000 11823931005957 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1257803929/2500000000 : ℝ)^4257 ≤ (4047461338809/10000000000000 : ℝ)^3233 := by
    have hnat : (1257803929 : ℕ)^4257*10000000000000^3233 ≤ 4047461338809^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1257803929 2500000000 4047461338809 10000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2027366873/10000000000 : ℝ), (1415734623/2500000000 : ℝ), (1257803929/2500000000 : ℝ)] ![(6114831286103/50000000000000 : ℝ), (11823931005957/25000000000000 : ℝ), (4047461338809/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2027366873/10000000000 : ℝ)|^4257 ≤ (6114831286103/50000000000000 : ℝ)^3233
        have hw : |(-2027366873/10000000000 : ℝ)|=(2027366873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1415734623/2500000000 : ℝ)|^4257 ≤ (11823931005957/25000000000000 : ℝ)^3233
        have hw : |(1415734623/2500000000 : ℝ)|=(1415734623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1257803929/2500000000 : ℝ)|^4257 ≤ (4047461338809/10000000000000 : ℝ)^3233
        have hw : |(1257803929/2500000000 : ℝ)|=(1257803929/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s1_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082091523/2000000000 : ℝ)*x 0 + (-473161513/2000000000 : ℝ)*x 1 + (5031215837/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082091523/2000000000 : ℝ)^4257 ≤ (44538975290513/100000000000000 : ℝ)^3233 := by
    have hnat : (1082091523 : ℕ)^4257*100000000000000^3233 ≤ 44538975290513^3233*2000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082091523 2000000000 44538975290513 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (473161513/2000000000 : ℝ)^4257 ≤ (2997282003927/20000000000000 : ℝ)^3233 := by
    have hnat : (473161513 : ℕ)^4257*20000000000000^3233 ≤ 2997282003927^3233*2000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473161513 2000000000 2997282003927 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5031215837/10000000000 : ℝ)^4257 ≤ (4047461466981/10000000000000 : ℝ)^3233 := by
    have hnat : (5031215837 : ℕ)^4257*10000000000000^3233 ≤ 4047461466981^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5031215837 10000000000 4047461466981 10000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082091523/2000000000 : ℝ), (-473161513/2000000000 : ℝ), (5031215837/10000000000 : ℝ)] ![(44538975290513/100000000000000 : ℝ), (2997282003927/20000000000000 : ℝ), (4047461466981/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082091523/2000000000 : ℝ)|^4257 ≤ (44538975290513/100000000000000 : ℝ)^3233
        have hw : |(1082091523/2000000000 : ℝ)|=(1082091523/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-473161513/2000000000 : ℝ)|^4257 ≤ (2997282003927/20000000000000 : ℝ)^3233
        have hw : |(-473161513/2000000000 : ℝ)|=(473161513/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5031215837/10000000000 : ℝ)|^4257 ≤ (4047461466981/10000000000000 : ℝ)^3233
        have hw : |(5031215837/10000000000 : ℝ)|=(5031215837/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s1_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (270522883/500000000 : ℝ)*x 0 + (5031215659/10000000000 : ℝ)*x 1 + (-2365807733/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (270522883/500000000 : ℝ)^4257 ≤ (8907795155657/20000000000000 : ℝ)^3233 := by
    have hnat : (270522883 : ℕ)^4257*20000000000000^3233 ≤ 8907795155657^3233*500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      270522883 500000000 8907795155657 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5031215659/10000000000 : ℝ)^4257 ≤ (2529663299019/6250000000000 : ℝ)^3233 := by
    have hnat : (5031215659 : ℕ)^4257*6250000000000^3233 ≤ 2529663299019^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5031215659 10000000000 2529663299019 6250000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2365807733/10000000000 : ℝ)^4257 ≤ (3746602855229/25000000000000 : ℝ)^3233 := by
    have hnat : (2365807733 : ℕ)^4257*25000000000000^3233 ≤ 3746602855229^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2365807733 10000000000 3746602855229 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(270522883/500000000 : ℝ), (5031215659/10000000000 : ℝ), (-2365807733/10000000000 : ℝ)] ![(8907795155657/20000000000000 : ℝ), (2529663299019/6250000000000 : ℝ), (3746602855229/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(270522883/500000000 : ℝ)|^4257 ≤ (8907795155657/20000000000000 : ℝ)^3233
        have hw : |(270522883/500000000 : ℝ)|=(270522883/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5031215659/10000000000 : ℝ)|^4257 ≤ (2529663299019/6250000000000 : ℝ)^3233
        have hw : |(5031215659/10000000000 : ℝ)|=(5031215659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2365807733/10000000000 : ℝ)|^4257 ≤ (3746602855229/25000000000000 : ℝ)^3233
        have hw : |(-2365807733/10000000000 : ℝ)|=(2365807733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s1_3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4300261631/10000000000 : ℝ)*x 0 + (462043243/1250000000 : ℝ)*x 1 + (312322911/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4300261631/10000000000 : ℝ)^4257 ≤ (32916250753573/100000000000000 : ℝ)^3233 := by
    have hnat : (4300261631 : ℕ)^4257*100000000000000^3233 ≤ 32916250753573^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4300261631 10000000000 32916250753573 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (462043243/1250000000 : ℝ)^4257 ≤ (5393884377041/20000000000000 : ℝ)^3233 := by
    have hnat : (462043243 : ℕ)^4257*20000000000000^3233 ≤ 5393884377041^3233*1250000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      462043243 1250000000 5393884377041 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (312322911/625000000 : ℝ)^4257 ≤ (20057163674301/50000000000000 : ℝ)^3233 := by
    have hnat : (312322911 : ℕ)^4257*50000000000000^3233 ≤ 20057163674301^3233*625000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      312322911 625000000 20057163674301 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4300261631/10000000000 : ℝ), (462043243/1250000000 : ℝ), (312322911/625000000 : ℝ)] ![(32916250753573/100000000000000 : ℝ), (5393884377041/20000000000000 : ℝ), (20057163674301/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4300261631/10000000000 : ℝ)|^4257 ≤ (32916250753573/100000000000000 : ℝ)^3233
        have hw : |(4300261631/10000000000 : ℝ)|=(4300261631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(462043243/1250000000 : ℝ)|^4257 ≤ (5393884377041/20000000000000 : ℝ)^3233
        have hw : |(462043243/1250000000 : ℝ)|=(462043243/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(312322911/625000000 : ℝ)|^4257 ≤ (20057163674301/50000000000000 : ℝ)^3233
        have hw : |(312322911/625000000 : ℝ)|=(312322911/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s1_4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2027993203/10000000000 : ℝ)*x 0 + (5039420981/10000000000 : ℝ)*x 1 + (282728927/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2027993203/10000000000 : ℝ)^4257 ≤ (3058659425841/25000000000000 : ℝ)^3233 := by
    have hnat : (2027993203 : ℕ)^4257*25000000000000^3233 ≤ 3058659425841^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2027993203 10000000000 3058659425841 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5039420981/10000000000 : ℝ)^4257 ≤ (40561551947539/100000000000000 : ℝ)^3233 := by
    have hnat : (5039420981 : ℕ)^4257*100000000000000^3233 ≤ 40561551947539^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5039420981 10000000000 40561551947539 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (282728927/500000000 : ℝ)^4257 ≤ (47203810337743/100000000000000 : ℝ)^3233 := by
    have hnat : (282728927 : ℕ)^4257*100000000000000^3233 ≤ 47203810337743^3233*500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282728927 500000000 47203810337743 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2027993203/10000000000 : ℝ), (5039420981/10000000000 : ℝ), (282728927/500000000 : ℝ)] ![(3058659425841/25000000000000 : ℝ), (40561551947539/100000000000000 : ℝ), (47203810337743/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2027993203/10000000000 : ℝ)|^4257 ≤ (3058659425841/25000000000000 : ℝ)^3233
        have hw : |(-2027993203/10000000000 : ℝ)|=(2027993203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5039420981/10000000000 : ℝ)|^4257 ≤ (40561551947539/100000000000000 : ℝ)^3233
        have hw : |(5039420981/10000000000 : ℝ)|=(5039420981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(282728927/500000000 : ℝ)|^4257 ≤ (47203810337743/100000000000000 : ℝ)^3233
        have hw : |(282728927/500000000 : ℝ)|=(282728927/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s1_5 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5247169319/10000000000 : ℝ)*x 0 + (-871222159/5000000000 : ℝ)*x 1 + (5654579259/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5247169319/10000000000 : ℝ)^4257 ≤ (42777550914437/100000000000000 : ℝ)^3233 := by
    have hnat : (5247169319 : ℕ)^4257*100000000000000^3233 ≤ 42777550914437^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247169319 10000000000 42777550914437 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (871222159/5000000000 : ℝ)^4257 ≤ (10018630837519/100000000000000 : ℝ)^3233 := by
    have hnat : (871222159 : ℕ)^4257*100000000000000^3233 ≤ 10018630837519^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871222159 5000000000 10018630837519 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5654579259/10000000000 : ℝ)^4257 ≤ (11800954560239/25000000000000 : ℝ)^3233 := by
    have hnat : (5654579259 : ℕ)^4257*25000000000000^3233 ≤ 11800954560239^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5654579259 10000000000 11800954560239 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5247169319/10000000000 : ℝ), (-871222159/5000000000 : ℝ), (5654579259/10000000000 : ℝ)] ![(42777550914437/100000000000000 : ℝ), (10018630837519/100000000000000 : ℝ), (11800954560239/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5247169319/10000000000 : ℝ)|^4257 ≤ (42777550914437/100000000000000 : ℝ)^3233
        have hw : |(5247169319/10000000000 : ℝ)|=(5247169319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-871222159/5000000000 : ℝ)|^4257 ≤ (10018630837519/100000000000000 : ℝ)^3233
        have hw : |(-871222159/5000000000 : ℝ)|=(871222159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5654579259/10000000000 : ℝ)|^4257 ≤ (11800954560239/25000000000000 : ℝ)^3233
        have hw : |(5654579259/10000000000 : ℝ)|=(5654579259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s1_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (327948077/625000000 : ℝ)*x 0 + (113091577/200000000 : ℝ)*x 1 + (-348489007/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327948077/625000000 : ℝ)^4257 ≤ (42777549980521/100000000000000 : ℝ)^3233 := by
    have hnat : (327948077 : ℕ)^4257*100000000000000^3233 ≤ 42777549980521^3233*625000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327948077 625000000 42777549980521 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113091577/200000000 : ℝ)^4257 ≤ (1475119179539/3125000000000 : ℝ)^3233 := by
    have hnat : (113091577 : ℕ)^4257*3125000000000^3233 ≤ 1475119179539^3233*200000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113091577 200000000 1475119179539 3125000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (348489007/2000000000 : ℝ)^4257 ≤ (5009318132927/50000000000000 : ℝ)^3233 := by
    have hnat : (348489007 : ℕ)^4257*50000000000000^3233 ≤ 5009318132927^3233*2000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      348489007 2000000000 5009318132927 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327948077/625000000 : ℝ), (113091577/200000000 : ℝ), (-348489007/2000000000 : ℝ)] ![(42777549980521/100000000000000 : ℝ), (1475119179539/3125000000000 : ℝ), (5009318132927/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327948077/625000000 : ℝ)|^4257 ≤ (42777549980521/100000000000000 : ℝ)^3233
        have hw : |(327948077/625000000 : ℝ)|=(327948077/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(113091577/200000000 : ℝ)|^4257 ≤ (1475119179539/3125000000000 : ℝ)^3233
        have hw : |(113091577/200000000 : ℝ)|=(113091577/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-348489007/2000000000 : ℝ)|^4257 ≤ (5009318132927/50000000000000 : ℝ)^3233
        have hw : |(-348489007/2000000000 : ℝ)|=(348489007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s1_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075387637/2500000000 : ℝ)*x 0 + (1245067791/2500000000 : ℝ)*x 1 + (3713559583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075387637/2500000000 : ℝ)^4257 ≤ (6585848448893/20000000000000 : ℝ)^3233 := by
    have hnat : (1075387637 : ℕ)^4257*20000000000000^3233 ≤ 6585848448893^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075387637 2500000000 6585848448893 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1245067791/2500000000 : ℝ)^4257 ≤ (19967919547463/50000000000000 : ℝ)^3233 := by
    have hnat : (1245067791 : ℕ)^4257*50000000000000^3233 ≤ 19967919547463^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245067791 2500000000 19967919547463 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3713559583/10000000000 : ℝ)^4257 ≤ (3391864830851/12500000000000 : ℝ)^3233 := by
    have hnat : (3713559583 : ℕ)^4257*12500000000000^3233 ≤ 3391864830851^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3713559583 10000000000 3391864830851 12500000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075387637/2500000000 : ℝ), (1245067791/2500000000 : ℝ), (3713559583/10000000000 : ℝ)] ![(6585848448893/20000000000000 : ℝ), (19967919547463/50000000000000 : ℝ), (3391864830851/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075387637/2500000000 : ℝ)|^4257 ≤ (6585848448893/20000000000000 : ℝ)^3233
        have hw : |(1075387637/2500000000 : ℝ)|=(1075387637/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1245067791/2500000000 : ℝ)|^4257 ≤ (19967919547463/50000000000000 : ℝ)^3233
        have hw : |(1245067791/2500000000 : ℝ)|=(1245067791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3713559583/10000000000 : ℝ)|^4257 ≤ (3391864830851/12500000000000 : ℝ)^3233
        have hw : |(3713559583/10000000000 : ℝ)|=(3713559583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1297_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27199/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1071/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3229/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1981/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27199/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1071/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27199/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1071/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27199/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1071/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27199/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1071/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27199/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1071/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27199/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1071/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1071/100000 : ℝ) ^ (133/32 : ℝ) ≤ (161902105547/25000000000000000000 : ℝ) := by
    have hpowers : (1071/100000 : ℝ)^133 ≤ (161902105547/25000000000000000000 : ℝ)^32 := by
      have hnat : (1071 : ℕ)^133*25000000000000000000^32 ≤ 161902105547^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1071 100000 161902105547 25000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1071/100000 : ℝ)) (X := (161902105547/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hpowhi : (27199/100000 : ℝ) ^ (133/32 : ℝ) ≤ (446540284292189443/100000000000000000000 : ℝ) := by
    have hpowers : (27199/100000 : ℝ)^133 ≤ (446540284292189443/100000000000000000000 : ℝ)^32 := by
      have hnat : (27199 : ℕ)^133*100000000000000000000^32 ≤ 446540284292189443^32*100000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27199 100000 446540284292189443 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27199/100000 : ℝ)) (X := (446540284292189443/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000161902105547/12500000000000000000 : ℝ) ≤ (1250000003895389/1250000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (12500000161902105547/12500000000000000000 : ℝ)^32 ≤ (1250000003895389/1250000000000000 : ℝ)^133 := by
      have hnat : (12500000161902105547 : ℕ)^32*1250000000000000^133 ≤ 1250000003895389^133*12500000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000161902105547 12500000000000000000 1250000003895389 1250000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000003895389/1250000000000000 : ℝ)) (X := (12500000161902105547/12500000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (100446540931900611631/100000000000000000000 : ℝ) ≤ (10010725673210171/10000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (100446540931900611631/100000000000000000000 : ℝ)^32 ≤ (10010725673210171/10000000000000000 : ℝ)^133 := by
      have hnat : (100446540931900611631 : ℕ)^32*10000000000000000^133 ≤ 10010725673210171^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100446540931900611631 100000000000000000000 10010725673210171 10000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10010725673210171/10000000000000000 : ℝ)) (X := (100446540931900611631/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (50446540284292189443/50000000000000000000 : ℝ) ≤ (1002145131525723/1000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50446540284292189443/50000000000000000000 : ℝ)^32 ≤ (1002145131525723/1000000000000000 : ℝ)^133 := by
      have hnat : (50446540284292189443 : ℕ)^32*1000000000000000^133 ≤ 1002145131525723^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50446540284292189443 50000000000000000000 1002145131525723 1000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1002145131525723/1000000000000000 : ℝ)) (X := (50446540284292189443/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(161902105547/25000000000000000000 : ℝ) ≤ ((130628513244482494979/130640000000000000000 : ℝ)+2*(10725642047059/2612800000000000 : ℝ)*(1071/100000 : ℝ))^(133/32 : ℝ) := by
    rw [show (130628513244482494979/130640000000000000000 : ℝ)+2*(10725642047059/2612800000000000 : ℝ)*(1071/100000 : ℝ)=(1250000003895389/1250000000000000 : ℝ) by norm_num, show 1+2*(161902105547/25000000000000000000 : ℝ)=(12500000161902105547/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(446540284292189443/100000000000000000000 : ℝ)+(161902105547/25000000000000000000 : ℝ) ≤ ((130628513244482494979/130640000000000000000 : ℝ)+(10725642047059/2612800000000000 : ℝ)*((27199/100000 : ℝ)+(1071/100000 : ℝ)))^(133/32 : ℝ) := by
    rw [show (130628513244482494979/130640000000000000000 : ℝ)+(10725642047059/2612800000000000 : ℝ)*((27199/100000 : ℝ)+(1071/100000 : ℝ))=(10010725673210171/10000000000000000 : ℝ) by norm_num, show 1+(446540284292189443/100000000000000000000 : ℝ)+(161902105547/25000000000000000000 : ℝ)=(100446540931900611631/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(446540284292189443/100000000000000000000 : ℝ) ≤ ((130628513244482494979/130640000000000000000 : ℝ)+2*(10725642047059/2612800000000000 : ℝ)*(27199/100000 : ℝ))^(133/32 : ℝ) := by
    rw [show (130628513244482494979/130640000000000000000 : ℝ)+2*(10725642047059/2612800000000000 : ℝ)*(27199/100000 : ℝ)=(1002145131525723/1000000000000000 : ℝ) by norm_num, show 1+2*(446540284292189443/100000000000000000000 : ℝ)=(50446540284292189443/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (130628513244482494979/130640000000000000000 : ℝ)*(X 1 0+X 2 0)+(10725642047059/2612800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (1071/100000 : ℝ)) (hi := (27199/100000 : ℝ)) (c := (130628513244482494979/130640000000000000000 : ℝ)) (alpha := (10725642047059/2612800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (130628513244482494979/130640000000000000000 : ℝ)*(X 0 1+X 2 1)+(10725642047059/2612800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (1071/100000 : ℝ)) (hi := (27199/100000 : ℝ)) (c := (130628513244482494979/130640000000000000000 : ℝ)) (alpha := (10725642047059/2612800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (130628513244482494979/130640000000000000000 : ℝ)*(X 0 2+X 1 2)+(10725642047059/2612800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (1071/100000 : ℝ)) (hi := (27199/100000 : ℝ)) (c := (130628513244482494979/130640000000000000000 : ℝ)) (alpha := (10725642047059/2612800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2027366873/10000000000 : ℝ)*X 0 0+(1415734623/2500000000 : ℝ)*X 0 1+(1257803929/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1082091523/2000000000 : ℝ)*X 1 0+(-473161513/2000000000 : ℝ)*X 1 1+(5031215837/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((270522883/500000000 : ℝ)*X 2 0+(5031215659/10000000000 : ℝ)*X 2 1+(-2365807733/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4300261631/10000000000 : ℝ)*X 0 0+(462043243/1250000000 : ℝ)*X 0 1+(312322911/625000000 : ℝ)*X 0 2+(4300261631/10000000000 : ℝ)*X 1 0+(462043243/1250000000 : ℝ)*X 1 1+(312322911/625000000 : ℝ)*X 1 2+(4300261631/10000000000 : ℝ)*X 2 0+(462043243/1250000000 : ℝ)*X 2 1+(312322911/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2027993203/10000000000 : ℝ)*X 0 0+(5039420981/10000000000 : ℝ)*X 0 1+(282728927/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5247169319/10000000000 : ℝ)*X 1 0+(-871222159/5000000000 : ℝ)*X 1 1+(5654579259/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((327948077/625000000 : ℝ)*X 2 0+(113091577/200000000 : ℝ)*X 2 1+(-348489007/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1075387637/2500000000 : ℝ)*X 0 0+(1245067791/2500000000 : ℝ)*X 0 1+(3713559583/10000000000 : ℝ)*X 0 2+(1075387637/2500000000 : ℝ)*X 1 0+(1245067791/2500000000 : ℝ)*X 1 1+(3713559583/10000000000 : ℝ)*X 1 2+(1075387637/2500000000 : ℝ)*X 2 0+(1245067791/2500000000 : ℝ)*X 2 1+(3713559583/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8214972066949595855193323283/1306400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (14621039/25000000000000 : ℝ)*(base1) + (1173638041/100000000000000 : ℝ)*(base19) + (237360817/20000000000000 : ℝ)*(base23) + (33437341/20000000000000 : ℝ)*(upper3) + (105217051/100000000000000 : ℝ)*(upper5) + (235173831923941/20000000000000 : ℝ)*(major0) + (235173831923941/20000000000000 : ℝ)*(major1) + (235173831923941/20000000000000 : ℝ)*(major2) + (395744955270047/25000000000000 : ℝ)*(sp0) + (316597019435471/20000000000000 : ℝ)*(sp1) + (158298508401131/10000000000000 : ℝ)*(sp2) + (768748445750019/100000000000000 : ℝ)*(sp3) + (6508219363/100000000000000 : ℝ)*(sp4) + (3334581439/100000000000000 : ℝ)*(sp7) + (768751838815613/100000000000000 : ℝ)*(f.failure) + (395746567703849/25000000000000 : ℝ)*(f.sum) + (1516827456809/1045120000000000000000000000 : ℝ)*base66 + (15608883177821542239/2612800000000000000000000000000000 : ℝ)*base67 + (10187029884696857761/2612800000000000000000000000000000 : ℝ)*base70 + (4183740147877542239/2612800000000000000000000000000000 : ℝ)*base71 + (7735259084177/26128000000000000000000000000 : ℝ)*base74 + (7259822534186457761/2612800000000000000000000000000000 : ℝ)*base76 + (3267101256557542239/2612800000000000000000000000000000 : ℝ)*base77 + (23685958039576742239/2612800000000000000000000000000000 : ℝ)*base79 + (154284005021809/26128000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (4503043/625000000000000000000 : ℝ)*base90 + (4503043/625000000000000000000 : ℝ)*base92 + (4503043/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21530381378402479526263527639/6532000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (99678311/20000000000000 : ℝ)*(base19) + (262806667/50000000000000 : ℝ)*(base23) + (23246353/50000000000000 : ℝ)*(upper2) + (61950051/50000000000000 : ℝ)*(upper3) + (16834777/25000000000000 : ℝ)*(upper5) + (1207522274821153/100000000000000 : ℝ)*(major0) + (1207522274821153/100000000000000 : ℝ)*(major1) + (1207522274821153/100000000000000 : ℝ)*(major2) + (3361643181/100000000000000 : ℝ)*(sp1) + (563809467/25000000000000 : ℝ)*(sp2) + (325119727993613/20000000000000 : ℝ)*(sp4) + (101599673745833/6250000000000 : ℝ)*(sp5) + (25399935298701/1562500000000 : ℝ)*(sp6) + (789445799802927/100000000000000 : ℝ)*(sp7) + (789445799802927/100000000000000 : ℝ)*(f.failure) + (325119727993613/20000000000000 : ℝ)*(f.sum) + (164238846243613/130640000000000000000000000000 : ℝ)*base66 + (28822538816644840787/13064000000000000000000000000000000 : ℝ)*base67 + (52536889724772840787/13064000000000000000000000000000000 : ℝ)*base69 + (102534563049044840787/13064000000000000000000000000000000 : ℝ)*base71 + (35716606604733/130640000000000000000000000000 : ℝ)*base74 + (54266872301436840787/13064000000000000000000000000000000 : ℝ)*base75 + (33518640968339159213/13064000000000000000000000000000000 : ℝ)*base78 + (12631226891763159213/13064000000000000000000000000000000 : ℝ)*base80 + (741082746816547/130640000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base87 + (2254897/625000000000000000000 : ℝ)*base90 + (2254897/625000000000000000000 : ℝ)*base92 + (2254897/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1297_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27199/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1071/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3229/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1981/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1297_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1297_s2_0 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2071596353/10000000000 : ℝ)*x 0 + (5492727023/10000000000 : ℝ)*x 1 + (5173168321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2071596353/10000000000 : ℝ)^4257 ≤ (6291090746443/50000000000000 : ℝ)^3233 := by
    have hnat : (2071596353 : ℕ)^4257*50000000000000^3233 ≤ 6291090746443^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2071596353 10000000000 6291090746443 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5492727023/10000000000 : ℝ)^4257 ≤ (45432864104431/100000000000000 : ℝ)^3233 := by
    have hnat : (5492727023 : ℕ)^4257*100000000000000^3233 ≤ 45432864104431^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5492727023 10000000000 45432864104431 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5173168321/10000000000 : ℝ)^4257 ≤ (2624059649961/6250000000000 : ℝ)^3233 := by
    have hnat : (5173168321 : ℕ)^4257*6250000000000^3233 ≤ 2624059649961^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173168321 10000000000 2624059649961 6250000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2071596353/10000000000 : ℝ), (5492727023/10000000000 : ℝ), (5173168321/10000000000 : ℝ)] ![(6291090746443/50000000000000 : ℝ), (45432864104431/100000000000000 : ℝ), (2624059649961/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2071596353/10000000000 : ℝ)|^4257 ≤ (6291090746443/50000000000000 : ℝ)^3233
        have hw : |(-2071596353/10000000000 : ℝ)|=(2071596353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5492727023/10000000000 : ℝ)|^4257 ≤ (45432864104431/100000000000000 : ℝ)^3233
        have hw : |(5492727023/10000000000 : ℝ)|=(5492727023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5173168321/10000000000 : ℝ)|^4257 ≤ (2624059649961/6250000000000 : ℝ)^3233
        have hw : |(5173168321/10000000000 : ℝ)|=(5173168321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s2_1 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2684605451/5000000000 : ℝ)*x 0 + (-559286791/2500000000 : ℝ)*x 1 + (5173168309/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684605451/5000000000 : ℝ)^4257 ≤ (8818485498537/20000000000000 : ℝ)^3233 := by
    have hnat : (2684605451 : ℕ)^4257*20000000000000^3233 ≤ 8818485498537^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684605451 5000000000 8818485498537 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (559286791/2500000000 : ℝ)^4257 ≤ (13922618216747/100000000000000 : ℝ)^3233 := by
    have hnat : (559286791 : ℕ)^4257*100000000000000^3233 ≤ 13922618216747^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      559286791 2500000000 13922618216747 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5173168309/10000000000 : ℝ)^4257 ≤ (20992477135569/50000000000000 : ℝ)^3233 := by
    have hnat : (5173168309 : ℕ)^4257*50000000000000^3233 ≤ 20992477135569^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173168309 10000000000 20992477135569 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684605451/5000000000 : ℝ), (-559286791/2500000000 : ℝ), (5173168309/10000000000 : ℝ)] ![(8818485498537/20000000000000 : ℝ), (13922618216747/100000000000000 : ℝ), (20992477135569/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684605451/5000000000 : ℝ)|^4257 ≤ (8818485498537/20000000000000 : ℝ)^3233
        have hw : |(2684605451/5000000000 : ℝ)|=(2684605451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-559286791/2500000000 : ℝ)|^4257 ≤ (13922618216747/100000000000000 : ℝ)^3233
        have hw : |(-559286791/2500000000 : ℝ)|=(559286791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5173168309/10000000000 : ℝ)|^4257 ≤ (20992477135569/50000000000000 : ℝ)^3233
        have hw : |(5173168309/10000000000 : ℝ)|=(5173168309/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s2_2 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268460539/500000000 : ℝ)*x 0 + (5173168331/10000000000 : ℝ)*x 1 + (-2237147297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268460539/500000000 : ℝ)^4257 ≤ (44092426173483/100000000000000 : ℝ)^3233 := by
    have hnat : (268460539 : ℕ)^4257*100000000000000^3233 ≤ 44092426173483^3233*500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268460539 500000000 44092426173483 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5173168331/10000000000 : ℝ)^4257 ≤ (41984954506241/100000000000000 : ℝ)^3233 := by
    have hnat : (5173168331 : ℕ)^4257*100000000000000^3233 ≤ 41984954506241^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173168331 10000000000 41984954506241 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2237147297/10000000000 : ℝ)^4257 ≤ (696130965331/5000000000000 : ℝ)^3233 := by
    have hnat : (2237147297 : ℕ)^4257*5000000000000^3233 ≤ 696130965331^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237147297 10000000000 696130965331 5000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268460539/500000000 : ℝ), (5173168331/10000000000 : ℝ), (-2237147297/10000000000 : ℝ)] ![(44092426173483/100000000000000 : ℝ), (41984954506241/100000000000000 : ℝ), (696130965331/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268460539/500000000 : ℝ)|^4257 ≤ (44092426173483/100000000000000 : ℝ)^3233
        have hw : |(268460539/500000000 : ℝ)|=(268460539/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5173168331/10000000000 : ℝ)|^4257 ≤ (41984954506241/100000000000000 : ℝ)^3233
        have hw : |(5173168331/10000000000 : ℝ)|=(5173168331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2237147297/10000000000 : ℝ)|^4257 ≤ (696130965331/5000000000000 : ℝ)^3233
        have hw : |(-2237147297/10000000000 : ℝ)|=(2237147297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s2_3 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1082756291/2500000000 : ℝ)*x 0 + (4013890411/10000000000 : ℝ)*x 1 + (1167980517/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082756291/2500000000 : ℝ)^4257 ≤ (6645332849153/20000000000000 : ℝ)^3233 := by
    have hnat : (1082756291 : ℕ)^4257*20000000000000^3233 ≤ 6645332849153^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082756291 2500000000 6645332849153 20000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4013890411/10000000000 : ℝ)^4257 ≤ (30060856809111/100000000000000 : ℝ)^3233 := by
    have hnat : (4013890411 : ℕ)^4257*100000000000000^3233 ≤ 30060856809111^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4013890411 10000000000 30060856809111 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1167980517/2500000000 : ℝ)^4257 ≤ (9178119733413/25000000000000 : ℝ)^3233 := by
    have hnat : (1167980517 : ℕ)^4257*25000000000000^3233 ≤ 9178119733413^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1167980517 2500000000 9178119733413 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082756291/2500000000 : ℝ), (4013890411/10000000000 : ℝ), (1167980517/2500000000 : ℝ)] ![(6645332849153/20000000000000 : ℝ), (30060856809111/100000000000000 : ℝ), (9178119733413/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082756291/2500000000 : ℝ)|^4257 ≤ (6645332849153/20000000000000 : ℝ)^3233
        have hw : |(1082756291/2500000000 : ℝ)|=(1082756291/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4013890411/10000000000 : ℝ)|^4257 ≤ (30060856809111/100000000000000 : ℝ)^3233
        have hw : |(4013890411/10000000000 : ℝ)|=(4013890411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1167980517/2500000000 : ℝ)|^4257 ≤ (9178119733413/25000000000000 : ℝ)^3233
        have hw : |(1167980517/2500000000 : ℝ)|=(1167980517/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s2_4 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-207167673/1000000000 : ℝ)*x 0 + (20701109/40000000 : ℝ)*x 1 + (1372649617/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207167673/1000000000 : ℝ)^4257 ≤ (157285303797/1250000000000 : ℝ)^3233 := by
    have hnat : (207167673 : ℕ)^4257*1250000000000^3233 ≤ 157285303797^3233*1000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207167673 1000000000 157285303797 1250000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20701109/40000000 : ℝ)^4257 ≤ (42007492899719/100000000000000 : ℝ)^3233 := by
    have hnat : (20701109 : ℕ)^4257*100000000000000^3233 ≤ 42007492899719^3233*40000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20701109 40000000 42007492899719 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1372649617/2500000000 : ℝ)^4257 ≤ (22704841389453/50000000000000 : ℝ)^3233 := by
    have hnat : (1372649617 : ℕ)^4257*50000000000000^3233 ≤ 22704841389453^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1372649617 2500000000 22704841389453 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-207167673/1000000000 : ℝ), (20701109/40000000 : ℝ), (1372649617/2500000000 : ℝ)] ![(157285303797/1250000000000 : ℝ), (42007492899719/100000000000000 : ℝ), (22704841389453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-207167673/1000000000 : ℝ)|^4257 ≤ (157285303797/1250000000000 : ℝ)^3233
        have hw : |(-207167673/1000000000 : ℝ)|=(207167673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(20701109/40000000 : ℝ)|^4257 ≤ (42007492899719/100000000000000 : ℝ)^3233
        have hw : |(20701109/40000000 : ℝ)|=(20701109/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1372649617/2500000000 : ℝ)|^4257 ≤ (22704841389453/50000000000000 : ℝ)^3233
        have hw : |(1372649617/2500000000 : ℝ)|=(1372649617/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s2_5 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1057452031/2000000000 : ℝ)*x 0 + (-959858213/5000000000 : ℝ)*x 1 + (2745299297/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057452031/2000000000 : ℝ)^4257 ≤ (21604216363697/50000000000000 : ℝ)^3233 := by
    have hnat : (1057452031 : ℕ)^4257*50000000000000^3233 ≤ 21604216363697^3233*2000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057452031 2000000000 21604216363697 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (959858213/5000000000 : ℝ)^4257 ≤ (5690941554217/50000000000000 : ℝ)^3233 := by
    have hnat : (959858213 : ℕ)^4257*50000000000000^3233 ≤ 5690941554217^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959858213 5000000000 5690941554217 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745299297/5000000000 : ℝ)^4257 ≤ (22704842075521/50000000000000 : ℝ)^3233 := by
    have hnat : (2745299297 : ℕ)^4257*50000000000000^3233 ≤ 22704842075521^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745299297 5000000000 22704842075521 50000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057452031/2000000000 : ℝ), (-959858213/5000000000 : ℝ), (2745299297/5000000000 : ℝ)] ![(21604216363697/50000000000000 : ℝ), (5690941554217/50000000000000 : ℝ), (22704842075521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057452031/2000000000 : ℝ)|^4257 ≤ (21604216363697/50000000000000 : ℝ)^3233
        have hw : |(1057452031/2000000000 : ℝ)|=(1057452031/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-959858213/5000000000 : ℝ)|^4257 ≤ (5690941554217/50000000000000 : ℝ)^3233
        have hw : |(-959858213/5000000000 : ℝ)|=(959858213/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745299297/5000000000 : ℝ)|^4257 ≤ (22704842075521/50000000000000 : ℝ)^3233
        have hw : |(2745299297/5000000000 : ℝ)|=(2745299297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s2_6 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528726031/1000000000 : ℝ)*x 0 + (219623939/400000000 : ℝ)*x 1 + (-1919716379/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528726031/1000000000 : ℝ)^4257 ≤ (10802108598821/25000000000000 : ℝ)^3233 := by
    have hnat : (528726031 : ℕ)^4257*25000000000000^3233 ≤ 10802108598821^3233*1000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528726031 1000000000 10802108598821 25000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (219623939/400000000 : ℝ)^4257 ≤ (1419052589223/3125000000000 : ℝ)^3233 := by
    have hnat : (219623939 : ℕ)^4257*3125000000000^3233 ≤ 1419052589223^3233*400000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219623939 400000000 1419052589223 3125000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1919716379/10000000000 : ℝ)^4257 ≤ (11381882741513/100000000000000 : ℝ)^3233 := by
    have hnat : (1919716379 : ℕ)^4257*100000000000000^3233 ≤ 11381882741513^3233*10000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1919716379 10000000000 11381882741513 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528726031/1000000000 : ℝ), (219623939/400000000 : ℝ), (-1919716379/10000000000 : ℝ)] ![(10802108598821/25000000000000 : ℝ), (1419052589223/3125000000000 : ℝ), (11381882741513/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528726031/1000000000 : ℝ)|^4257 ≤ (10802108598821/25000000000000 : ℝ)^3233
        have hw : |(528726031/1000000000 : ℝ)|=(528726031/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(219623939/400000000 : ℝ)|^4257 ≤ (1419052589223/3125000000000 : ℝ)^3233
        have hw : |(219623939/400000000 : ℝ)|=(219623939/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1919716379/10000000000 : ℝ)|^4257 ≤ (11381882741513/100000000000000 : ℝ)^3233
        have hw : |(-1919716379/10000000000 : ℝ)|=(1919716379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1297_s2_7 (p : ℝ) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2165595027/5000000000 : ℝ)*x 0 + (2333788821/5000000000 : ℝ)*x 1 + (1004569623/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2165595027/5000000000 : ℝ)^4257 ≤ (1661416496163/5000000000000 : ℝ)^3233 := by
    have hnat : (2165595027 : ℕ)^4257*5000000000000^3233 ≤ 1661416496163^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165595027 5000000000 1661416496163 5000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2333788821/5000000000 : ℝ)^4257 ≤ (2291720850733/6250000000000 : ℝ)^3233 := by
    have hnat : (2333788821 : ℕ)^4257*6250000000000^3233 ≤ 2291720850733^3233*5000000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2333788821 5000000000 2291720850733 6250000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004569623/2500000000 : ℝ)^4257 ≤ (30104136444111/100000000000000 : ℝ)^3233 := by
    have hnat : (1004569623 : ℕ)^4257*100000000000000^3233 ≤ 30104136444111^3233*2500000000^4257 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004569623 2500000000 30104136444111 100000000000000 4257 3233 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4257/1024 : ℝ)) 4257 3233 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2165595027/5000000000 : ℝ), (2333788821/5000000000 : ℝ), (1004569623/2500000000 : ℝ)] ![(1661416496163/5000000000000 : ℝ), (2291720850733/6250000000000 : ℝ), (30104136444111/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2165595027/5000000000 : ℝ)|^4257 ≤ (1661416496163/5000000000000 : ℝ)^3233
        have hw : |(2165595027/5000000000 : ℝ)|=(2165595027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2333788821/5000000000 : ℝ)|^4257 ≤ (2291720850733/6250000000000 : ℝ)^3233
        have hw : |(2333788821/5000000000 : ℝ)|=(2333788821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1004569623/2500000000 : ℝ)|^4257 ≤ (30104136444111/100000000000000 : ℝ)^3233
        have hw : |(1004569623/2500000000 : ℝ)|=(1004569623/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1297_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1981/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3229/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9541/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3259/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1981/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3229/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1981/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3229/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1981/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3229/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1981/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3229/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1981/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3229/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1981/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3229/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3229/50000 : ℝ) ^ (133/32 : ℝ) ≤ (113362647917581/10000000000000000000 : ℝ) := by
    have hpowers : (3229/50000 : ℝ)^133 ≤ (113362647917581/10000000000000000000 : ℝ)^32 := by
      have hnat : (3229 : ℕ)^133*10000000000000000000^32 ≤ 113362647917581^32*50000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3229 50000 113362647917581 10000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3229/50000 : ℝ)) (X := (113362647917581/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hpowhi : (1981/10000 : ℝ) ^ (133/32 : ℝ) ≤ (119584833022892637/100000000000000000000 : ℝ) := by
    have hpowers : (1981/10000 : ℝ)^133 ≤ (119584833022892637/100000000000000000000 : ℝ)^32 := by
      have hnat : (1981 : ℕ)^133*100000000000000000000^32 ≤ 119584833022892637^32*10000^133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1981 10000 119584833022892637 100000000000000000000 133 32 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1981/10000 : ℝ)) (X := (119584833022892637/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000113362647917581/5000000000000000000 : ℝ) ≤ (5000027274988757/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (5000113362647917581/5000000000000000000 : ℝ)^32 ≤ (5000027274988757/5000000000000000 : ℝ)^133 := by
      have hnat : (5000113362647917581 : ℕ)^32*5000000000000000^133 ≤ 5000027274988757^133*5000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000113362647917581 5000000000000000000 5000027274988757 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000027274988757/5000000000000000 : ℝ)) (X := (5000113362647917581/5000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner10 : (100120718459502068447/100000000000000000000 : ℝ) ≤ (5001451586950687/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (100120718459502068447/100000000000000000000 : ℝ)^32 ≤ (5001451586950687/5000000000000000 : ℝ)^133 := by
      have hnat : (100120718459502068447 : ℕ)^32*5000000000000000^133 ≤ 5001451586950687^133*100000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100120718459502068447 100000000000000000000 5001451586950687 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001451586950687/5000000000000000 : ℝ)) (X := (100120718459502068447/100000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have hcorner11 : (50119584833022892637/50000000000000000000 : ℝ) ≤ (5002875898912617/5000000000000000 : ℝ) ^ (133/32 : ℝ) := by
    have hpowers : (50119584833022892637/50000000000000000000 : ℝ)^32 ≤ (5002875898912617/5000000000000000 : ℝ)^133 := by
      have hnat : (50119584833022892637 : ℕ)^32*5000000000000000^133 ≤ 5002875898912617^133*50000000000000000000^32 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50119584833022892637 50000000000000000000 5002875898912617 5000000000000000 32 133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002875898912617/5000000000000000 : ℝ)) (X := (50119584833022892637/50000000000000000000 : ℝ)) (by norm_num) 133 32 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(113362647917581/10000000000000000000 : ℝ) ≤ ((1042843246286712431/1043125000000000000 : ℝ)+2*(142431196193/66760000000000 : ℝ)*(3229/50000 : ℝ))^(133/32 : ℝ) := by
    rw [show (1042843246286712431/1043125000000000000 : ℝ)+2*(142431196193/66760000000000 : ℝ)*(3229/50000 : ℝ)=(5000027274988757/5000000000000000 : ℝ) by norm_num, show 1+2*(113362647917581/10000000000000000000 : ℝ)=(5000113362647917581/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(119584833022892637/100000000000000000000 : ℝ)+(113362647917581/10000000000000000000 : ℝ) ≤ ((1042843246286712431/1043125000000000000 : ℝ)+(142431196193/66760000000000 : ℝ)*((1981/10000 : ℝ)+(3229/50000 : ℝ)))^(133/32 : ℝ) := by
    rw [show (1042843246286712431/1043125000000000000 : ℝ)+(142431196193/66760000000000 : ℝ)*((1981/10000 : ℝ)+(3229/50000 : ℝ))=(5001451586950687/5000000000000000 : ℝ) by norm_num, show 1+(119584833022892637/100000000000000000000 : ℝ)+(113362647917581/10000000000000000000 : ℝ)=(100120718459502068447/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(119584833022892637/100000000000000000000 : ℝ) ≤ ((1042843246286712431/1043125000000000000 : ℝ)+2*(142431196193/66760000000000 : ℝ)*(1981/10000 : ℝ))^(133/32 : ℝ) := by
    rw [show (1042843246286712431/1043125000000000000 : ℝ)+2*(142431196193/66760000000000 : ℝ)*(1981/10000 : ℝ)=(5002875898912617/5000000000000000 : ℝ) by norm_num, show 1+2*(119584833022892637/100000000000000000000 : ℝ)=(50119584833022892637/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1042843246286712431/1043125000000000000 : ℝ)*(X 1 0+X 2 0)+(142431196193/66760000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (3229/50000 : ℝ)) (hi := (1981/10000 : ℝ)) (c := (1042843246286712431/1043125000000000000 : ℝ)) (alpha := (142431196193/66760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1042843246286712431/1043125000000000000 : ℝ)*(X 0 1+X 2 1)+(142431196193/66760000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (3229/50000 : ℝ)) (hi := (1981/10000 : ℝ)) (c := (1042843246286712431/1043125000000000000 : ℝ)) (alpha := (142431196193/66760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1042843246286712431/1043125000000000000 : ℝ)*(X 0 2+X 1 2)+(142431196193/66760000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (133/32 : ℝ)) (lo := (3229/50000 : ℝ)) (hi := (1981/10000 : ℝ)) (c := (1042843246286712431/1043125000000000000 : ℝ)) (alpha := (142431196193/66760000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2071596353/10000000000 : ℝ)*X 0 0+(5492727023/10000000000 : ℝ)*X 0 1+(5173168321/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2684605451/5000000000 : ℝ)*X 1 0+(-559286791/2500000000 : ℝ)*X 1 1+(5173168309/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268460539/500000000 : ℝ)*X 2 0+(5173168331/10000000000 : ℝ)*X 2 1+(-2237147297/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1082756291/2500000000 : ℝ)*X 0 0+(4013890411/10000000000 : ℝ)*X 0 1+(1167980517/2500000000 : ℝ)*X 0 2+(1082756291/2500000000 : ℝ)*X 1 0+(4013890411/10000000000 : ℝ)*X 1 1+(1167980517/2500000000 : ℝ)*X 1 2+(1082756291/2500000000 : ℝ)*X 2 0+(4013890411/10000000000 : ℝ)*X 2 1+(1167980517/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-207167673/1000000000 : ℝ)*X 0 0+(20701109/40000000 : ℝ)*X 0 1+(1372649617/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1057452031/2000000000 : ℝ)*X 1 0+(-959858213/5000000000 : ℝ)*X 1 1+(2745299297/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((528726031/1000000000 : ℝ)*X 2 0+(219623939/400000000 : ℝ)*X 2 1+(-1919716379/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2165595027/5000000000 : ℝ)*X 0 0+(2333788821/5000000000 : ℝ)*X 0 1+(1004569623/2500000000 : ℝ)*X 0 2+(2165595027/5000000000 : ℝ)*X 1 0+(2333788821/5000000000 : ℝ)*X 1 1+(1004569623/2500000000 : ℝ)*X 1 2+(2165595027/5000000000 : ℝ)*X 2 0+(2333788821/5000000000 : ℝ)*X 2 1+(1004569623/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1297_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (56498938423862477627873439/10431250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1014936777/50000000000000 : ℝ)*(base19) + (1650426907/100000000000000 : ℝ)*(base23) + (82777459/50000000000000 : ℝ)*(lower2) + (119880923/20000000000000 : ℝ)*(upper3) + (235164083/100000000000000 : ℝ)*(upper5) + (2324530551722259/100000000000000 : ℝ)*(major0) + (2324530551722259/100000000000000 : ℝ)*(major1) + (116226527586113/5000000000000 : ℝ)*(major2) + (195583318241823/6250000000000 : ℝ)*(sp0) + (391167865855163/12500000000000 : ℝ)*(sp1) + (3129343306287951/100000000000000 : ℝ)*(sp2) + (759848959851369/50000000000000 : ℝ)*(sp3) + (1186484569/10000000000000 : ℝ)*(sp4) + (9023241537/50000000000000 : ℝ)*(sp7) + (379928991546453/25000000000000 : ℝ)*(f.failure) + (1564672478357429/50000000000000 : ℝ)*(f.sum) + (8109745023943/6676000000000000000000000000 : ℝ)*base65 + (364896465235639129/104312500000000000000000000000000 : ℝ)*base67 + (86736523850742187/20862500000000000000000000000000 : ℝ)*base69 + (598245087624764129/104312500000000000000000000000000 : ℝ)*base71 + (6381901223553/6676000000000000000000000000 : ℝ)*base74 + (124697822702342187/20862500000000000000000000000000 : ℝ)*base75 + (61529076458750187/13039062500000000000000000000000 : ℝ)*base78 + (76451322675797249/26078125000000000000000000000000 : ℝ)*base80 + (12645629651977/3338000000000000000000000000 : ℝ)*base81 + (663783/156250000000000000000 : ℝ)*base90 + (663783/156250000000000000000 : ℝ)*base92 + (2226283/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (523218494690988863304137961/52156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1914425533/100000000000000 : ℝ)*(base19) + (569000781/25000000000000 : ℝ)*(base23) + (274233297/100000000000000 : ℝ)*(upper3) + (103539637/100000000000000 : ℝ)*(lower4) + (77782469/50000000000000 : ℝ)*(upper5) + (2355744751825123/100000000000000 : ℝ)*(major0) + (2355744751825123/100000000000000 : ℝ)*(major1) + (2355744751825123/100000000000000 : ℝ)*(major2) + (19815917567/100000000000000 : ℝ)*(sp1) + (24511467219/100000000000000 : ℝ)*(sp2) + (158568309652481/5000000000000 : ℝ)*(sp4) + (79283611567663/2500000000000 : ℝ)*(sp5) + (3171339405579277/100000000000000 : ℝ)*(sp6) + (154012297620893/10000000000000 : ℝ)*(sp7) + (154012297620893/10000000000000 : ℝ)*(f.failure) + (158568309652481/5000000000000 : ℝ)*(f.sum) + (12156528305179/3338000000000000000000000000 : ℝ)*base65 + (27581985611562611/13039062500000000000000000000000 : ℝ)*base67 + (71450054736406139/13039062500000000000000000000000 : ℝ)*base70 + (572511540992243/6519531250000000000000000000000 : ℝ)*base71 + (9142394644163/3338000000000000000000000000 : ℝ)*base73 + (134748998324171653/26078125000000000000000000000000 : ℝ)*base76 + (5869039646992243/6519531250000000000000000000000 : ℝ)*base77 + (2076287659875111/13039062500000000000000000000000 : ℝ)*base79 + (644230749753/3338000000000000000000000000 : ℝ)*base82 + (714123/62500000000000000000 : ℝ)*base90 + (714123/62500000000000000000 : ℝ)*base92 + (714123/62500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1297_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1981/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3229/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9541/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1297_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1297_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9541/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1297_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1297_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1297_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (133/32 : ℝ) ≤ p) (hpb : p ≤ (4257/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9559889/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9541/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3259/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1297_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
