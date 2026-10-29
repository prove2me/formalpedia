-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1457_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T22:07:02.196375+00:00
-- url     : https://prove2.me/submissions/a851f434-b554-4112-afd5-3714bd9435c6

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
theorem support_rectangle_w1457_s3_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1947740999/10000000000 : ℝ)*x 0 + (5414546829/10000000000 : ℝ)*x 1 + (5240317723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1947740999/10000000000 : ℝ)^4417 ≤ (2377624510649/20000000000000 : ℝ)^3393 := by
    have hnat : (1947740999 : ℕ)^4417*20000000000000^3393 ≤ 2377624510649^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947740999 10000000000 2377624510649 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414546829/10000000000 : ℝ)^4417 ≤ (11248425855223/25000000000000 : ℝ)^3393 := by
    have hnat : (5414546829 : ℕ)^4417*25000000000000^3393 ≤ 11248425855223^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414546829 10000000000 11248425855223 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5240317723/10000000000 : ℝ)^4417 ≤ (43118174008333/100000000000000 : ℝ)^3393 := by
    have hnat : (5240317723 : ℕ)^4417*100000000000000^3393 ≤ 43118174008333^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240317723 10000000000 43118174008333 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1947740999/10000000000 : ℝ), (5414546829/10000000000 : ℝ), (5240317723/10000000000 : ℝ)] ![(2377624510649/20000000000000 : ℝ), (11248425855223/25000000000000 : ℝ), (43118174008333/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1947740999/10000000000 : ℝ)|^4417 ≤ (2377624510649/20000000000000 : ℝ)^3393
        have hw : |(-1947740999/10000000000 : ℝ)|=(1947740999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414546829/10000000000 : ℝ)|^4417 ≤ (11248425855223/25000000000000 : ℝ)^3393
        have hw : |(5414546829/10000000000 : ℝ)|=(5414546829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5240317723/10000000000 : ℝ)|^4417 ≤ (43118174008333/100000000000000 : ℝ)^3393
        have hw : |(5240317723/10000000000 : ℝ)|=(5240317723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s3_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069747237/2000000000 : ℝ)*x 0 + (-2036570409/10000000000 : ℝ)*x 1 + (1310079421/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069747237/2000000000 : ℝ)^4417 ≤ (11070773985981/25000000000000 : ℝ)^3393 := by
    have hnat : (1069747237 : ℕ)^4417*25000000000000^3393 ≤ 11070773985981^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069747237 2000000000 11070773985981 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2036570409/10000000000 : ℝ)^4417 ≤ (6299365224609/50000000000000 : ℝ)^3393 := by
    have hnat : (2036570409 : ℕ)^4417*50000000000000^3393 ≤ 6299365224609^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036570409 10000000000 6299365224609 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310079421/2500000000 : ℝ)^4417 ≤ (10779543397647/25000000000000 : ℝ)^3393 := by
    have hnat : (1310079421 : ℕ)^4417*25000000000000^3393 ≤ 10779543397647^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310079421 2500000000 10779543397647 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069747237/2000000000 : ℝ), (-2036570409/10000000000 : ℝ), (1310079421/2500000000 : ℝ)] ![(11070773985981/25000000000000 : ℝ), (6299365224609/50000000000000 : ℝ), (10779543397647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069747237/2000000000 : ℝ)|^4417 ≤ (11070773985981/25000000000000 : ℝ)^3393
        have hw : |(1069747237/2000000000 : ℝ)|=(1069747237/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2036570409/10000000000 : ℝ)|^4417 ≤ (6299365224609/50000000000000 : ℝ)^3393
        have hw : |(-2036570409/10000000000 : ℝ)|=(2036570409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310079421/2500000000 : ℝ)|^4417 ≤ (10779543397647/25000000000000 : ℝ)^3393
        have hw : |(1310079421/2500000000 : ℝ)|=(1310079421/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s3_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348736559/10000000000 : ℝ)*x 0 + (5240317513/10000000000 : ℝ)*x 1 + (-254571267/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348736559/10000000000 : ℝ)^4417 ≤ (5535387496853/12500000000000 : ℝ)^3393 := by
    have hnat : (5348736559 : ℕ)^4417*12500000000000^3393 ≤ 5535387496853^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348736559 10000000000 5535387496853 12500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240317513/10000000000 : ℝ)^4417 ≤ (43118171758939/100000000000000 : ℝ)^3393 := by
    have hnat : (5240317513 : ℕ)^4417*100000000000000^3393 ≤ 43118171758939^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240317513 10000000000 43118171758939 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (254571267/1250000000 : ℝ)^4417 ≤ (12598728250683/100000000000000 : ℝ)^3393 := by
    have hnat : (254571267 : ℕ)^4417*100000000000000^3393 ≤ 12598728250683^3393*1250000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254571267 1250000000 12598728250683 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348736559/10000000000 : ℝ), (5240317513/10000000000 : ℝ), (-254571267/1250000000 : ℝ)] ![(5535387496853/12500000000000 : ℝ), (43118171758939/100000000000000 : ℝ), (12598728250683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348736559/10000000000 : ℝ)|^4417 ≤ (5535387496853/12500000000000 : ℝ)^3393
        have hw : |(5348736559/10000000000 : ℝ)|=(5348736559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240317513/10000000000 : ℝ)|^4417 ≤ (43118171758939/100000000000000 : ℝ)^3393
        have hw : |(5240317513/10000000000 : ℝ)|=(5240317513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-254571267/1250000000 : ℝ)|^4417 ≤ (12598728250683/100000000000000 : ℝ)^3393
        have hw : |(-254571267/1250000000 : ℝ)|=(254571267/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s3_3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4296871971/10000000000 : ℝ)*x 0 + (4110225967/10000000000 : ℝ)*x 1 + (4491012369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296871971/10000000000 : ℝ)^4417 ≤ (33299568985577/100000000000000 : ℝ)^3393 := by
    have hnat : (4296871971 : ℕ)^4417*100000000000000^3393 ≤ 33299568985577^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296871971 10000000000 33299568985577 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4110225967/10000000000 : ℝ)^4417 ≤ (7857261681567/25000000000000 : ℝ)^3393 := by
    have hnat : (4110225967 : ℕ)^4417*25000000000000^3393 ≤ 7857261681567^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4110225967 10000000000 7857261681567 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4491012369/10000000000 : ℝ)^4417 ≤ (35271384268203/100000000000000 : ℝ)^3393 := by
    have hnat : (4491012369 : ℕ)^4417*100000000000000^3393 ≤ 35271384268203^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491012369 10000000000 35271384268203 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296871971/10000000000 : ℝ), (4110225967/10000000000 : ℝ), (4491012369/10000000000 : ℝ)] ![(33299568985577/100000000000000 : ℝ), (7857261681567/25000000000000 : ℝ), (35271384268203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296871971/10000000000 : ℝ)|^4417 ≤ (33299568985577/100000000000000 : ℝ)^3393
        have hw : |(4296871971/10000000000 : ℝ)|=(4296871971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4110225967/10000000000 : ℝ)|^4417 ≤ (7857261681567/25000000000000 : ℝ)^3393
        have hw : |(4110225967/10000000000 : ℝ)|=(4110225967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4491012369/10000000000 : ℝ)|^4417 ≤ (35271384268203/100000000000000 : ℝ)^3393
        have hw : |(4491012369/10000000000 : ℝ)|=(4491012369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s3_4 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-973877501/5000000000 : ℝ)*x 0 + (5241006531/10000000000 : ℝ)*x 1 + (2706927237/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (973877501/5000000000 : ℝ)^4417 ≤ (11888233815323/100000000000000 : ℝ)^3393 := by
    have hnat : (973877501 : ℕ)^4417*100000000000000^3393 ≤ 11888233815323^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      973877501 5000000000 11888233815323 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241006531/10000000000 : ℝ)^4417 ≤ (21562776126711/50000000000000 : ℝ)^3393 := by
    have hnat : (5241006531 : ℕ)^4417*50000000000000^3393 ≤ 21562776126711^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241006531 10000000000 21562776126711 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706927237/5000000000 : ℝ)^4417 ≤ (44986213907193/100000000000000 : ℝ)^3393 := by
    have hnat : (2706927237 : ℕ)^4417*100000000000000^3393 ≤ 44986213907193^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706927237 5000000000 44986213907193 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-973877501/5000000000 : ℝ), (5241006531/10000000000 : ℝ), (2706927237/5000000000 : ℝ)] ![(11888233815323/100000000000000 : ℝ), (21562776126711/50000000000000 : ℝ), (44986213907193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-973877501/5000000000 : ℝ)|^4417 ≤ (11888233815323/100000000000000 : ℝ)^3393
        have hw : |(-973877501/5000000000 : ℝ)|=(973877501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241006531/10000000000 : ℝ)|^4417 ≤ (21562776126711/50000000000000 : ℝ)^3393
        have hw : |(5241006531/10000000000 : ℝ)|=(5241006531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706927237/5000000000 : ℝ)|^4417 ≤ (44986213907193/100000000000000 : ℝ)^3393
        have hw : |(2706927237/5000000000 : ℝ)|=(2706927237/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s3_5 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1060664239/2000000000 : ℝ)*x 0 + (-58219801/312500000 : ℝ)*x 1 + (2706927227/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060664239/2000000000 : ℝ)^4417 ≤ (43794250402239/100000000000000 : ℝ)^3393 := by
    have hnat : (1060664239 : ℕ)^4417*100000000000000^3393 ≤ 43794250402239^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060664239 2000000000 43794250402239 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (58219801/312500000 : ℝ)^4417 ≤ (1121953589443/10000000000000 : ℝ)^3393 := by
    have hnat : (58219801 : ℕ)^4417*10000000000000^3393 ≤ 1121953589443^3393*312500000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      58219801 312500000 1121953589443 10000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706927227/5000000000 : ℝ)^4417 ≤ (44986213690849/100000000000000 : ℝ)^3393 := by
    have hnat : (2706927227 : ℕ)^4417*100000000000000^3393 ≤ 44986213690849^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706927227 5000000000 44986213690849 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060664239/2000000000 : ℝ), (-58219801/312500000 : ℝ), (2706927227/5000000000 : ℝ)] ![(43794250402239/100000000000000 : ℝ), (1121953589443/10000000000000 : ℝ), (44986213690849/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060664239/2000000000 : ℝ)|^4417 ≤ (43794250402239/100000000000000 : ℝ)^3393
        have hw : |(1060664239/2000000000 : ℝ)|=(1060664239/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-58219801/312500000 : ℝ)|^4417 ≤ (1121953589443/10000000000000 : ℝ)^3393
        have hw : |(-58219801/312500000 : ℝ)|=(58219801/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706927227/5000000000 : ℝ)|^4417 ≤ (44986213690849/100000000000000 : ℝ)^3393
        have hw : |(2706927227/5000000000 : ℝ)|=(2706927227/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s3_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651660071/5000000000 : ℝ)*x 0 + (5413855271/10000000000 : ℝ)*x 1 + (-465758487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651660071/5000000000 : ℝ)^4417 ≤ (43794239082379/100000000000000 : ℝ)^3393 := by
    have hnat : (2651660071 : ℕ)^4417*100000000000000^3393 ≤ 43794239082379^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651660071 5000000000 43794239082379 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5413855271/10000000000 : ℝ)^4417 ≤ (44986222528533/100000000000000 : ℝ)^3393 := by
    have hnat : (5413855271 : ℕ)^4417*100000000000000^3393 ≤ 44986222528533^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413855271 10000000000 44986222528533 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (465758487/2500000000 : ℝ)^4417 ≤ (2243907674353/20000000000000 : ℝ)^3393 := by
    have hnat : (465758487 : ℕ)^4417*20000000000000^3393 ≤ 2243907674353^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      465758487 2500000000 2243907674353 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651660071/5000000000 : ℝ), (5413855271/10000000000 : ℝ), (-465758487/2500000000 : ℝ)] ![(43794239082379/100000000000000 : ℝ), (44986222528533/100000000000000 : ℝ), (2243907674353/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651660071/5000000000 : ℝ)|^4417 ≤ (43794239082379/100000000000000 : ℝ)^3393
        have hw : |(2651660071/5000000000 : ℝ)|=(2651660071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5413855271/10000000000 : ℝ)|^4417 ≤ (44986222528533/100000000000000 : ℝ)^3393
        have hw : |(5413855271/10000000000 : ℝ)|=(5413855271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-465758487/2500000000 : ℝ)|^4417 ≤ (2243907674353/20000000000000 : ℝ)^3393
        have hw : |(-465758487/2500000000 : ℝ)|=(465758487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s3_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4296902661/10000000000 : ℝ)*x 0 + (2244753817/5000000000 : ℝ)*x 1 + (2055870107/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4296902661/10000000000 : ℝ)^4417 ≤ (16649939302107/50000000000000 : ℝ)^3393 := by
    have hnat : (4296902661 : ℕ)^4417*50000000000000^3393 ≤ 16649939302107^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4296902661 10000000000 16649939302107 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2244753817/5000000000 : ℝ)^4417 ≤ (35256000601727/100000000000000 : ℝ)^3393 := by
    have hnat : (2244753817 : ℕ)^4417*100000000000000^3393 ≤ 35256000601727^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2244753817 5000000000 35256000601727 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2055870107/5000000000 : ℝ)^4417 ≤ (3144412077491/10000000000000 : ℝ)^3393 := by
    have hnat : (2055870107 : ℕ)^4417*10000000000000^3393 ≤ 3144412077491^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2055870107 5000000000 3144412077491 10000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4296902661/10000000000 : ℝ), (2244753817/5000000000 : ℝ), (2055870107/5000000000 : ℝ)] ![(16649939302107/50000000000000 : ℝ), (35256000601727/100000000000000 : ℝ), (3144412077491/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4296902661/10000000000 : ℝ)|^4417 ≤ (16649939302107/50000000000000 : ℝ)^3393
        have hw : |(4296902661/10000000000 : ℝ)|=(4296902661/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2244753817/5000000000 : ℝ)|^4417 ≤ (35256000601727/100000000000000 : ℝ)^3393
        have hw : |(2244753817/5000000000 : ℝ)|=(2244753817/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2055870107/5000000000 : ℝ)|^4417 ≤ (3144412077491/10000000000000 : ℝ)^3393
        have hw : |(2055870107/5000000000 : ℝ)|=(2055870107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s3_8 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-6977681587/10000000000 : ℝ)*x 0 + (2759011039/10000000000 : ℝ)*x 1 + (2758221909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6977681587/10000000000 : ℝ)^4417 ≤ (62595557606097/100000000000000 : ℝ)^3393 := by
    have hnat : (6977681587 : ℕ)^4417*100000000000000^3393 ≤ 62595557606097^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6977681587 10000000000 62595557606097 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2759011039/10000000000 : ℝ)^4417 ≤ (18705703469403/100000000000000 : ℝ)^3393 := by
    have hnat : (2759011039 : ℕ)^4417*100000000000000^3393 ≤ 18705703469403^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759011039 10000000000 18705703469403 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2758221909/10000000000 : ℝ)^4417 ≤ (18698738905057/100000000000000 : ℝ)^3393 := by
    have hnat : (2758221909 : ℕ)^4417*100000000000000^3393 ≤ 18698738905057^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758221909 10000000000 18698738905057 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-6977681587/10000000000 : ℝ), (2759011039/10000000000 : ℝ), (2758221909/10000000000 : ℝ)] ![(62595557606097/100000000000000 : ℝ), (18705703469403/100000000000000 : ℝ), (18698738905057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-6977681587/10000000000 : ℝ)|^4417 ≤ (62595557606097/100000000000000 : ℝ)^3393
        have hw : |(-6977681587/10000000000 : ℝ)|=(6977681587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2759011039/10000000000 : ℝ)|^4417 ≤ (18705703469403/100000000000000 : ℝ)^3393
        have hw : |(2759011039/10000000000 : ℝ)|=(2759011039/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2758221909/10000000000 : ℝ)|^4417 ≤ (18698738905057/100000000000000 : ℝ)^3393
        have hw : |(2758221909/10000000000 : ℝ)|=(2758221909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s3_9 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4175909769/5000000000 : ℝ)*x 0 + (-74605017/1250000000 : ℝ)*x 1 + (543747667/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4175909769/5000000000 : ℝ)^4417 ≤ (3954984749343/5000000000000 : ℝ)^3393 := by
    have hnat : (4175909769 : ℕ)^4417*5000000000000^3393 ≤ 3954984749343^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4175909769 5000000000 3954984749343 5000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (74605017/1250000000 : ℝ)^4417 ≤ (2549262990783/100000000000000 : ℝ)^3393 := by
    have hnat : (74605017 : ℕ)^4417*100000000000000^3393 ≤ 2549262990783^3393*1250000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74605017 1250000000 2549262990783 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543747667/2000000000 : ℝ)^4417 ≤ (4587760499713/25000000000000 : ℝ)^3393 := by
    have hnat : (543747667 : ℕ)^4417*25000000000000^3393 ≤ 4587760499713^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543747667 2000000000 4587760499713 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4175909769/5000000000 : ℝ), (-74605017/1250000000 : ℝ), (543747667/2000000000 : ℝ)] ![(3954984749343/5000000000000 : ℝ), (2549262990783/100000000000000 : ℝ), (4587760499713/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4175909769/5000000000 : ℝ)|^4417 ≤ (3954984749343/5000000000000 : ℝ)^3393
        have hw : |(4175909769/5000000000 : ℝ)|=(4175909769/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-74605017/1250000000 : ℝ)|^4417 ≤ (2549262990783/100000000000000 : ℝ)^3393
        have hw : |(-74605017/1250000000 : ℝ)|=(74605017/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543747667/2000000000 : ℝ)|^4417 ≤ (4587760499713/25000000000000 : ℝ)^3393
        have hw : |(543747667/2000000000 : ℝ)|=(543747667/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s3_10 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (8354101733/10000000000 : ℝ)*x 0 + (339520869/1250000000 : ℝ)*x 1 + (-595842169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (8354101733/10000000000 : ℝ)^4417 ≤ (9890979242227/12500000000000 : ℝ)^3393 := by
    have hnat : (8354101733 : ℕ)^4417*12500000000000^3393 ≤ 9890979242227^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8354101733 10000000000 9890979242227 12500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339520869/1250000000 : ℝ)^4417 ≤ (9164225338951/50000000000000 : ℝ)^3393 := by
    have hnat : (339520869 : ℕ)^4417*50000000000000^3393 ≤ 9164225338951^3393*1250000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339520869 1250000000 9164225338951 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (595842169/10000000000 : ℝ)^4417 ≤ (2543715370787/100000000000000 : ℝ)^3393 := by
    have hnat : (595842169 : ℕ)^4417*100000000000000^3393 ≤ 2543715370787^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      595842169 10000000000 2543715370787 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(8354101733/10000000000 : ℝ), (339520869/1250000000 : ℝ), (-595842169/10000000000 : ℝ)] ![(9890979242227/12500000000000 : ℝ), (9164225338951/50000000000000 : ℝ), (2543715370787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(8354101733/10000000000 : ℝ)|^4417 ≤ (9890979242227/12500000000000 : ℝ)^3393
        have hw : |(8354101733/10000000000 : ℝ)|=(8354101733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339520869/1250000000 : ℝ)|^4417 ≤ (9164225338951/50000000000000 : ℝ)^3393
        have hw : |(339520869/1250000000 : ℝ)|=(339520869/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-595842169/10000000000 : ℝ)|^4417 ≤ (2543715370787/100000000000000 : ℝ)^3393
        have hw : |(-595842169/10000000000 : ℝ)|=(595842169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s3_11 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1413134679/2000000000 : ℝ)*x 0 + (3064727749/10000000000 : ℝ)*x 1 + (2899883/12500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1413134679/2000000000 : ℝ)^4417 ≤ (31812546609717/50000000000000 : ℝ)^3393 := by
    have hnat : (1413134679 : ℕ)^4417*50000000000000^3393 ≤ 31812546609717^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1413134679 2000000000 31812546609717 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3064727749/10000000000 : ℝ)^4417 ≤ (10723982600929/50000000000000 : ℝ)^3393 := by
    have hnat : (3064727749 : ℕ)^4417*50000000000000^3393 ≤ 10723982600929^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3064727749 10000000000 10723982600929 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2899883/12500000 : ℝ)^4417 ≤ (14926941563119/100000000000000 : ℝ)^3393 := by
    have hnat : (2899883 : ℕ)^4417*100000000000000^3393 ≤ 14926941563119^3393*12500000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2899883 12500000 14926941563119 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1413134679/2000000000 : ℝ), (3064727749/10000000000 : ℝ), (2899883/12500000 : ℝ)] ![(31812546609717/50000000000000 : ℝ), (10723982600929/50000000000000 : ℝ), (14926941563119/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1413134679/2000000000 : ℝ)|^4417 ≤ (31812546609717/50000000000000 : ℝ)^3393
        have hw : |(1413134679/2000000000 : ℝ)|=(1413134679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3064727749/10000000000 : ℝ)|^4417 ≤ (10723982600929/50000000000000 : ℝ)^3393
        have hw : |(3064727749/10000000000 : ℝ)|=(3064727749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2899883/12500000 : ℝ)|^4417 ≤ (14926941563119/100000000000000 : ℝ)^3393
        have hw : |(2899883/12500000 : ℝ)|=(2899883/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1457_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11243/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14933/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (657/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15717/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (657/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (657/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15717/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (657/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (657/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15717/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (657/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (657/6250 : ℝ) ^ (69/16 : ℝ) ≤ (6039737747162127/100000000000000000000 : ℝ) := by
    have hpowers : (657/6250 : ℝ)^69 ≤ (6039737747162127/100000000000000000000 : ℝ)^16 := by
      have hnat : (657 : ℕ)^69*100000000000000000000^16 ≤ 6039737747162127^16*6250^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        657 6250 6039737747162127 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (657/6250 : ℝ)) (X := (6039737747162127/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hpowhi : (15717/100000 : ℝ) ^ (69/16 : ℝ) ≤ (34225052995426601/100000000000000000000 : ℝ) := by
    have hpowers : (15717/100000 : ℝ)^69 ≤ (34225052995426601/100000000000000000000 : ℝ)^16 := by
      have hnat : (15717 : ℕ)^69*100000000000000000000^16 ≤ 34225052995426601^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15717 100000 34225052995426601 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15717/100000 : ℝ)) (X := (34225052995426601/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006039737747162127/50000000000000000000 : ℝ) ≤ (10000280090785877/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50006039737747162127/50000000000000000000 : ℝ)^16 ≤ (10000280090785877/10000000000000000 : ℝ)^69 := by
      have hnat : (50006039737747162127 : ℕ)^16*10000000000000000^69 ≤ 10000280090785877^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006039737747162127 50000000000000000000 10000280090785877 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000280090785877/10000000000000000 : ℝ)) (X := (50006039737747162127/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505033098842823591/12500000000000000000 : ℝ) ≤ (1250116691494687/1250000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (12505033098842823591/12500000000000000000 : ℝ)^16 ≤ (1250116691494687/1250000000000000 : ℝ)^69 := by
      have hnat : (12505033098842823591 : ℕ)^16*1250000000000000^69 ≤ 1250116691494687^69*12500000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505033098842823591 12500000000000000000 1250116691494687 1250000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250116691494687/1250000000000000 : ℝ)) (X := (12505033098842823591/12500000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50034225052995426601/50000000000000000000 : ℝ) ≤ (2000317394625823/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50034225052995426601/50000000000000000000 : ℝ)^16 ≤ (2000317394625823/2000000000000000 : ℝ)^69 := by
      have hnat : (50034225052995426601 : ℕ)^16*2000000000000000^69 ≤ 2000317394625823^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50034225052995426601 50000000000000000000 2000317394625823 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000317394625823/2000000000000000 : ℝ)) (X := (50034225052995426601/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6039737747162127/100000000000000000000 : ℝ) ≤ ((17345906641782790643/17350000000000000000 : ℝ)+2*(217813723873/173500000000000 : ℝ)*(657/6250 : ℝ))^(69/16 : ℝ) := by
    rw [show (17345906641782790643/17350000000000000000 : ℝ)+2*(217813723873/173500000000000 : ℝ)*(657/6250 : ℝ)=(10000280090785877/10000000000000000 : ℝ) by norm_num, show 1+2*(6039737747162127/100000000000000000000 : ℝ)=(50006039737747162127/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(34225052995426601/100000000000000000000 : ℝ)+(6039737747162127/100000000000000000000 : ℝ) ≤ ((17345906641782790643/17350000000000000000 : ℝ)+(217813723873/173500000000000 : ℝ)*((15717/100000 : ℝ)+(657/6250 : ℝ)))^(69/16 : ℝ) := by
    rw [show (17345906641782790643/17350000000000000000 : ℝ)+(217813723873/173500000000000 : ℝ)*((15717/100000 : ℝ)+(657/6250 : ℝ))=(1250116691494687/1250000000000000 : ℝ) by norm_num, show 1+(34225052995426601/100000000000000000000 : ℝ)+(6039737747162127/100000000000000000000 : ℝ)=(12505033098842823591/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(34225052995426601/100000000000000000000 : ℝ) ≤ ((17345906641782790643/17350000000000000000 : ℝ)+2*(217813723873/173500000000000 : ℝ)*(15717/100000 : ℝ))^(69/16 : ℝ) := by
    rw [show (17345906641782790643/17350000000000000000 : ℝ)+2*(217813723873/173500000000000 : ℝ)*(15717/100000 : ℝ)=(2000317394625823/2000000000000000 : ℝ) by norm_num, show 1+2*(34225052995426601/100000000000000000000 : ℝ)=(50034225052995426601/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17345906641782790643/17350000000000000000 : ℝ)*(X 1 0+X 2 0)+(217813723873/173500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (657/6250 : ℝ)) (hi := (15717/100000 : ℝ)) (c := (17345906641782790643/17350000000000000000 : ℝ)) (alpha := (217813723873/173500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17345906641782790643/17350000000000000000 : ℝ)*(X 0 1+X 2 1)+(217813723873/173500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (657/6250 : ℝ)) (hi := (15717/100000 : ℝ)) (c := (17345906641782790643/17350000000000000000 : ℝ)) (alpha := (217813723873/173500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17345906641782790643/17350000000000000000 : ℝ)*(X 0 2+X 1 2)+(217813723873/173500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (657/6250 : ℝ)) (hi := (15717/100000 : ℝ)) (c := (17345906641782790643/17350000000000000000 : ℝ)) (alpha := (217813723873/173500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1947740999/10000000000 : ℝ)*X 0 0+(5414546829/10000000000 : ℝ)*X 0 1+(5240317723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069747237/2000000000 : ℝ)*X 1 0+(-2036570409/10000000000 : ℝ)*X 1 1+(1310079421/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348736559/10000000000 : ℝ)*X 2 0+(5240317513/10000000000 : ℝ)*X 2 1+(-254571267/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4296871971/10000000000 : ℝ)*X 0 0+(4110225967/10000000000 : ℝ)*X 0 1+(4491012369/10000000000 : ℝ)*X 0 2+(4296871971/10000000000 : ℝ)*X 1 0+(4110225967/10000000000 : ℝ)*X 1 1+(4491012369/10000000000 : ℝ)*X 1 2+(4296871971/10000000000 : ℝ)*X 2 0+(4110225967/10000000000 : ℝ)*X 2 1+(4491012369/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-973877501/5000000000 : ℝ)*X 0 0+(5241006531/10000000000 : ℝ)*X 0 1+(2706927237/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1060664239/2000000000 : ℝ)*X 1 0+(-58219801/312500000 : ℝ)*X 1 1+(2706927227/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651660071/5000000000 : ℝ)*X 2 0+(5413855271/10000000000 : ℝ)*X 2 1+(-465758487/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4296902661/10000000000 : ℝ)*X 0 0+(2244753817/5000000000 : ℝ)*X 0 1+(2055870107/5000000000 : ℝ)*X 0 2+(4296902661/10000000000 : ℝ)*X 1 0+(2244753817/5000000000 : ℝ)*X 1 1+(2055870107/5000000000 : ℝ)*X 1 2+(4296902661/10000000000 : ℝ)*X 2 0+(2244753817/5000000000 : ℝ)*X 2 1+(2055870107/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-6977681587/10000000000 : ℝ)*X 0 0+(2759011039/10000000000 : ℝ)*X 0 1+(2758221909/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((4175909769/5000000000 : ℝ)*X 1 0+(-74605017/1250000000 : ℝ)*X 1 1+(543747667/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((8354101733/10000000000 : ℝ)*X 2 0+(339520869/1250000000 : ℝ)*X 2 1+(-595842169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((1413134679/2000000000 : ℝ)*X 0 0+(3064727749/10000000000 : ℝ)*X 0 1+(2899883/12500000 : ℝ)*X 0 2+(1413134679/2000000000 : ℝ)*X 1 0+(3064727749/10000000000 : ℝ)*X 1 1+(2899883/12500000 : ℝ)*X 1 2+(1413134679/2000000000 : ℝ)*X 2 0+(3064727749/10000000000 : ℝ)*X 2 1+(2899883/12500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (973668030539741941047391623/216875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (735024811/100000000000000 : ℝ)*(base19) + (1106744439/100000000000000 : ℝ)*(base23) + (28570989/100000000000000 : ℝ)*(lower2) + (257309339/100000000000000 : ℝ)*(upper5) + (1045720057737287/25000000000000 : ℝ)*(major0) + (1045720057737287/25000000000000 : ℝ)*(major1) + (1045720057737287/25000000000000 : ℝ)*(major2) + (1434894400499673/25000000000000 : ℝ)*(sp0) + (5739595736984099/100000000000000 : ℝ)*(sp1) + (2869799084486513/50000000000000 : ℝ)*(sp2) + (656538388310557/25000000000000 : ℝ)*(sp3) + (21673718773/100000000000000 : ℝ)*(sp4) + (700927139/25000000000000 : ℝ)*(sp5) + (1870821853/25000000000000 : ℝ)*(sp7) + (2626161036529639/100000000000000 : ℝ)*(f.failure) + (1147919855143493/20000000000000 : ℝ)*(f.sum) + (1377679151173/4337500000000000000000000000 : ℝ)*base66 + (843639274485344459/433750000000000000000000000000000 : ℝ)*base68 + (1717666966213405541/433750000000000000000000000000000 : ℝ)*base69 + (874639230835344459/433750000000000000000000000000000 : ℝ)*base72 + (9710730036529/8675000000000000000000000000 : ℝ)*base73 + (5699786131829094459/433750000000000000000000000000000 : ℝ)*base76 + (3062730385098405541/433750000000000000000000000000000 : ℝ)*base77 + (492887426771594459/433750000000000000000000000000000 : ℝ)*base80 + (4451797952187/1084375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2696943/1000000000000000000000 : ℝ)*base89 + (2696943/1000000000000000000000 : ℝ)*base91 + (2696943/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13831295679521015347287/8675000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2063913/6250000000000 : ℝ)*(lower5) + (527035507344081/12500000000000 : ℝ)*(major0) + (527035507344081/12500000000000 : ℝ)*(major1) + (527035507344081/12500000000000 : ℝ)*(major2) + (2559377721/100000000000000 : ℝ)*(sp1) + (3595116621/100000000000000 : ℝ)*(sp2) + (2892717295778453/50000000000000 : ℝ)*(sp4) + (578543224466493/10000000000000 : ℝ)*(sp5) + (5785429227544057/100000000000000 : ℝ)*(sp6) + (661783168914101/25000000000000 : ℝ)*(sp7) + (324664043/100000000000000 : ℝ)*(sp8) + (112178299/100000000000000 : ℝ)*(sp9) + (130847517/6250000000000 : ℝ)*(sp10) + (236240873/50000000000000 : ℝ)*(sp11) + (52942662962763/2000000000000 : ℝ)*(f.failure) + (5785434916220949/100000000000000 : ℝ)*(f.sum) + (599127318471/8675000000000000000000000000 : ℝ)*base66 + (274577786465159083/216875000000000000000000000000000 : ℝ)*base67 + (2056479448528909083/216875000000000000000000000000000 : ℝ)*base69 + (2382279933761409083/216875000000000000000000000000000 : ℝ)*base71 + (364441814771/8675000000000000000000000000 : ℝ)*base74 + (3932652287249840917/216875000000000000000000000000000 : ℝ)*base76 + (671615669466090917/216875000000000000000000000000000 : ℝ)*base78 + (613929854001715917/216875000000000000000000000000000 : ℝ)*base80 + (3308509663851/2168750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (257331/20000000000000000000 : ℝ)*base89 + (257331/20000000000000000000 : ℝ)*base91 + (257331/20000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1457_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14933/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1457_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1457_s4_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-487127747/2500000000 : ℝ)*x 0 + (1351973851/2500000000 : ℝ)*x 1 + (1049292319/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487127747/2500000000 : ℝ)^4417 ≤ (743390057963/6250000000000 : ℝ)^3393 := by
    have hnat : (487127747 : ℕ)^4417*6250000000000^3393 ≤ 743390057963^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487127747 2500000000 743390057963 6250000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1351973851/2500000000 : ℝ)^4417 ≤ (4492176393503/10000000000000 : ℝ)^3393 := by
    have hnat : (1351973851 : ℕ)^4417*10000000000000^3393 ≤ 4492176393503^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351973851 2500000000 4492176393503 10000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049292319/2000000000 : ℝ)^4417 ≤ (2159199756257/5000000000000 : ℝ)^3393 := by
    have hnat : (1049292319 : ℕ)^4417*5000000000000^3393 ≤ 2159199756257^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049292319 2000000000 2159199756257 5000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-487127747/2500000000 : ℝ), (1351973851/2500000000 : ℝ), (1049292319/2000000000 : ℝ)] ![(743390057963/6250000000000 : ℝ), (4492176393503/10000000000000 : ℝ), (2159199756257/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-487127747/2500000000 : ℝ)|^4417 ≤ (743390057963/6250000000000 : ℝ)^3393
        have hw : |(-487127747/2500000000 : ℝ)|=(487127747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1351973851/2500000000 : ℝ)|^4417 ≤ (4492176393503/10000000000000 : ℝ)^3393
        have hw : |(1351973851/2500000000 : ℝ)|=(1351973851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1049292319/2000000000 : ℝ)|^4417 ≤ (2159199756257/5000000000000 : ℝ)^3393
        have hw : |(1049292319/2000000000 : ℝ)|=(1049292319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s4_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336753317/2500000000 : ℝ)*x 0 + (-507675031/2500000000 : ℝ)*x 1 + (5246461697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336753317/2500000000 : ℝ)^4417 ≤ (44264527582449/100000000000000 : ℝ)^3393 := by
    have hnat : (1336753317 : ℕ)^4417*100000000000000^3393 ≤ 44264527582449^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336753317 2500000000 44264527582449 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (507675031/2500000000 : ℝ)^4417 ≤ (1568934523007/12500000000000 : ℝ)^3393 := by
    have hnat : (507675031 : ℕ)^4417*12500000000000^3393 ≤ 1568934523007^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      507675031 2500000000 1568934523007 12500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5246461697/10000000000 : ℝ)^4417 ≤ (43183996218089/100000000000000 : ℝ)^3393 := by
    have hnat : (5246461697 : ℕ)^4417*100000000000000^3393 ≤ 43183996218089^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5246461697 10000000000 43183996218089 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336753317/2500000000 : ℝ), (-507675031/2500000000 : ℝ), (5246461697/10000000000 : ℝ)] ![(44264527582449/100000000000000 : ℝ), (1568934523007/12500000000000 : ℝ), (43183996218089/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336753317/2500000000 : ℝ)|^4417 ≤ (44264527582449/100000000000000 : ℝ)^3393
        have hw : |(1336753317/2500000000 : ℝ)|=(1336753317/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-507675031/2500000000 : ℝ)|^4417 ≤ (1568934523007/12500000000000 : ℝ)^3393
        have hw : |(-507675031/2500000000 : ℝ)|=(507675031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5246461697/10000000000 : ℝ)|^4417 ≤ (43183996218089/100000000000000 : ℝ)^3393
        have hw : |(5246461697/10000000000 : ℝ)|=(5246461697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s4_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336753281/2500000000 : ℝ)*x 0 + (40987983/78125000 : ℝ)*x 1 + (-2030700147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336753281/2500000000 : ℝ)^4417 ≤ (11066131507649/25000000000000 : ℝ)^3393 := by
    have hnat : (1336753281 : ℕ)^4417*25000000000000^3393 ≤ 11066131507649^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336753281 2500000000 11066131507649 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (40987983/78125000 : ℝ)^4417 ≤ (21591998789459/50000000000000 : ℝ)^3393 := by
    have hnat : (40987983 : ℕ)^4417*50000000000000^3393 ≤ 21591998789459^3393*78125000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40987983 78125000 21591998789459 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2030700147/10000000000 : ℝ)^4417 ≤ (78446727307/625000000000 : ℝ)^3393 := by
    have hnat : (2030700147 : ℕ)^4417*625000000000^3393 ≤ 78446727307^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2030700147 10000000000 78446727307 625000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336753281/2500000000 : ℝ), (40987983/78125000 : ℝ), (-2030700147/10000000000 : ℝ)] ![(11066131507649/25000000000000 : ℝ), (21591998789459/50000000000000 : ℝ), (78446727307/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336753281/2500000000 : ℝ)|^4417 ≤ (11066131507649/25000000000000 : ℝ)^3393
        have hw : |(1336753281/2500000000 : ℝ)|=(1336753281/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(40987983/78125000 : ℝ)|^4417 ≤ (21591998789459/50000000000000 : ℝ)^3393
        have hw : |(40987983/78125000 : ℝ)|=(40987983/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2030700147/10000000000 : ℝ)|^4417 ≤ (78446727307/625000000000 : ℝ)^3393
        have hw : |(-2030700147/10000000000 : ℝ)|=(2030700147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s4_3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4297344927/10000000000 : ℝ)*x 0 + (4124152237/10000000000 : ℝ)*x 1 + (1119243323/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297344927/10000000000 : ℝ)^4417 ≤ (4163042564491/12500000000000 : ℝ)^3393 := by
    have hnat : (4297344927 : ℕ)^4417*12500000000000^3393 ≤ 4163042564491^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297344927 10000000000 4163042564491 12500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4124152237/10000000000 : ℝ)^4417 ≤ (7891935820259/25000000000000 : ℝ)^3393 := by
    have hnat : (4124152237 : ℕ)^4417*25000000000000^3393 ≤ 7891935820259^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4124152237 10000000000 7891935820259 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1119243323/2500000000 : ℝ)^4417 ≤ (35127916187751/100000000000000 : ℝ)^3393 := by
    have hnat : (1119243323 : ℕ)^4417*100000000000000^3393 ≤ 35127916187751^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119243323 2500000000 35127916187751 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297344927/10000000000 : ℝ), (4124152237/10000000000 : ℝ), (1119243323/2500000000 : ℝ)] ![(4163042564491/12500000000000 : ℝ), (7891935820259/25000000000000 : ℝ), (35127916187751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297344927/10000000000 : ℝ)|^4417 ≤ (4163042564491/12500000000000 : ℝ)^3393
        have hw : |(4297344927/10000000000 : ℝ)|=(4297344927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4124152237/10000000000 : ℝ)|^4417 ≤ (7891935820259/25000000000000 : ℝ)^3393
        have hw : |(4124152237/10000000000 : ℝ)|=(4124152237/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1119243323/2500000000 : ℝ)|^4417 ≤ (35127916187751/100000000000000 : ℝ)^3393
        have hw : |(1119243323/2500000000 : ℝ)|=(1119243323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s4_4 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-974261301/5000000000 : ℝ)*x 0 + (5247053171/10000000000 : ℝ)*x 1 + (5407300659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (974261301/5000000000 : ℝ)^4417 ≤ (5947166609233/50000000000000 : ℝ)^3393 := by
    have hnat : (974261301 : ℕ)^4417*50000000000000^3393 ≤ 5947166609233^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974261301 5000000000 5947166609233 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247053171/10000000000 : ℝ)^4417 ≤ (43190334081989/100000000000000 : ℝ)^3393 := by
    have hnat : (5247053171 : ℕ)^4417*100000000000000^3393 ≤ 43190334081989^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247053171 10000000000 43190334081989 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407300659/10000000000 : ℝ)^4417 ≤ (22457666340607/50000000000000 : ℝ)^3393 := by
    have hnat : (5407300659 : ℕ)^4417*50000000000000^3393 ≤ 22457666340607^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407300659 10000000000 22457666340607 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-974261301/5000000000 : ℝ), (5247053171/10000000000 : ℝ), (5407300659/10000000000 : ℝ)] ![(5947166609233/50000000000000 : ℝ), (43190334081989/100000000000000 : ℝ), (22457666340607/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-974261301/5000000000 : ℝ)|^4417 ≤ (5947166609233/50000000000000 : ℝ)^3393
        have hw : |(-974261301/5000000000 : ℝ)|=(974261301/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247053171/10000000000 : ℝ)|^4417 ≤ (43190334081989/100000000000000 : ℝ)^3393
        have hw : |(5247053171/10000000000 : ℝ)|=(5247053171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407300659/10000000000 : ℝ)|^4417 ≤ (22457666340607/50000000000000 : ℝ)^3393
        have hw : |(5407300659/10000000000 : ℝ)|=(5407300659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s4_5 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (132623319/250000000 : ℝ)*x 0 + (-233732657/1250000000 : ℝ)*x 1 + (5407300643/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (132623319/250000000 : ℝ)^4417 ≤ (876231513791/2000000000000 : ℝ)^3393 := by
    have hnat : (132623319 : ℕ)^4417*2000000000000^3393 ≤ 876231513791^3393*250000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      132623319 250000000 876231513791 2000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (233732657/1250000000 : ℝ)^4417 ≤ (2254618356687/20000000000000 : ℝ)^3393 := by
    have hnat : (233732657 : ℕ)^4417*20000000000000^3393 ≤ 2254618356687^3393*1250000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233732657 1250000000 2254618356687 20000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407300643/10000000000 : ℝ)^4417 ≤ (44915332508201/100000000000000 : ℝ)^3393 := by
    have hnat : (5407300643 : ℕ)^4417*100000000000000^3393 ≤ 44915332508201^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407300643 10000000000 44915332508201 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(132623319/250000000 : ℝ), (-233732657/1250000000 : ℝ), (5407300643/10000000000 : ℝ)] ![(876231513791/2000000000000 : ℝ), (2254618356687/20000000000000 : ℝ), (44915332508201/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(132623319/250000000 : ℝ)|^4417 ≤ (876231513791/2000000000000 : ℝ)^3393
        have hw : |(132623319/250000000 : ℝ)|=(132623319/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-233732657/1250000000 : ℝ)|^4417 ≤ (2254618356687/20000000000000 : ℝ)^3393
        have hw : |(-233732657/1250000000 : ℝ)|=(233732657/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407300643/10000000000 : ℝ)|^4417 ≤ (44915332508201/100000000000000 : ℝ)^3393
        have hw : |(5407300643/10000000000 : ℝ)|=(5407300643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s4_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (331558303/625000000 : ℝ)*x 0 + (5407300589/10000000000 : ℝ)*x 1 + (-186986121/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (331558303/625000000 : ℝ)^4417 ≤ (21905788317823/50000000000000 : ℝ)^3393 := by
    have hnat : (331558303 : ℕ)^4417*50000000000000^3393 ≤ 21905788317823^3393*625000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      331558303 625000000 21905788317823 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407300589/10000000000 : ℝ)^4417 ≤ (11228832981071/25000000000000 : ℝ)^3393 := by
    have hnat : (5407300589 : ℕ)^4417*25000000000000^3393 ≤ 11228832981071^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407300589 10000000000 11228832981071 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (186986121/1000000000 : ℝ)^4417 ≤ (2818272855603/25000000000000 : ℝ)^3393 := by
    have hnat : (186986121 : ℕ)^4417*25000000000000^3393 ≤ 2818272855603^3393*1000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      186986121 1000000000 2818272855603 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(331558303/625000000 : ℝ), (5407300589/10000000000 : ℝ), (-186986121/1000000000 : ℝ)] ![(21905788317823/50000000000000 : ℝ), (11228832981071/25000000000000 : ℝ), (2818272855603/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(331558303/625000000 : ℝ)|^4417 ≤ (21905788317823/50000000000000 : ℝ)^3393
        have hw : |(331558303/625000000 : ℝ)|=(331558303/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407300589/10000000000 : ℝ)|^4417 ≤ (11228832981071/25000000000000 : ℝ)^3393
        have hw : |(5407300589/10000000000 : ℝ)|=(5407300589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-186986121/1000000000 : ℝ)|^4417 ≤ (2818272855603/25000000000000 : ℝ)^3393
        have hw : |(-186986121/1000000000 : ℝ)|=(186986121/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s4_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2148685119/5000000000 : ℝ)*x 0 + (447568021/1000000000 : ℝ)*x 1 + (4125452007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2148685119/5000000000 : ℝ)^4417 ≤ (16652297938253/50000000000000 : ℝ)^3393 := by
    have hnat : (2148685119 : ℕ)^4417*50000000000000^3393 ≤ 16652297938253^3393*5000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2148685119 5000000000 16652297938253 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447568021/1000000000 : ℝ)^4417 ≤ (8778677187593/25000000000000 : ℝ)^3393 := by
    have hnat : (447568021 : ℕ)^4417*25000000000000^3393 ≤ 8778677187593^3393*1000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447568021 1000000000 8778677187593 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4125452007/10000000000 : ℝ)^4417 ≤ (31580695361929/100000000000000 : ℝ)^3393 := by
    have hnat : (4125452007 : ℕ)^4417*100000000000000^3393 ≤ 31580695361929^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4125452007 10000000000 31580695361929 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2148685119/5000000000 : ℝ), (447568021/1000000000 : ℝ), (4125452007/10000000000 : ℝ)] ![(16652297938253/50000000000000 : ℝ), (8778677187593/25000000000000 : ℝ), (31580695361929/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2148685119/5000000000 : ℝ)|^4417 ≤ (16652297938253/50000000000000 : ℝ)^3393
        have hw : |(2148685119/5000000000 : ℝ)|=(2148685119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(447568021/1000000000 : ℝ)|^4417 ≤ (8778677187593/25000000000000 : ℝ)^3393
        have hw : |(447568021/1000000000 : ℝ)|=(447568021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4125452007/10000000000 : ℝ)|^4417 ≤ (31580695361929/100000000000000 : ℝ)^3393
        have hw : |(4125452007/10000000000 : ℝ)|=(4125452007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1457_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5687/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7397/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14933/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14933/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11243/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14933/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14933/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11243/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14933/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14933/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11243/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11243/100000 : ℝ) ^ (69/16 : ℝ) ≤ (4035520314212213/50000000000000000000 : ℝ) := by
    have hpowers : (11243/100000 : ℝ)^69 ≤ (4035520314212213/50000000000000000000 : ℝ)^16 := by
      have hnat : (11243 : ℕ)^69*50000000000000000000^16 ≤ 4035520314212213^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11243 100000 4035520314212213 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11243/100000 : ℝ)) (X := (4035520314212213/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hpowhi : (14933/100000 : ℝ) ^ (69/16 : ℝ) ≤ (343098825391249/1250000000000000000 : ℝ) := by
    have hpowers : (14933/100000 : ℝ)^69 ≤ (343098825391249/1250000000000000000 : ℝ)^16 := by
      have hnat : (14933 : ℕ)^69*1250000000000000000^16 ≤ 343098825391249^16*100000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14933 100000 343098825391249 1250000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14933/100000 : ℝ)) (X := (343098825391249/1250000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004035520314212213/25000000000000000000 : ℝ) ≤ (5000187142963763/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25004035520314212213/25000000000000000000 : ℝ)^16 ≤ (5000187142963763/5000000000000000 : ℝ)^69 := by
      have hnat : (25004035520314212213 : ℕ)^16*5000000000000000^69 ≤ 5000187142963763^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004035520314212213 25000000000000000000 5000187142963763 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000187142963763/5000000000000000 : ℝ)) (X := (25004035520314212213/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017759473329862173/50000000000000000000 : ℝ) ≤ (10000823515418329/10000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50017759473329862173/50000000000000000000 : ℝ)^16 ≤ (10000823515418329/10000000000000000 : ℝ)^69 := by
      have hnat : (50017759473329862173 : ℕ)^16*10000000000000000^69 ≤ 10000823515418329^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017759473329862173 50000000000000000000 10000823515418329 10000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000823515418329/10000000000000000 : ℝ)) (X := (50017759473329862173/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (625343098825391249/625000000000000000 : ℝ) ≤ (2500318186227283/2500000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (625343098825391249/625000000000000000 : ℝ)^16 ≤ (2500318186227283/2500000000000000 : ℝ)^69 := by
      have hnat : (625343098825391249 : ℕ)^16*2500000000000000^69 ≤ 2500318186227283^69*625000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        625343098825391249 625000000000000000 2500318186227283 2500000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500318186227283/2500000000000000 : ℝ)) (X := (625343098825391249/625000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4035520314212213/50000000000000000000 : ℝ) ≤ ((2049515541152354149/2050000000000000000 : ℝ)+2*(49914387867/41000000000000 : ℝ)*(11243/100000 : ℝ))^(69/16 : ℝ) := by
    rw [show (2049515541152354149/2050000000000000000 : ℝ)+2*(49914387867/41000000000000 : ℝ)*(11243/100000 : ℝ)=(5000187142963763/5000000000000000 : ℝ) by norm_num, show 1+2*(4035520314212213/50000000000000000000 : ℝ)=(25004035520314212213/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(343098825391249/1250000000000000000 : ℝ)+(4035520314212213/50000000000000000000 : ℝ) ≤ ((2049515541152354149/2050000000000000000 : ℝ)+(49914387867/41000000000000 : ℝ)*((14933/100000 : ℝ)+(11243/100000 : ℝ)))^(69/16 : ℝ) := by
    rw [show (2049515541152354149/2050000000000000000 : ℝ)+(49914387867/41000000000000 : ℝ)*((14933/100000 : ℝ)+(11243/100000 : ℝ))=(10000823515418329/10000000000000000 : ℝ) by norm_num, show 1+(343098825391249/1250000000000000000 : ℝ)+(4035520314212213/50000000000000000000 : ℝ)=(50017759473329862173/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(343098825391249/1250000000000000000 : ℝ) ≤ ((2049515541152354149/2050000000000000000 : ℝ)+2*(49914387867/41000000000000 : ℝ)*(14933/100000 : ℝ))^(69/16 : ℝ) := by
    rw [show (2049515541152354149/2050000000000000000 : ℝ)+2*(49914387867/41000000000000 : ℝ)*(14933/100000 : ℝ)=(2500318186227283/2500000000000000 : ℝ) by norm_num, show 1+2*(343098825391249/1250000000000000000 : ℝ)=(625343098825391249/625000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2049515541152354149/2050000000000000000 : ℝ)*(X 1 0+X 2 0)+(49914387867/41000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (14933/100000 : ℝ)) (c := (2049515541152354149/2050000000000000000 : ℝ)) (alpha := (49914387867/41000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2049515541152354149/2050000000000000000 : ℝ)*(X 0 1+X 2 1)+(49914387867/41000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (14933/100000 : ℝ)) (c := (2049515541152354149/2050000000000000000 : ℝ)) (alpha := (49914387867/41000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2049515541152354149/2050000000000000000 : ℝ)*(X 0 2+X 1 2)+(49914387867/41000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (11243/100000 : ℝ)) (hi := (14933/100000 : ℝ)) (c := (2049515541152354149/2050000000000000000 : ℝ)) (alpha := (49914387867/41000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-487127747/2500000000 : ℝ)*X 0 0+(1351973851/2500000000 : ℝ)*X 0 1+(1049292319/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336753317/2500000000 : ℝ)*X 1 0+(-507675031/2500000000 : ℝ)*X 1 1+(5246461697/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336753281/2500000000 : ℝ)*X 2 0+(40987983/78125000 : ℝ)*X 2 1+(-2030700147/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297344927/10000000000 : ℝ)*X 0 0+(4124152237/10000000000 : ℝ)*X 0 1+(1119243323/2500000000 : ℝ)*X 0 2+(4297344927/10000000000 : ℝ)*X 1 0+(4124152237/10000000000 : ℝ)*X 1 1+(1119243323/2500000000 : ℝ)*X 1 2+(4297344927/10000000000 : ℝ)*X 2 0+(4124152237/10000000000 : ℝ)*X 2 1+(1119243323/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-974261301/5000000000 : ℝ)*X 0 0+(5247053171/10000000000 : ℝ)*X 0 1+(5407300659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((132623319/250000000 : ℝ)*X 1 0+(-233732657/1250000000 : ℝ)*X 1 1+(5407300643/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((331558303/625000000 : ℝ)*X 2 0+(5407300589/10000000000 : ℝ)*X 2 1+(-186986121/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2148685119/5000000000 : ℝ)*X 0 0+(447568021/1000000000 : ℝ)*X 0 1+(4125452007/10000000000 : ℝ)*X 0 2+(2148685119/5000000000 : ℝ)*X 1 0+(447568021/1000000000 : ℝ)*X 1 1+(4125452007/10000000000 : ℝ)*X 1 2+(2148685119/5000000000 : ℝ)*X 2 0+(447568021/1000000000 : ℝ)*X 2 1+(4125452007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38614300610546567237886339/5125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (45108853/4000000000000 : ℝ)*(base19) + (386518827/50000000000000 : ℝ)*(base23) + (12556049/12500000000000 : ℝ)*(lower2) + (201735739/100000000000000 : ℝ)*(upper3) + (7877739/100000000000000 : ℝ)*(upper5) + (451443364398563/10000000000000 : ℝ)*(major0) + (451443364398563/10000000000000 : ℝ)*(major1) + (451443364398563/10000000000000 : ℝ)*(major2) + (774315031971221/12500000000000 : ℝ)*(sp0) + (3097271921571611/50000000000000 : ℝ)*(sp1) + (6194544197826893/100000000000000 : ℝ)*(sp2) + (708577110835233/25000000000000 : ℝ)*(sp3) + (24715094779/100000000000000 : ℝ)*(sp4) + (3405653963/25000000000000 : ℝ)*(sp7) + (177145129122299/6250000000000 : ℝ)*(f.failure) + (6194544970864547/100000000000000 : ℝ)*(f.sum) + (359720159469/205000000000000000000000000 : ℝ)*base66 + (37965361876237887/20500000000000000000000000000000 : ℝ)*base67 + (124815084924237887/20500000000000000000000000000000 : ℝ)*base69 + (167569642880737887/20500000000000000000000000000000 : ℝ)*base71 + (1563364391459/205000000000000000000000000 : ℝ)*base74 + (133016142457737887/20500000000000000000000000000000 : ℝ)*base75 + (43434278957262113/20500000000000000000000000000000 : ℝ)*base78 + (379942418680737887/20500000000000000000000000000000 : ℝ)*base79 + (44672660183/25625000000000000000000000 : ℝ)*base82 + (557363/62500000000000000000 : ℝ)*base89 + (557363/62500000000000000000 : ℝ)*base91 + (557363/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (106824943101425674845124227/25625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (531913877/100000000000000 : ℝ)*(base19) + (764502541/100000000000000 : ℝ)*(base23) + (20270407/50000000000000 : ℝ)*(upper3) + (14605033/25000000000000 : ℝ)*(lower4) + (5666039/5000000000000 : ℝ)*(upper5) + (2273907505333741/50000000000000 : ℝ)*(major0) + (2273907505333741/50000000000000 : ℝ)*(major1) + (2273907505333741/50000000000000 : ℝ)*(major2) + (9637799/80000000000 : ℝ)*(sp1) + (7217984121/50000000000000 : ℝ)*(sp2) + (249613992268069/4000000000000 : ℝ)*(sp4) + (6240337227539099/100000000000000 : ℝ)*(sp5) + (3120167303115471/50000000000000 : ℝ)*(sp6) + (1427640037836977/50000000000000 : ℝ)*(sp7) + (1427640037836977/50000000000000 : ℝ)*(f.failure) + (249613992268069/4000000000000 : ℝ)*(f.sum) + (6643848796603/1025000000000000000000000000 : ℝ)*base66 + (590388314805891409/102500000000000000000000000000000 : ℝ)*base67 + (973043379339108591/102500000000000000000000000000000 : ℝ)*base70 + (1800660855336608591/102500000000000000000000000000000 : ℝ)*base72 + (1441629800453/1025000000000000000000000000 : ℝ)*base74 + (791365474119108591/102500000000000000000000000000000 : ℝ)*base76 + (539766595196608591/102500000000000000000000000000000 : ℝ)*base78 + (1117630507971608591/102500000000000000000000000000000 : ℝ)*base80 + (2611644020653/1025000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (8531049/500000000000000000000 : ℝ)*base89 + (8531049/500000000000000000000 : ℝ)*base91 + (8531049/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1457_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14933/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11243/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1457_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1457_s5_0 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-487155323/2500000000 : ℝ)*x 0 + (540691453/1000000000 : ℝ)*x 1 + (5247369627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (487155323/2500000000 : ℝ)^4417 ≤ (11895117468707/100000000000000 : ℝ)^3393 := by
    have hnat : (487155323 : ℕ)^4417*100000000000000^3393 ≤ 11895117468707^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      487155323 2500000000 11895117468707 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (540691453/1000000000 : ℝ)^4417 ≤ (5613894675419/12500000000000 : ℝ)^3393 := by
    have hnat : (540691453 : ℕ)^4417*12500000000000^3393 ≤ 5613894675419^3393*1000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540691453 1000000000 5613894675419 12500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247369627/10000000000 : ℝ)^4417 ≤ (21596862557137/50000000000000 : ℝ)^3393 := by
    have hnat : (5247369627 : ℕ)^4417*50000000000000^3393 ≤ 21596862557137^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247369627 10000000000 21596862557137 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-487155323/2500000000 : ℝ), (540691453/1000000000 : ℝ), (5247369627/10000000000 : ℝ)] ![(11895117468707/100000000000000 : ℝ), (5613894675419/12500000000000 : ℝ), (21596862557137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-487155323/2500000000 : ℝ)|^4417 ≤ (11895117468707/100000000000000 : ℝ)^3393
        have hw : |(-487155323/2500000000 : ℝ)|=(487155323/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(540691453/1000000000 : ℝ)|^4417 ≤ (5613894675419/12500000000000 : ℝ)^3393
        have hw : |(540691453/1000000000 : ℝ)|=(540691453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247369627/10000000000 : ℝ)|^4417 ≤ (21596862557137/50000000000000 : ℝ)^3393
        have hw : |(5247369627/10000000000 : ℝ)|=(5247369627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s5_1 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (213870351/400000000 : ℝ)*x 0 + (-2029831797/10000000000 : ℝ)*x 1 + (5247369627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213870351/400000000 : ℝ)^4417 ≤ (22130892496397/50000000000000 : ℝ)^3393 := by
    have hnat : (213870351 : ℕ)^4417*50000000000000^3393 ≤ 22130892496397^3393*400000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213870351 400000000 22130892496397 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2029831797/10000000000 : ℝ)^4417 ≤ (12544489874423/100000000000000 : ℝ)^3393 := by
    have hnat : (2029831797 : ℕ)^4417*100000000000000^3393 ≤ 12544489874423^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2029831797 10000000000 12544489874423 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247369627/10000000000 : ℝ)^4417 ≤ (21596862557137/50000000000000 : ℝ)^3393 := by
    have hnat : (5247369627 : ℕ)^4417*50000000000000^3393 ≤ 21596862557137^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247369627 10000000000 21596862557137 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213870351/400000000 : ℝ), (-2029831797/10000000000 : ℝ), (5247369627/10000000000 : ℝ)] ![(22130892496397/50000000000000 : ℝ), (12544489874423/100000000000000 : ℝ), (21596862557137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213870351/400000000 : ℝ)|^4417 ≤ (22130892496397/50000000000000 : ℝ)^3393
        have hw : |(213870351/400000000 : ℝ)|=(213870351/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2029831797/10000000000 : ℝ)|^4417 ≤ (12544489874423/100000000000000 : ℝ)^3393
        have hw : |(-2029831797/10000000000 : ℝ)|=(2029831797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247369627/10000000000 : ℝ)|^4417 ≤ (21596862557137/50000000000000 : ℝ)^3393
        have hw : |(5247369627/10000000000 : ℝ)|=(5247369627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s5_2 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346758769/10000000000 : ℝ)*x 0 + (5247369637/10000000000 : ℝ)*x 1 + (-126864487/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346758769/10000000000 : ℝ)^4417 ≤ (22130892464067/50000000000000 : ℝ)^3393 := by
    have hnat : (5346758769 : ℕ)^4417*50000000000000^3393 ≤ 22130892464067^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346758769 10000000000 22130892464067 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247369637/10000000000 : ℝ)^4417 ≤ (43193725221431/100000000000000 : ℝ)^3393 := by
    have hnat : (5247369637 : ℕ)^4417*100000000000000^3393 ≤ 43193725221431^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247369637 10000000000 43193725221431 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126864487/625000000 : ℝ)^4417 ≤ (12544489834197/100000000000000 : ℝ)^3393 := by
    have hnat : (126864487 : ℕ)^4417*100000000000000^3393 ≤ 12544489834197^3393*625000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126864487 625000000 12544489834197 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346758769/10000000000 : ℝ), (5247369637/10000000000 : ℝ), (-126864487/625000000 : ℝ)] ![(22130892464067/50000000000000 : ℝ), (43193725221431/100000000000000 : ℝ), (12544489834197/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346758769/10000000000 : ℝ)|^4417 ≤ (22130892464067/50000000000000 : ℝ)^3393
        have hw : |(5346758769/10000000000 : ℝ)|=(5346758769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247369637/10000000000 : ℝ)|^4417 ≤ (43193725221431/100000000000000 : ℝ)^3393
        have hw : |(5247369637/10000000000 : ℝ)|=(5247369637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-126864487/625000000 : ℝ)|^4417 ≤ (12544489834197/100000000000000 : ℝ)^3393
        have hw : |(-126864487/625000000 : ℝ)|=(126864487/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s5_3 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4297411799/10000000000 : ℝ)*x 0 + (4126208287/10000000000 : ℝ)*x 1 + (894980241/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297411799/10000000000 : ℝ)^4417 ≤ (33305015182971/100000000000000 : ℝ)^3393 := by
    have hnat : (4297411799 : ℕ)^4417*100000000000000^3393 ≤ 33305015182971^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297411799 10000000000 33305015182971 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4126208287/10000000000 : ℝ)^4417 ≤ (3948529023119/12500000000000 : ℝ)^3393 := by
    have hnat : (4126208287 : ℕ)^4417*12500000000000^3393 ≤ 3948529023119^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126208287 10000000000 3948529023119 12500000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (894980241/2000000000 : ℝ)^4417 ≤ (8776688152669/25000000000000 : ℝ)^3393 := by
    have hnat : (894980241 : ℕ)^4417*25000000000000^3393 ≤ 8776688152669^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      894980241 2000000000 8776688152669 25000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297411799/10000000000 : ℝ), (4126208287/10000000000 : ℝ), (894980241/2000000000 : ℝ)] ![(33305015182971/100000000000000 : ℝ), (3948529023119/12500000000000 : ℝ), (8776688152669/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297411799/10000000000 : ℝ)|^4417 ≤ (33305015182971/100000000000000 : ℝ)^3393
        have hw : |(4297411799/10000000000 : ℝ)|=(4297411799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4126208287/10000000000 : ℝ)|^4417 ≤ (3948529023119/12500000000000 : ℝ)^3393
        have hw : |(4126208287/10000000000 : ℝ)|=(4126208287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(894980241/2000000000 : ℝ)|^4417 ≤ (8776688152669/25000000000000 : ℝ)^3393
        have hw : |(894980241/2000000000 : ℝ)|=(894980241/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s5_4 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-243579053/1250000000 : ℝ)*x 0 + (5247947487/10000000000 : ℝ)*x 1 + (5406333669/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (243579053/1250000000 : ℝ)^4417 ≤ (11895205931043/100000000000000 : ℝ)^3393 := by
    have hnat : (243579053 : ℕ)^4417*100000000000000^3393 ≤ 11895205931043^3393*1250000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      243579053 1250000000 11895205931043 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247947487/10000000000 : ℝ)^4417 ≤ (43199917420033/100000000000000 : ℝ)^3393 := by
    have hnat : (5247947487 : ℕ)^4417*100000000000000^3393 ≤ 43199917420033^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247947487 10000000000 43199917420033 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406333669/10000000000 : ℝ)^4417 ≤ (22452438312553/50000000000000 : ℝ)^3393 := by
    have hnat : (5406333669 : ℕ)^4417*50000000000000^3393 ≤ 22452438312553^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406333669 10000000000 22452438312553 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-243579053/1250000000 : ℝ), (5247947487/10000000000 : ℝ), (5406333669/10000000000 : ℝ)] ![(11895205931043/100000000000000 : ℝ), (43199917420033/100000000000000 : ℝ), (22452438312553/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-243579053/1250000000 : ℝ)|^4417 ≤ (11895205931043/100000000000000 : ℝ)^3393
        have hw : |(-243579053/1250000000 : ℝ)|=(243579053/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247947487/10000000000 : ℝ)|^4417 ≤ (43199917420033/100000000000000 : ℝ)^3393
        have hw : |(5247947487/10000000000 : ℝ)|=(5247947487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406333669/10000000000 : ℝ)|^4417 ≤ (22452438312553/50000000000000 : ℝ)^3393
        have hw : |(5406333669/10000000000 : ℝ)|=(5406333669/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s5_5 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (663146311/1250000000 : ℝ)*x 0 + (-1870867761/10000000000 : ℝ)*x 1 + (540633367/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (663146311/1250000000 : ℝ)^4417 ≤ (21907065771071/50000000000000 : ℝ)^3393 := by
    have hnat : (663146311 : ℕ)^4417*50000000000000^3393 ≤ 21907065771071^3393*1250000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      663146311 1250000000 21907065771071 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1870867761/10000000000 : ℝ)^4417 ≤ (5640495903677/50000000000000 : ℝ)^3393 := by
    have hnat : (1870867761 : ℕ)^4417*50000000000000^3393 ≤ 5640495903677^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870867761 10000000000 5640495903677 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540633367/1000000000 : ℝ)^4417 ≤ (44904876635919/100000000000000 : ℝ)^3393 := by
    have hnat : (540633367 : ℕ)^4417*100000000000000^3393 ≤ 44904876635919^3393*1000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540633367 1000000000 44904876635919 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(663146311/1250000000 : ℝ), (-1870867761/10000000000 : ℝ), (540633367/1000000000 : ℝ)] ![(21907065771071/50000000000000 : ℝ), (5640495903677/50000000000000 : ℝ), (44904876635919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(663146311/1250000000 : ℝ)|^4417 ≤ (21907065771071/50000000000000 : ℝ)^3393
        have hw : |(663146311/1250000000 : ℝ)|=(663146311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1870867761/10000000000 : ℝ)|^4417 ≤ (5640495903677/50000000000000 : ℝ)^3393
        have hw : |(-1870867761/10000000000 : ℝ)|=(1870867761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540633367/1000000000 : ℝ)|^4417 ≤ (44904876635919/100000000000000 : ℝ)^3393
        have hw : |(540633367/1000000000 : ℝ)|=(540633367/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s5_6 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061034099/2000000000 : ℝ)*x 0 + (5406333679/10000000000 : ℝ)*x 1 + (-1870867739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061034099/2000000000 : ℝ)^4417 ≤ (43814131617401/100000000000000 : ℝ)^3393 := by
    have hnat : (1061034099 : ℕ)^4417*100000000000000^3393 ≤ 43814131617401^3393*2000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061034099 2000000000 43814131617401 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406333679/10000000000 : ℝ)^4417 ≤ (44904876733233/100000000000000 : ℝ)^3393 := by
    have hnat : (5406333679 : ℕ)^4417*100000000000000^3393 ≤ 44904876733233^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406333679 10000000000 44904876733233 100000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1870867739/10000000000 : ℝ)^4417 ≤ (5640495817331/50000000000000 : ℝ)^3393 := by
    have hnat : (1870867739 : ℕ)^4417*50000000000000^3393 ≤ 5640495817331^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1870867739 10000000000 5640495817331 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061034099/2000000000 : ℝ), (5406333679/10000000000 : ℝ), (-1870867739/10000000000 : ℝ)] ![(43814131617401/100000000000000 : ℝ), (44904876733233/100000000000000 : ℝ), (5640495817331/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061034099/2000000000 : ℝ)|^4417 ≤ (43814131617401/100000000000000 : ℝ)^3393
        have hw : |(1061034099/2000000000 : ℝ)|=(1061034099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406333679/10000000000 : ℝ)|^4417 ≤ (44904876733233/100000000000000 : ℝ)^3393
        have hw : |(5406333679/10000000000 : ℝ)|=(5406333679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1870867739/10000000000 : ℝ)|^4417 ≤ (5640495817331/50000000000000 : ℝ)^3393
        have hw : |(-1870867739/10000000000 : ℝ)|=(1870867739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1457_s5_7 (p : ℝ) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4297436141/10000000000 : ℝ)*x 0 + (447363829/1000000000 : ℝ)*x 1 + (1031869437/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4297436141/10000000000 : ℝ)^4417 ≤ (16652630384267/50000000000000 : ℝ)^3393 := by
    have hnat : (4297436141 : ℕ)^4417*50000000000000^3393 ≤ 16652630384267^3393*10000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4297436141 10000000000 16652630384267 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (447363829/1000000000 : ℝ)^4417 ≤ (17546927542939/50000000000000 : ℝ)^3393 := by
    have hnat : (447363829 : ℕ)^4417*50000000000000^3393 ≤ 17546927542939^3393*1000000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      447363829 1000000000 17546927542939 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1031869437/2500000000 : ℝ)^4417 ≤ (15800442064137/50000000000000 : ℝ)^3393 := by
    have hnat : (1031869437 : ℕ)^4417*50000000000000^3393 ≤ 15800442064137^3393*2500000000^4417 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031869437 2500000000 15800442064137 50000000000000 4417 3393 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4417/1024 : ℝ)) 4417 3393 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4297436141/10000000000 : ℝ), (447363829/1000000000 : ℝ), (1031869437/2500000000 : ℝ)] ![(16652630384267/50000000000000 : ℝ), (17546927542939/50000000000000 : ℝ), (15800442064137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4297436141/10000000000 : ℝ)|^4417 ≤ (16652630384267/50000000000000 : ℝ)^3393
        have hw : |(4297436141/10000000000 : ℝ)|=(4297436141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(447363829/1000000000 : ℝ)|^4417 ≤ (17546927542939/50000000000000 : ℝ)^3393
        have hw : |(447363829/1000000000 : ℝ)|=(447363829/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1031869437/2500000000 : ℝ)|^4417 ≤ (15800442064137/50000000000000 : ℝ)^3393
        have hw : |(1031869437/2500000000 : ℝ)|=(1031869437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1457_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11393/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7387/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7397/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5687/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7397/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5687/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7397/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5687/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7397/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5687/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7397/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5687/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7397/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5687/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5687/50000 : ℝ) ^ (69/16 : ℝ) ≤ (4242245351687399/50000000000000000000 : ℝ) := by
    have hpowers : (5687/50000 : ℝ)^69 ≤ (4242245351687399/50000000000000000000 : ℝ)^16 := by
      have hnat : (5687 : ℕ)^69*50000000000000000000^16 ≤ 4242245351687399^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5687 50000 4242245351687399 50000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5687/50000 : ℝ)) (X := (4242245351687399/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hpowhi : (7397/50000 : ℝ) ^ (69/16 : ℝ) ≤ (26362962504294827/100000000000000000000 : ℝ) := by
    have hpowers : (7397/50000 : ℝ)^69 ≤ (26362962504294827/100000000000000000000 : ℝ)^16 := by
      have hnat : (7397 : ℕ)^69*100000000000000000000^16 ≤ 26362962504294827^16*50000^69 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7397 50000 26362962504294827 100000000000000000000 69 16 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7397/50000 : ℝ)) (X := (26362962504294827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004242245351687399/25000000000000000000 : ℝ) ≤ (5000196728992887/5000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (25004242245351687399/25000000000000000000 : ℝ)^16 ≤ (5000196728992887/5000000000000000 : ℝ)^69 := by
      have hnat : (25004242245351687399 : ℕ)^16*5000000000000000^69 ≤ 5000196728992887^69*25000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004242245351687399 25000000000000000000 5000196728992887 5000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000196728992887/5000000000000000 : ℝ)) (X := (25004242245351687399/25000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner10 : (800278779625661357/800000000000000000 : ℝ) ≤ (2000161589752471/2000000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (800278779625661357/800000000000000000 : ℝ)^16 ≤ (2000161589752471/2000000000000000 : ℝ)^69 := by
      have hnat : (800278779625661357 : ℕ)^16*2000000000000000^69 ≤ 2000161589752471^69*800000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        800278779625661357 800000000000000000 2000161589752471 2000000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000161589752471/2000000000000000 : ℝ)) (X := (800278779625661357/800000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026362962504294827/50000000000000000000 : ℝ) ≤ (1250152804942367/1250000000000000 : ℝ) ^ (69/16 : ℝ) := by
    have hpowers : (50026362962504294827/50000000000000000000 : ℝ)^16 ≤ (1250152804942367/1250000000000000 : ℝ)^69 := by
      have hnat : (50026362962504294827 : ℕ)^16*1250000000000000^69 ≤ 1250152804942367^69*50000000000000000000^16 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026362962504294827 50000000000000000000 1250152804942367 1250000000000000 16 69 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250152804942367/1250000000000000 : ℝ)) (X := (50026362962504294827/50000000000000000000 : ℝ)) (by norm_num) 69 16 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4242245351687399/50000000000000000000 : ℝ) ≤ ((8547979197531420623/8550000000000000000 : ℝ)+2*(414490776581/342000000000000 : ℝ)*(5687/50000 : ℝ))^(69/16 : ℝ) := by
    rw [show (8547979197531420623/8550000000000000000 : ℝ)+2*(414490776581/342000000000000 : ℝ)*(5687/50000 : ℝ)=(5000196728992887/5000000000000000 : ℝ) by norm_num, show 1+2*(4242245351687399/50000000000000000000 : ℝ)=(25004242245351687399/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26362962504294827/100000000000000000000 : ℝ)+(4242245351687399/50000000000000000000 : ℝ) ≤ ((8547979197531420623/8550000000000000000 : ℝ)+(414490776581/342000000000000 : ℝ)*((7397/50000 : ℝ)+(5687/50000 : ℝ)))^(69/16 : ℝ) := by
    rw [show (8547979197531420623/8550000000000000000 : ℝ)+(414490776581/342000000000000 : ℝ)*((7397/50000 : ℝ)+(5687/50000 : ℝ))=(2000161589752471/2000000000000000 : ℝ) by norm_num, show 1+(26362962504294827/100000000000000000000 : ℝ)+(4242245351687399/50000000000000000000 : ℝ)=(800278779625661357/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26362962504294827/100000000000000000000 : ℝ) ≤ ((8547979197531420623/8550000000000000000 : ℝ)+2*(414490776581/342000000000000 : ℝ)*(7397/50000 : ℝ))^(69/16 : ℝ) := by
    rw [show (8547979197531420623/8550000000000000000 : ℝ)+2*(414490776581/342000000000000 : ℝ)*(7397/50000 : ℝ)=(1250152804942367/1250000000000000 : ℝ) by norm_num, show 1+2*(26362962504294827/100000000000000000000 : ℝ)=(50026362962504294827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8547979197531420623/8550000000000000000 : ℝ)*(X 1 0+X 2 0)+(414490776581/342000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (8547979197531420623/8550000000000000000 : ℝ)) (alpha := (414490776581/342000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8547979197531420623/8550000000000000000 : ℝ)*(X 0 1+X 2 1)+(414490776581/342000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (8547979197531420623/8550000000000000000 : ℝ)) (alpha := (414490776581/342000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8547979197531420623/8550000000000000000 : ℝ)*(X 0 2+X 1 2)+(414490776581/342000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (69/16 : ℝ)) (lo := (5687/50000 : ℝ)) (hi := (7397/50000 : ℝ)) (c := (8547979197531420623/8550000000000000000 : ℝ)) (alpha := (414490776581/342000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-487155323/2500000000 : ℝ)*X 0 0+(540691453/1000000000 : ℝ)*X 0 1+(5247369627/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((213870351/400000000 : ℝ)*X 1 0+(-2029831797/10000000000 : ℝ)*X 1 1+(5247369627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346758769/10000000000 : ℝ)*X 2 0+(5247369637/10000000000 : ℝ)*X 2 1+(-126864487/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4297411799/10000000000 : ℝ)*X 0 0+(4126208287/10000000000 : ℝ)*X 0 1+(894980241/2000000000 : ℝ)*X 0 2+(4297411799/10000000000 : ℝ)*X 1 0+(4126208287/10000000000 : ℝ)*X 1 1+(894980241/2000000000 : ℝ)*X 1 2+(4297411799/10000000000 : ℝ)*X 2 0+(4126208287/10000000000 : ℝ)*X 2 1+(894980241/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-243579053/1250000000 : ℝ)*X 0 0+(5247947487/10000000000 : ℝ)*X 0 1+(5406333669/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((663146311/1250000000 : ℝ)*X 1 0+(-1870867761/10000000000 : ℝ)*X 1 1+(540633367/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1061034099/2000000000 : ℝ)*X 2 0+(5406333679/10000000000 : ℝ)*X 2 1+(-1870867739/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4297436141/10000000000 : ℝ)*X 0 0+(447363829/1000000000 : ℝ)*X 0 1+(1031869437/2500000000 : ℝ)*X 0 2+(4297436141/10000000000 : ℝ)*X 1 0+(447363829/1000000000 : ℝ)*X 1 1+(1031869437/2500000000 : ℝ)*X 1 2+(4297436141/10000000000 : ℝ)*X 2 0+(447363829/1000000000 : ℝ)*X 2 1+(1031869437/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1457_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20146989274874453597369/1900000000000000000000000000 : ℝ) := by norm_num
    linear_combination (477167401/25000000000000 : ℝ)*(base19) + (35478927/2000000000000 : ℝ)*(base23) + (68272529/100000000000000 : ℝ)*(lower2) + (64748411/25000000000000 : ℝ)*(upper3) + (171900767/100000000000000 : ℝ)*(upper5) + (4567901109021753/100000000000000 : ℝ)*(major0) + (4567901109021753/100000000000000 : ℝ)*(major1) + (4567901109021753/100000000000000 : ℝ)*(major2) + (626787024980849/10000000000000 : ℝ)*(sp0) + (6267909113030621/100000000000000 : ℝ)*(sp1) + (50143273982031/800000000000 : ℝ)*(sp2) + (1433935451489253/50000000000000 : ℝ)*(sp3) + (5096486467/12500000000000 : ℝ)*(sp4) + (19939908813/100000000000000 : ℝ)*(sp7) + (1433945421443659/50000000000000 : ℝ)*(f.failure) + (250716440868009/4000000000000 : ℝ)*(f.sum) + (11016214974269/5700000000000000000000000000 : ℝ)*base66 + (506354461680712373/285000000000000000000000000000000 : ℝ)*base67 + (2182828401359287627/285000000000000000000000000000000 : ℝ)*base70 + (2178885920549287627/285000000000000000000000000000000 : ℝ)*base72 + (1466287575331/5700000000000000000000000000 : ℝ)*base73 + (4542044209035712373/285000000000000000000000000000000 : ℝ)*base75 + (763727141549287627/285000000000000000000000000000000 : ℝ)*base78 + (2316541582425712373/285000000000000000000000000000000 : ℝ)*base79 + (4407340521031/5700000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (4130317/500000000000000000000 : ℝ)*base90 + (4130317/500000000000000000000 : ℝ)*base92 + (4130317/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (224113844741369157778523997/23750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (196357009/12500000000000 : ℝ)*(base19) + (1730140271/100000000000000 : ℝ)*(base23) + (196783493/100000000000000 : ℝ)*(upper3) + (2571611/4000000000000 : ℝ)*(lower4) + (190324293/100000000000000 : ℝ)*(upper5) + (4601256769635683/100000000000000 : ℝ)*(major0) + (4601256769635683/100000000000000 : ℝ)*(major1) + (4601256769635683/100000000000000 : ℝ)*(major2) + (8263609947/25000000000000 : ℝ)*(sp1) + (36851946797/100000000000000 : ℝ)*(sp2) + (1578420127826297/25000000000000 : ℝ)*(sp4) + (6313645886009327/100000000000000 : ℝ)*(sp5) + (157841048230453/2500000000000 : ℝ)*(sp6) + (144441635671021/5000000000000 : ℝ)*(sp7) + (144441635671021/5000000000000 : ℝ)*(f.failure) + (1578420127826297/25000000000000 : ℝ)*(f.sum) + (31972919646977/17100000000000000000000000000 : ℝ)*base66 + (26577152741534491/855000000000000000000000000000000 : ℝ)*base68 + (6327744734778465509/855000000000000000000000000000000 : ℝ)*base69 + (11228355447558465509/855000000000000000000000000000000 : ℝ)*base71 + (74838385840877/17100000000000000000000000000 : ℝ)*base74 + (2457258577908465509/855000000000000000000000000000000 : ℝ)*base75 + (4958383078023465509/855000000000000000000000000000000 : ℝ)*base77 + (11297381758143465509/855000000000000000000000000000000 : ℝ)*base79 + (37551751662223/17100000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (490523/50000000000000000000 : ℝ)*base90 + (490523/50000000000000000000 : ℝ)*base92 + (490523/50000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1457_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7397/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5687/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1457_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1457_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1457_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1457_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1457_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (69/16 : ℝ) ≤ p) (hpb : p ≤ (4417/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (15927737/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15717/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (657/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11393/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7387/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1457_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
