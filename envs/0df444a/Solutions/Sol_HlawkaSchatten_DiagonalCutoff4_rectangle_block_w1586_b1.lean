-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1586_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:31:31.103092+00:00
-- url     : https://prove2.me/submissions/e1c01aab-4b7a-4282-9ad5-a540398fb0c0

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
theorem support_rectangle_w1586_s3_0 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1763780989/10000000000 : ℝ)*x 0 + (1085030847/2000000000 : ℝ)*x 1 + (5219322623/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1763780989/10000000000 : ℝ)^4669 ≤ (10832937971141/100000000000000 : ℝ)^3645 := by
    have hnat : (1763780989 : ℕ)^4669*100000000000000^3645 ≤ 10832937971141^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763780989 10000000000 10832937971141 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085030847/2000000000 : ℝ)^4669 ≤ (2855484161469/6250000000000 : ℝ)^3645 := by
    have hnat : (1085030847 : ℕ)^4669*6250000000000^3645 ≤ 2855484161469^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085030847 2000000000 2855484161469 6250000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219322623/10000000000 : ℝ)^4669 ≤ (8695863085867/20000000000000 : ℝ)^3645 := by
    have hnat : (5219322623 : ℕ)^4669*20000000000000^3645 ≤ 8695863085867^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219322623 10000000000 8695863085867 20000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1763780989/10000000000 : ℝ), (1085030847/2000000000 : ℝ), (5219322623/10000000000 : ℝ)] ![(10832937971141/100000000000000 : ℝ), (2855484161469/6250000000000 : ℝ), (8695863085867/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1763780989/10000000000 : ℝ)|^4669 ≤ (10832937971141/100000000000000 : ℝ)^3645
        have hw : |(-1763780989/10000000000 : ℝ)|=(1763780989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085030847/2000000000 : ℝ)|^4669 ≤ (2855484161469/6250000000000 : ℝ)^3645
        have hw : |(1085030847/2000000000 : ℝ)|=(1085030847/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219322623/10000000000 : ℝ)|^4669 ≤ (8695863085867/20000000000000 : ℝ)^3645
        have hw : |(5219322623/10000000000 : ℝ)|=(5219322623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s3_1 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336891373/2500000000 : ℝ)*x 0 + (-93454129/500000000 : ℝ)*x 1 + (1043864417/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336891373/2500000000 : ℝ)^4669 ≤ (44852458361803/100000000000000 : ℝ)^3645 := by
    have hnat : (1336891373 : ℕ)^4669*100000000000000^3645 ≤ 44852458361803^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336891373 2500000000 44852458361803 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93454129/500000000 : ℝ)^4669 ≤ (2333646387191/20000000000000 : ℝ)^3645 := by
    have hnat : (93454129 : ℕ)^4669*20000000000000^3645 ≤ 2333646387191^3645*500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93454129 500000000 2333646387191 20000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043864417/2000000000 : ℝ)^4669 ≤ (5434913711059/12500000000000 : ℝ)^3645 := by
    have hnat : (1043864417 : ℕ)^4669*12500000000000^3645 ≤ 5434913711059^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043864417 2000000000 5434913711059 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336891373/2500000000 : ℝ), (-93454129/500000000 : ℝ), (1043864417/2000000000 : ℝ)] ![(44852458361803/100000000000000 : ℝ), (2333646387191/20000000000000 : ℝ), (5434913711059/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336891373/2500000000 : ℝ)|^4669 ≤ (44852458361803/100000000000000 : ℝ)^3645
        have hw : |(1336891373/2500000000 : ℝ)|=(1336891373/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93454129/500000000 : ℝ)|^4669 ≤ (2333646387191/20000000000000 : ℝ)^3645
        have hw : |(-93454129/500000000 : ℝ)|=(93454129/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1043864417/2000000000 : ℝ)|^4669 ≤ (5434913711059/12500000000000 : ℝ)^3645
        have hw : |(1043864417/2000000000 : ℝ)|=(1043864417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s3_2 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5347565639/10000000000 : ℝ)*x 0 + (5219322123/10000000000 : ℝ)*x 1 + (-467270583/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347565639/10000000000 : ℝ)^4669 ≤ (2803278746321/6250000000000 : ℝ)^3645 := by
    have hnat : (5347565639 : ℕ)^4669*6250000000000^3645 ≤ 2803278746321^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347565639 10000000000 2803278746321 6250000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219322123/10000000000 : ℝ)^4669 ≤ (1086982752349/2500000000000 : ℝ)^3645 := by
    have hnat : (5219322123 : ℕ)^4669*2500000000000^3645 ≤ 1086982752349^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219322123 10000000000 1086982752349 2500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (467270583/2500000000 : ℝ)^4669 ≤ (1166822995281/10000000000000 : ℝ)^3645 := by
    have hnat : (467270583 : ℕ)^4669*10000000000000^3645 ≤ 1166822995281^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      467270583 2500000000 1166822995281 10000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347565639/10000000000 : ℝ), (5219322123/10000000000 : ℝ), (-467270583/2500000000 : ℝ)] ![(2803278746321/6250000000000 : ℝ), (1086982752349/2500000000000 : ℝ), (1166822995281/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347565639/10000000000 : ℝ)|^4669 ≤ (2803278746321/6250000000000 : ℝ)^3645
        have hw : |(5347565639/10000000000 : ℝ)|=(5347565639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219322123/10000000000 : ℝ)|^4669 ≤ (1086982752349/2500000000000 : ℝ)^3645
        have hw : |(5219322123/10000000000 : ℝ)|=(5219322123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-467270583/2500000000 : ℝ)|^4669 ≤ (1166822995281/10000000000000 : ℝ)^3645
        have hw : |(-467270583/2500000000 : ℝ)|=(467270583/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s3_3 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66193483/156250000 : ℝ)*x 0 + (499560617/1250000000 : ℝ)*x 1 + (2243832177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66193483/156250000 : ℝ)^4669 ≤ (33281733029573/100000000000000 : ℝ)^3645 := by
    have hnat : (66193483 : ℕ)^4669*100000000000000^3645 ≤ 33281733029573^3645*156250000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66193483 156250000 33281733029573 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (499560617/1250000000 : ℝ)^4669 ≤ (3860882060813/12500000000000 : ℝ)^3645 := by
    have hnat : (499560617 : ℕ)^4669*12500000000000^3645 ≤ 3860882060813^3645*1250000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499560617 1250000000 3860882060813 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243832177/5000000000 : ℝ)^4669 ≤ (4478901309261/12500000000000 : ℝ)^3645 := by
    have hnat : (2243832177 : ℕ)^4669*12500000000000^3645 ≤ 4478901309261^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243832177 5000000000 4478901309261 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66193483/156250000 : ℝ), (499560617/1250000000 : ℝ), (2243832177/5000000000 : ℝ)] ![(33281733029573/100000000000000 : ℝ), (3860882060813/12500000000000 : ℝ), (4478901309261/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66193483/156250000 : ℝ)|^4669 ≤ (33281733029573/100000000000000 : ℝ)^3645
        have hw : |(66193483/156250000 : ℝ)|=(66193483/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(499560617/1250000000 : ℝ)|^4669 ≤ (3860882060813/12500000000000 : ℝ)^3645
        have hw : |(499560617/1250000000 : ℝ)|=(499560617/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243832177/5000000000 : ℝ)|^4669 ≤ (4478901309261/12500000000000 : ℝ)^3645
        have hw : |(2243832177/5000000000 : ℝ)|=(2243832177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s3_4 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1763808271/10000000000 : ℝ)*x 0 + (2610205907/5000000000 : ℝ)*x 1 + (1084811371/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1763808271/10000000000 : ℝ)^4669 ≤ (2708288152097/25000000000000 : ℝ)^3645 := by
    have hnat : (1763808271 : ℕ)^4669*25000000000000^3645 ≤ 2708288152097^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763808271 10000000000 2708288152097 25000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2610205907/5000000000 : ℝ)^4669 ≤ (43490938253559/100000000000000 : ℝ)^3645 := by
    have hnat : (2610205907 : ℕ)^4669*100000000000000^3645 ≤ 43490938253559^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610205907 5000000000 43490938253559 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084811371/2000000000 : ℝ)^4669 ≤ (45675909118981/100000000000000 : ℝ)^3645 := by
    have hnat : (1084811371 : ℕ)^4669*100000000000000^3645 ≤ 45675909118981^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084811371 2000000000 45675909118981 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1763808271/10000000000 : ℝ), (2610205907/5000000000 : ℝ), (1084811371/2000000000 : ℝ)] ![(2708288152097/25000000000000 : ℝ), (43490938253559/100000000000000 : ℝ), (45675909118981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1763808271/10000000000 : ℝ)|^4669 ≤ (2708288152097/25000000000000 : ℝ)^3645
        have hw : |(-1763808271/10000000000 : ℝ)|=(1763808271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2610205907/5000000000 : ℝ)|^4669 ≤ (43490938253559/100000000000000 : ℝ)^3645
        have hw : |(2610205907/5000000000 : ℝ)|=(2610205907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084811371/2000000000 : ℝ)|^4669 ≤ (45675909118981/100000000000000 : ℝ)^3645
        have hw : |(1084811371/2000000000 : ℝ)|=(1084811371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s3_5 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646503943/5000000000 : ℝ)*x 0 + (-1664347947/10000000000 : ℝ)*x 1 + (678007103/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646503943/5000000000 : ℝ)^4669 ≤ (1106678659037/2500000000000 : ℝ)^3645 := by
    have hnat : (2646503943 : ℕ)^4669*2500000000000^3645 ≤ 1106678659037^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646503943 5000000000 1106678659037 2500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1664347947/10000000000 : ℝ)^4669 ≤ (5028472418727/50000000000000 : ℝ)^3645 := by
    have hnat : (1664347947 : ℕ)^4669*50000000000000^3645 ≤ 5028472418727^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1664347947 10000000000 5028472418727 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (678007103/1250000000 : ℝ)^4669 ≤ (2854744299037/6250000000000 : ℝ)^3645 := by
    have hnat : (678007103 : ℕ)^4669*6250000000000^3645 ≤ 2854744299037^3645*1250000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678007103 1250000000 2854744299037 6250000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646503943/5000000000 : ℝ), (-1664347947/10000000000 : ℝ), (678007103/1250000000 : ℝ)] ![(1106678659037/2500000000000 : ℝ), (5028472418727/50000000000000 : ℝ), (2854744299037/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646503943/5000000000 : ℝ)|^4669 ≤ (1106678659037/2500000000000 : ℝ)^3645
        have hw : |(2646503943/5000000000 : ℝ)|=(2646503943/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1664347947/10000000000 : ℝ)|^4669 ≤ (5028472418727/50000000000000 : ℝ)^3645
        have hw : |(-1664347947/10000000000 : ℝ)|=(1664347947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(678007103/1250000000 : ℝ)|^4669 ≤ (2854744299037/6250000000000 : ℝ)^3645
        have hw : |(678007103/1250000000 : ℝ)|=(678007103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s3_6 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529300823/1000000000 : ℝ)*x 0 + (678007103/1250000000 : ℝ)*x 1 + (-104021717/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529300823/1000000000 : ℝ)^4669 ≤ (44267150046703/100000000000000 : ℝ)^3645 := by
    have hnat : (529300823 : ℕ)^4669*100000000000000^3645 ≤ 44267150046703^3645*1000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529300823 1000000000 44267150046703 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678007103/1250000000 : ℝ)^4669 ≤ (2854744299037/6250000000000 : ℝ)^3645 := by
    have hnat : (678007103 : ℕ)^4669*6250000000000^3645 ≤ 2854744299037^3645*1250000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678007103 1250000000 2854744299037 6250000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (104021717/625000000 : ℝ)^4669 ≤ (2514235290223/25000000000000 : ℝ)^3645 := by
    have hnat : (104021717 : ℕ)^4669*25000000000000^3645 ≤ 2514235290223^3645*625000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104021717 625000000 2514235290223 25000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529300823/1000000000 : ℝ), (678007103/1250000000 : ℝ), (-104021717/625000000 : ℝ)] ![(44267150046703/100000000000000 : ℝ), (2854744299037/6250000000000 : ℝ), (2514235290223/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529300823/1000000000 : ℝ)|^4669 ≤ (44267150046703/100000000000000 : ℝ)^3645
        have hw : |(529300823/1000000000 : ℝ)|=(529300823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678007103/1250000000 : ℝ)|^4669 ≤ (2854744299037/6250000000000 : ℝ)^3645
        have hw : |(678007103/1250000000 : ℝ)|=(678007103/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-104021717/625000000 : ℝ)|^4669 ≤ (2514235290223/25000000000000 : ℝ)^3645
        have hw : |(-104021717/625000000 : ℝ)|=(104021717/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s3_7 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4236447553/10000000000 : ℝ)*x 0 + (2242532263/5000000000 : ℝ)*x 1 + (3999104653/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4236447553/10000000000 : ℝ)^4669 ≤ (832059588193/2500000000000 : ℝ)^3645 := by
    have hnat : (4236447553 : ℕ)^4669*2500000000000^3645 ≤ 832059588193^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236447553 10000000000 832059588193 2500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2242532263/5000000000 : ℝ)^4669 ≤ (7160924604363/20000000000000 : ℝ)^3645 := by
    have hnat : (2242532263 : ℕ)^4669*20000000000000^3645 ≤ 7160924604363^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2242532263 5000000000 7160924604363 20000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3999104653/10000000000 : ℝ)^4669 ≤ (15456496722343/50000000000000 : ℝ)^3645 := by
    have hnat : (3999104653 : ℕ)^4669*50000000000000^3645 ≤ 15456496722343^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3999104653 10000000000 15456496722343 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4236447553/10000000000 : ℝ), (2242532263/5000000000 : ℝ), (3999104653/10000000000 : ℝ)] ![(832059588193/2500000000000 : ℝ), (7160924604363/20000000000000 : ℝ), (15456496722343/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4236447553/10000000000 : ℝ)|^4669 ≤ (832059588193/2500000000000 : ℝ)^3645
        have hw : |(4236447553/10000000000 : ℝ)|=(4236447553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2242532263/5000000000 : ℝ)|^4669 ≤ (7160924604363/20000000000000 : ℝ)^3645
        have hw : |(2242532263/5000000000 : ℝ)|=(2242532263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3999104653/10000000000 : ℝ)|^4669 ≤ (15456496722343/50000000000000 : ℝ)^3645
        have hw : |(3999104653/10000000000 : ℝ)|=(3999104653/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1586_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5453/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2229/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1939/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5453/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15771/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5453/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5453/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15771/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5453/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5453/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15771/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5453/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5453/50000 : ℝ) ^ (4667/1024 : ℝ) ≤ (822389786464287/20000000000000000000 : ℝ) := by
    have hpowers : (5453/50000 : ℝ)^4667 ≤ (822389786464287/20000000000000000000 : ℝ)^1024 := by
      have hnat : (5453 : ℕ)^4667*20000000000000000000^1024 ≤ 822389786464287^1024*50000^4667 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5453 50000 822389786464287 20000000000000000000 4667 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5453/50000 : ℝ)) (X := (822389786464287/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15771/100000 : ℝ) ^ (4667/1024 : ℝ) ≤ (22087646740057151/100000000000000000000 : ℝ) := by
    have hpowers : (15771/100000 : ℝ)^4667 ≤ (22087646740057151/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15771 : ℕ)^4667*100000000000000000000^1024 ≤ 22087646740057151^1024*100000^4667 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15771 100000 22087646740057151 100000000000000000000 4667 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15771/100000 : ℝ)) (X := (22087646740057151/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000822389786464287/10000000000000000000 : ℝ) ≤ (2000036087427153/2000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (10000822389786464287/10000000000000000000 : ℝ)^1024 ≤ (2000036087427153/2000000000000000 : ℝ)^4667 := by
      have hnat : (10000822389786464287 : ℕ)^1024*2000000000000000^4667 ≤ 2000036087427153^4667*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000822389786464287 10000000000000000000 2000036087427153 2000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000036087427153/2000000000000000 : ℝ)) (X := (10000822389786464287/10000000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50013099797836189293/50000000000000000000 : ℝ) ≤ (10000574794151479/10000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (50013099797836189293/50000000000000000000 : ℝ)^1024 ≤ (10000574794151479/10000000000000000 : ℝ)^4667 := by
      have hnat : (50013099797836189293 : ℕ)^1024*10000000000000000^4667 ≤ 10000574794151479^4667*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013099797836189293 50000000000000000000 10000574794151479 10000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000574794151479/10000000000000000 : ℝ)) (X := (50013099797836189293/50000000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50022087646740057151/50000000000000000000 : ℝ) ≤ (10000969151167193/10000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (50022087646740057151/50000000000000000000 : ℝ)^1024 ≤ (10000969151167193/10000000000000000 : ℝ)^4667 := by
      have hnat : (50022087646740057151 : ℕ)^1024*10000000000000000^4667 ≤ 10000969151167193^4667*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50022087646740057151 50000000000000000000 10000969151167193 10000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000969151167193/10000000000000000 : ℝ)) (X := (50022087646740057151/50000000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(822389786464287/20000000000000000000 : ℝ) ≤ ((6948896587348391851/6950000000000000000 : ℝ)+2*(197178507857/243250000000000 : ℝ)*(5453/50000 : ℝ))^(4667/1024 : ℝ) := by
    rw [show (6948896587348391851/6950000000000000000 : ℝ)+2*(197178507857/243250000000000 : ℝ)*(5453/50000 : ℝ)=(2000036087427153/2000000000000000 : ℝ) by norm_num, show 1+2*(822389786464287/20000000000000000000 : ℝ)=(10000822389786464287/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(22087646740057151/100000000000000000000 : ℝ)+(822389786464287/20000000000000000000 : ℝ) ≤ ((6948896587348391851/6950000000000000000 : ℝ)+(197178507857/243250000000000 : ℝ)*((15771/100000 : ℝ)+(5453/50000 : ℝ)))^(4667/1024 : ℝ) := by
    rw [show (6948896587348391851/6950000000000000000 : ℝ)+(197178507857/243250000000000 : ℝ)*((15771/100000 : ℝ)+(5453/50000 : ℝ))=(10000574794151479/10000000000000000 : ℝ) by norm_num, show 1+(22087646740057151/100000000000000000000 : ℝ)+(822389786464287/20000000000000000000 : ℝ)=(50013099797836189293/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(22087646740057151/100000000000000000000 : ℝ) ≤ ((6948896587348391851/6950000000000000000 : ℝ)+2*(197178507857/243250000000000 : ℝ)*(15771/100000 : ℝ))^(4667/1024 : ℝ) := by
    rw [show (6948896587348391851/6950000000000000000 : ℝ)+2*(197178507857/243250000000000 : ℝ)*(15771/100000 : ℝ)=(10000969151167193/10000000000000000 : ℝ) by norm_num, show 1+2*(22087646740057151/100000000000000000000 : ℝ)=(50022087646740057151/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6948896587348391851/6950000000000000000 : ℝ)*(X 1 0+X 2 0)+(197178507857/243250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (5453/50000 : ℝ)) (hi := (15771/100000 : ℝ)) (c := (6948896587348391851/6950000000000000000 : ℝ)) (alpha := (197178507857/243250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6948896587348391851/6950000000000000000 : ℝ)*(X 0 1+X 2 1)+(197178507857/243250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (5453/50000 : ℝ)) (hi := (15771/100000 : ℝ)) (c := (6948896587348391851/6950000000000000000 : ℝ)) (alpha := (197178507857/243250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6948896587348391851/6950000000000000000 : ℝ)*(X 0 2+X 1 2)+(197178507857/243250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (5453/50000 : ℝ)) (hi := (15771/100000 : ℝ)) (c := (6948896587348391851/6950000000000000000 : ℝ)) (alpha := (197178507857/243250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1763780989/10000000000 : ℝ)*X 0 0+(1085030847/2000000000 : ℝ)*X 0 1+(5219322623/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336891373/2500000000 : ℝ)*X 1 0+(-93454129/500000000 : ℝ)*X 1 1+(1043864417/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5347565639/10000000000 : ℝ)*X 2 0+(5219322123/10000000000 : ℝ)*X 2 1+(-467270583/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((66193483/156250000 : ℝ)*X 0 0+(499560617/1250000000 : ℝ)*X 0 1+(2243832177/5000000000 : ℝ)*X 0 2+(66193483/156250000 : ℝ)*X 1 0+(499560617/1250000000 : ℝ)*X 1 1+(2243832177/5000000000 : ℝ)*X 1 2+(66193483/156250000 : ℝ)*X 2 0+(499560617/1250000000 : ℝ)*X 2 1+(2243832177/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1763808271/10000000000 : ℝ)*X 0 0+(2610205907/5000000000 : ℝ)*X 0 1+(1084811371/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646503943/5000000000 : ℝ)*X 1 0+(-1664347947/10000000000 : ℝ)*X 1 1+(678007103/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529300823/1000000000 : ℝ)*X 2 0+(678007103/1250000000 : ℝ)*X 2 1+(-104021717/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4236447553/10000000000 : ℝ)*X 0 0+(2242532263/5000000000 : ℝ)*X 0 1+(3999104653/10000000000 : ℝ)*X 0 2+(4236447553/10000000000 : ℝ)*X 1 0+(2242532263/5000000000 : ℝ)*X 1 1+(3999104653/10000000000 : ℝ)*X 1 2+(4236447553/10000000000 : ℝ)*X 2 0+(2242532263/5000000000 : ℝ)*X 2 1+(3999104653/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9600313384321082066369340843/1216250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1579835453/100000000000000 : ℝ)*(base19) + (823291147/50000000000000 : ℝ)*(base23) + (35724703/100000000000000 : ℝ)*(lower2) + (50989293/50000000000000 : ℝ)*(upper3) + (324266067/100000000000000 : ℝ)*(upper5) + (1723575472156289/50000000000000 : ℝ)*(major0) + (1723575472156289/50000000000000 : ℝ)*(major1) + (1723575472156289/50000000000000 : ℝ)*(major2) + (1214587702743429/25000000000000 : ℝ)*(sp0) + (242918418674713/5000000000000 : ℝ)*(sp1) + (4858368306747419/100000000000000 : ℝ)*(sp2) + (2035924671557243/100000000000000 : ℝ)*(sp3) + (19142355997/100000000000000 : ℝ)*(sp4) + (3500312897/50000000000000 : ℝ)*(sp7) + (508982918045759/25000000000000 : ℝ)*(f.failure) + (4858369953329713/100000000000000 : ℝ)*(f.sum) + (129570838588083/24325000000000000000000000000 : ℝ)*base66 + (13835195754361606573/2432500000000000000000000000000000 : ℝ)*base67 + (30345762510909106573/2432500000000000000000000000000000 : ℝ)*base69 + (42745266797151606573/2432500000000000000000000000000000 : ℝ)*base71 + (5581614628263/1520312500000000000000000000 : ℝ)*base74 + (3872024346206606573/2432500000000000000000000000000000 : ℝ)*base75 + (24598184782569106573/2432500000000000000000000000000000 : ℝ)*base77 + (38655903450394106573/2432500000000000000000000000000000 : ℝ)*base79 + (7523995583499/3040625000000000000000000000 : ℝ)*base81 + (703433/50000000000000000000 : ℝ)*base90 + (703433/50000000000000000000 : ℝ)*base92 + (703433/50000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1219126035974425962714540579/304062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (628562161/100000000000000 : ℝ)*(base19) + (7584393/625000000000 : ℝ)*(base23) + (4118357/5000000000000 : ℝ)*(upper2) + (11826089/100000000000000 : ℝ)*(upper3) + (46754187/25000000000000 : ℝ)*(upper5) + (871036643059551/25000000000000 : ℝ)*(major0) + (871036643059551/25000000000000 : ℝ)*(major1) + (871036643059551/25000000000000 : ℝ)*(major2) + (2545516219/20000000000000 : ℝ)*(sp1) + (5854362307/25000000000000 : ℝ)*(sp2) + (4910511245091293/100000000000000 : ℝ)*(sp4) + (2455248944474019/50000000000000 : ℝ)*(sp5) + (982097322827837/20000000000000 : ℝ)*(sp6) + (2057781765736483/100000000000000 : ℝ)*(sp7) + (2057781765736483/100000000000000 : ℝ)*(f.failure) + (4910511245091293/100000000000000 : ℝ)*(f.sum) + (13616330795943/3040625000000000000000000000 : ℝ)*base66 + (11941623383024232307/1216250000000000000000000000000000 : ℝ)*base67 + (13684897186221732307/1216250000000000000000000000000000 : ℝ)*base69 + (6975869297485482307/1216250000000000000000000000000000 : ℝ)*base71 + (21308352089061/6081250000000000000000000000 : ℝ)*base74 + (8139002888151732307/1216250000000000000000000000000000 : ℝ)*base75 + (2290213830617017693/1216250000000000000000000000000000 : ℝ)*base78 + (4973746614916732307/1216250000000000000000000000000000 : ℝ)*base79 + (76328668303819/24325000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1042821/200000000000000000000 : ℝ)*base90 + (1042821/200000000000000000000 : ℝ)*base92 + (1042821/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1586_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5453/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2229/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1939/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1586_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1586_s4_0 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1763968061/10000000000 : ℝ)*x 0 + (5423894277/10000000000 : ℝ)*x 1 + (652557293/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1763968061/10000000000 : ℝ)^4669 ≤ (10834409752167/100000000000000 : ℝ)^3645 := by
    have hnat : (1763968061 : ℕ)^4669*100000000000000^3645 ≤ 10834409752167^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763968061 10000000000 10834409752167 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423894277/10000000000 : ℝ)^4669 ≤ (45674155443393/100000000000000 : ℝ)^3645 := by
    have hnat : (5423894277 : ℕ)^4669*100000000000000^3645 ≤ 45674155443393^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423894277 10000000000 45674155443393 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (652557293/1250000000 : ℝ)^4669 ≤ (43491434793229/100000000000000 : ℝ)^3645 := by
    have hnat : (652557293 : ℕ)^4669*100000000000000^3645 ≤ 43491434793229^3645*1250000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652557293 1250000000 43491434793229 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1763968061/10000000000 : ℝ), (5423894277/10000000000 : ℝ), (652557293/1250000000 : ℝ)] ![(10834409752167/100000000000000 : ℝ), (45674155443393/100000000000000 : ℝ), (43491434793229/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1763968061/10000000000 : ℝ)|^4669 ≤ (10834409752167/100000000000000 : ℝ)^3645
        have hw : |(-1763968061/10000000000 : ℝ)|=(1763968061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423894277/10000000000 : ℝ)|^4669 ≤ (45674155443393/100000000000000 : ℝ)^3645
        have hw : |(5423894277/10000000000 : ℝ)|=(5423894277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(652557293/1250000000 : ℝ)|^4669 ≤ (43491434793229/100000000000000 : ℝ)^3645
        have hw : |(652557293/1250000000 : ℝ)|=(652557293/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s4_1 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673615209/5000000000 : ℝ)*x 0 + (-1868016267/10000000000 : ℝ)*x 1 + (1044091687/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673615209/5000000000 : ℝ)^4669 ≤ (5606107304667/12500000000000 : ℝ)^3645 := by
    have hnat : (2673615209 : ℕ)^4669*12500000000000^3645 ≤ 5606107304667^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673615209 5000000000 5606107304667 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1868016267/10000000000 : ℝ)^4669 ≤ (466388231571/4000000000000 : ℝ)^3645 := by
    have hnat : (1868016267 : ℕ)^4669*4000000000000^3645 ≤ 466388231571^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1868016267 10000000000 466388231571 4000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1044091687/2000000000 : ℝ)^4669 ≤ (21745717882163/50000000000000 : ℝ)^3645 := by
    have hnat : (1044091687 : ℕ)^4669*50000000000000^3645 ≤ 21745717882163^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044091687 2000000000 21745717882163 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673615209/5000000000 : ℝ), (-1868016267/10000000000 : ℝ), (1044091687/2000000000 : ℝ)] ![(5606107304667/12500000000000 : ℝ), (466388231571/4000000000000 : ℝ), (21745717882163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673615209/5000000000 : ℝ)|^4669 ≤ (5606107304667/12500000000000 : ℝ)^3645
        have hw : |(2673615209/5000000000 : ℝ)|=(2673615209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1868016267/10000000000 : ℝ)|^4669 ≤ (466388231571/4000000000000 : ℝ)^3645
        have hw : |(-1868016267/10000000000 : ℝ)|=(1868016267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1044091687/2000000000 : ℝ)|^4669 ≤ (21745717882163/50000000000000 : ℝ)^3645
        have hw : |(1044091687/2000000000 : ℝ)|=(1044091687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s4_2 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336807709/2500000000 : ℝ)*x 0 + (163139313/312500000 : ℝ)*x 1 + (-233502033/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336807709/2500000000 : ℝ)^4669 ≤ (44848862928151/100000000000000 : ℝ)^3645 := by
    have hnat : (1336807709 : ℕ)^4669*100000000000000^3645 ≤ 44848862928151^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336807709 2500000000 44848862928151 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (163139313/312500000 : ℝ)^4669 ≤ (43491431293009/100000000000000 : ℝ)^3645 := by
    have hnat : (163139313 : ℕ)^4669*100000000000000^3645 ≤ 43491431293009^3645*312500000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      163139313 312500000 43491431293009 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (233502033/1250000000 : ℝ)^4669 ≤ (1165970576529/10000000000000 : ℝ)^3645 := by
    have hnat : (233502033 : ℕ)^4669*10000000000000^3645 ≤ 1165970576529^3645*1250000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233502033 1250000000 1165970576529 10000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336807709/2500000000 : ℝ), (163139313/312500000 : ℝ), (-233502033/1250000000 : ℝ)] ![(44848862928151/100000000000000 : ℝ), (43491431293009/100000000000000 : ℝ), (1165970576529/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336807709/2500000000 : ℝ)|^4669 ≤ (44848862928151/100000000000000 : ℝ)^3645
        have hw : |(1336807709/2500000000 : ℝ)|=(1336807709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(163139313/312500000 : ℝ)|^4669 ≤ (43491431293009/100000000000000 : ℝ)^3645
        have hw : |(163139313/312500000 : ℝ)|=(163139313/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-233502033/1250000000 : ℝ)|^4669 ≤ (1165970576529/10000000000000 : ℝ)^3645
        have hw : |(-233502033/1250000000 : ℝ)|=(233502033/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s4_3 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118250797/5000000000 : ℝ)*x 0 + (3999331297/10000000000 : ℝ)*x 1 + (112119797/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118250797/5000000000 : ℝ)^4669 ≤ (33282927357621/100000000000000 : ℝ)^3645 := by
    have hnat : (2118250797 : ℕ)^4669*100000000000000^3645 ≤ 33282927357621^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118250797 5000000000 33282927357621 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3999331297/10000000000 : ℝ)^4669 ≤ (6183047519387/20000000000000 : ℝ)^3645 := by
    have hnat : (3999331297 : ℕ)^4669*20000000000000^3645 ≤ 6183047519387^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3999331297 10000000000 6183047519387 20000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (112119797/250000000 : ℝ)^4669 ≤ (17900917512821/50000000000000 : ℝ)^3645 := by
    have hnat : (112119797 : ℕ)^4669*50000000000000^3645 ≤ 17900917512821^3645*250000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112119797 250000000 17900917512821 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118250797/5000000000 : ℝ), (3999331297/10000000000 : ℝ), (112119797/250000000 : ℝ)] ![(33282927357621/100000000000000 : ℝ), (6183047519387/20000000000000 : ℝ), (17900917512821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118250797/5000000000 : ℝ)|^4669 ≤ (33282927357621/100000000000000 : ℝ)^3645
        have hw : |(2118250797/5000000000 : ℝ)|=(2118250797/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3999331297/10000000000 : ℝ)|^4669 ≤ (6183047519387/20000000000000 : ℝ)^3645
        have hw : |(3999331297/10000000000 : ℝ)|=(3999331297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(112119797/250000000 : ℝ)|^4669 ≤ (17900917512821/50000000000000 : ℝ)^3645
        have hw : |(112119797/250000000 : ℝ)|=(112119797/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s4_4 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-352798827/2000000000 : ℝ)*x 0 + (5221522897/10000000000 : ℝ)*x 1 + (5422822017/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (352798827/2000000000 : ℝ)^4669 ≤ (10834614891739/100000000000000 : ℝ)^3645 := by
    have hnat : (352798827 : ℕ)^4669*100000000000000^3645 ≤ 10834614891739^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352798827 2000000000 10834614891739 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221522897/10000000000 : ℝ)^4669 ≤ (43502795390621/100000000000000 : ℝ)^3645 := by
    have hnat : (5221522897 : ℕ)^4669*100000000000000^3645 ≤ 43502795390621^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221522897 10000000000 43502795390621 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422822017/10000000000 : ℝ)^4669 ≤ (5707823712023/12500000000000 : ℝ)^3645 := by
    have hnat : (5422822017 : ℕ)^4669*12500000000000^3645 ≤ 5707823712023^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422822017 10000000000 5707823712023 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-352798827/2000000000 : ℝ), (5221522897/10000000000 : ℝ), (5422822017/10000000000 : ℝ)] ![(10834614891739/100000000000000 : ℝ), (43502795390621/100000000000000 : ℝ), (5707823712023/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-352798827/2000000000 : ℝ)|^4669 ≤ (10834614891739/100000000000000 : ℝ)^3645
        have hw : |(-352798827/2000000000 : ℝ)|=(352798827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221522897/10000000000 : ℝ)|^4669 ≤ (43502795390621/100000000000000 : ℝ)^3645
        have hw : |(5221522897/10000000000 : ℝ)|=(5221522897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422822017/10000000000 : ℝ)|^4669 ≤ (5707823712023/12500000000000 : ℝ)^3645
        have hw : |(5422822017/10000000000 : ℝ)|=(5422822017/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s4_5 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646654307/5000000000 : ℝ)*x 0 + (-1665652337/10000000000 : ℝ)*x 1 + (542282203/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646654307/5000000000 : ℝ)^4669 ≤ (345862250339/781250000000 : ℝ)^3645 := by
    have hnat : (2646654307 : ℕ)^4669*781250000000^3645 ≤ 345862250339^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646654307 5000000000 345862250339 781250000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1665652337/10000000000 : ℝ)^4669 ≤ (251676052439/2500000000000 : ℝ)^3645 := by
    have hnat : (1665652337 : ℕ)^4669*2500000000000^3645 ≤ 251676052439^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665652337 10000000000 251676052439 2500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542282203/1000000000 : ℝ)^4669 ≤ (22831294918201/50000000000000 : ℝ)^3645 := by
    have hnat : (542282203 : ℕ)^4669*50000000000000^3645 ≤ 22831294918201^3645*1000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542282203 1000000000 22831294918201 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646654307/5000000000 : ℝ), (-1665652337/10000000000 : ℝ), (542282203/1000000000 : ℝ)] ![(345862250339/781250000000 : ℝ), (251676052439/2500000000000 : ℝ), (22831294918201/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646654307/5000000000 : ℝ)|^4669 ≤ (345862250339/781250000000 : ℝ)^3645
        have hw : |(2646654307/5000000000 : ℝ)|=(2646654307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1665652337/10000000000 : ℝ)|^4669 ≤ (251676052439/2500000000000 : ℝ)^3645
        have hw : |(-1665652337/10000000000 : ℝ)|=(1665652337/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542282203/1000000000 : ℝ)|^4669 ≤ (22831294918201/50000000000000 : ℝ)^3645
        have hw : |(542282203/1000000000 : ℝ)|=(542282203/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s4_6 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293308629/10000000000 : ℝ)*x 0 + (338926377/625000000 : ℝ)*x 1 + (-832826157/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293308629/10000000000 : ℝ)^4669 ≤ (44270368204087/100000000000000 : ℝ)^3645 := by
    have hnat : (5293308629 : ℕ)^4669*100000000000000^3645 ≤ 44270368204087^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293308629 10000000000 44270368204087 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338926377/625000000 : ℝ)^4669 ≤ (22831294928987/50000000000000 : ℝ)^3645 := by
    have hnat : (338926377 : ℕ)^4669*50000000000000^3645 ≤ 22831294928987^3645*625000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338926377 625000000 22831294928987 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (832826157/5000000000 : ℝ)^4669 ≤ (5033520959749/50000000000000 : ℝ)^3645 := by
    have hnat : (832826157 : ℕ)^4669*50000000000000^3645 ≤ 5033520959749^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832826157 5000000000 5033520959749 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293308629/10000000000 : ℝ), (338926377/625000000 : ℝ), (-832826157/5000000000 : ℝ)] ![(44270368204087/100000000000000 : ℝ), (22831294928987/50000000000000 : ℝ), (5033520959749/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293308629/10000000000 : ℝ)|^4669 ≤ (44270368204087/100000000000000 : ℝ)^3645
        have hw : |(5293308629/10000000000 : ℝ)|=(5293308629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338926377/625000000 : ℝ)|^4669 ≤ (22831294928987/50000000000000 : ℝ)^3645
        have hw : |(338926377/625000000 : ℝ)|=(338926377/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-832826157/5000000000 : ℝ)|^4669 ≤ (5033520959749/50000000000000 : ℝ)^3645
        have hw : |(-832826157/5000000000 : ℝ)|=(832826157/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s4_7 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4236564063/10000000000 : ℝ)*x 0 + (1792901/4000000 : ℝ)*x 1 + (400188981/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4236564063/10000000000 : ℝ)^4669 ≤ (4160444500413/12500000000000 : ℝ)^3645 := by
    have hnat : (4236564063 : ℕ)^4669*12500000000000^3645 ≤ 4160444500413^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236564063 10000000000 4160444500413 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1792901/4000000 : ℝ)^4669 ≤ (4471983796891/12500000000000 : ℝ)^3645 := by
    have hnat : (1792901 : ℕ)^4669*12500000000000^3645 ≤ 4471983796891^3645*4000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792901 4000000 4471983796891 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (400188981/1000000000 : ℝ)^4669 ≤ (3867571700669/12500000000000 : ℝ)^3645 := by
    have hnat : (400188981 : ℕ)^4669*12500000000000^3645 ≤ 3867571700669^3645*1000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      400188981 1000000000 3867571700669 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4236564063/10000000000 : ℝ), (1792901/4000000 : ℝ), (400188981/1000000000 : ℝ)] ![(4160444500413/12500000000000 : ℝ), (4471983796891/12500000000000 : ℝ), (3867571700669/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4236564063/10000000000 : ℝ)|^4669 ≤ (4160444500413/12500000000000 : ℝ)^3645
        have hw : |(4236564063/10000000000 : ℝ)|=(4236564063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1792901/4000000 : ℝ)|^4669 ≤ (4471983796891/12500000000000 : ℝ)^3645
        have hw : |(1792901/4000000 : ℝ)|=(1792901/4000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(400188981/1000000000 : ℝ)|^4669 ≤ (3867571700669/12500000000000 : ℝ)^3645
        have hw : |(400188981/1000000000 : ℝ)|=(400188981/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1586_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1939/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2229/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (11169/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7743/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1939/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2229/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1939/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2229/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1939/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2229/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1939/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2229/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1939/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2229/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1939/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2229/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2229/20000 : ℝ) ^ (4667/1024 : ℝ) ≤ (2269476896247543/50000000000000000000 : ℝ) := by
    have hpowers : (2229/20000 : ℝ)^4667 ≤ (2269476896247543/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2229 : ℕ)^4667*50000000000000000000^1024 ≤ 2269476896247543^1024*20000^4667 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2229 20000 2269476896247543 50000000000000000000 4667 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2229/20000 : ℝ)) (X := (2269476896247543/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1939/12500 : ℝ) ^ (4667/1024 : ℝ) ≤ (5120515034779089/25000000000000000000 : ℝ) := by
    have hpowers : (1939/12500 : ℝ)^4667 ≤ (5120515034779089/25000000000000000000 : ℝ)^1024 := by
      have hnat : (1939 : ℕ)^4667*25000000000000000000^1024 ≤ 5120515034779089^1024*12500^4667 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1939 12500 5120515034779089 25000000000000000000 4667 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1939/12500 : ℝ)) (X := (5120515034779089/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002269476896247543/25000000000000000000 : ℝ) ≤ (500009958697269/500000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (25002269476896247543/25000000000000000000 : ℝ)^1024 ≤ (500009958697269/500000000000000 : ℝ)^4667 := by
      have hnat : (25002269476896247543 : ℕ)^1024*500000000000000^4667 ≤ 500009958697269^4667*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002269476896247543 25000000000000000000 500009958697269 500000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500009958697269/500000000000000 : ℝ)) (X := (25002269476896247543/25000000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012510506965805721/50000000000000000000 : ℝ) ≤ (10000548939716259/10000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (50012510506965805721/50000000000000000000 : ℝ)^1024 ≤ (10000548939716259/10000000000000000 : ℝ)^4667 := by
      have hnat : (50012510506965805721 : ℕ)^1024*10000000000000000^4667 ≤ 10000548939716259^4667*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012510506965805721 50000000000000000000 10000548939716259 10000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000548939716259/10000000000000000 : ℝ)) (X := (50012510506965805721/50000000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12505120515034779089/12500000000000000000 : ℝ) ≤ (5000449352743569/5000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (12505120515034779089/12500000000000000000 : ℝ)^1024 ≤ (5000449352743569/5000000000000000 : ℝ)^4667 := by
      have hnat : (12505120515034779089 : ℕ)^1024*5000000000000000^4667 ≤ 5000449352743569^4667*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505120515034779089 12500000000000000000 5000449352743569 5000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000449352743569/5000000000000000 : ℝ)) (X := (12505120515034779089/12500000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2269476896247543/50000000000000000000 : ℝ) ≤ ((873261470271731631/873400000000000000 : ℝ)+2*(349765770879/436700000000000 : ℝ)*(2229/20000 : ℝ))^(4667/1024 : ℝ) := by
    rw [show (873261470271731631/873400000000000000 : ℝ)+2*(349765770879/436700000000000 : ℝ)*(2229/20000 : ℝ)=(500009958697269/500000000000000 : ℝ) by norm_num, show 1+2*(2269476896247543/50000000000000000000 : ℝ)=(25002269476896247543/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5120515034779089/25000000000000000000 : ℝ)+(2269476896247543/50000000000000000000 : ℝ) ≤ ((873261470271731631/873400000000000000 : ℝ)+(349765770879/436700000000000 : ℝ)*((1939/12500 : ℝ)+(2229/20000 : ℝ)))^(4667/1024 : ℝ) := by
    rw [show (873261470271731631/873400000000000000 : ℝ)+(349765770879/436700000000000 : ℝ)*((1939/12500 : ℝ)+(2229/20000 : ℝ))=(10000548939716259/10000000000000000 : ℝ) by norm_num, show 1+(5120515034779089/25000000000000000000 : ℝ)+(2269476896247543/50000000000000000000 : ℝ)=(50012510506965805721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5120515034779089/25000000000000000000 : ℝ) ≤ ((873261470271731631/873400000000000000 : ℝ)+2*(349765770879/436700000000000 : ℝ)*(1939/12500 : ℝ))^(4667/1024 : ℝ) := by
    rw [show (873261470271731631/873400000000000000 : ℝ)+2*(349765770879/436700000000000 : ℝ)*(1939/12500 : ℝ)=(5000449352743569/5000000000000000 : ℝ) by norm_num, show 1+2*(5120515034779089/25000000000000000000 : ℝ)=(12505120515034779089/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (873261470271731631/873400000000000000 : ℝ)*(X 1 0+X 2 0)+(349765770879/436700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (2229/20000 : ℝ)) (hi := (1939/12500 : ℝ)) (c := (873261470271731631/873400000000000000 : ℝ)) (alpha := (349765770879/436700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (873261470271731631/873400000000000000 : ℝ)*(X 0 1+X 2 1)+(349765770879/436700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (2229/20000 : ℝ)) (hi := (1939/12500 : ℝ)) (c := (873261470271731631/873400000000000000 : ℝ)) (alpha := (349765770879/436700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (873261470271731631/873400000000000000 : ℝ)*(X 0 2+X 1 2)+(349765770879/436700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (2229/20000 : ℝ)) (hi := (1939/12500 : ℝ)) (c := (873261470271731631/873400000000000000 : ℝ)) (alpha := (349765770879/436700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1763968061/10000000000 : ℝ)*X 0 0+(5423894277/10000000000 : ℝ)*X 0 1+(652557293/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673615209/5000000000 : ℝ)*X 1 0+(-1868016267/10000000000 : ℝ)*X 1 1+(1044091687/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336807709/2500000000 : ℝ)*X 2 0+(163139313/312500000 : ℝ)*X 2 1+(-233502033/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2118250797/5000000000 : ℝ)*X 0 0+(3999331297/10000000000 : ℝ)*X 0 1+(112119797/250000000 : ℝ)*X 0 2+(2118250797/5000000000 : ℝ)*X 1 0+(3999331297/10000000000 : ℝ)*X 1 1+(112119797/250000000 : ℝ)*X 1 2+(2118250797/5000000000 : ℝ)*X 2 0+(3999331297/10000000000 : ℝ)*X 2 1+(112119797/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-352798827/2000000000 : ℝ)*X 0 0+(5221522897/10000000000 : ℝ)*X 0 1+(5422822017/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646654307/5000000000 : ℝ)*X 1 0+(-1665652337/10000000000 : ℝ)*X 1 1+(542282203/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293308629/10000000000 : ℝ)*X 2 0+(338926377/625000000 : ℝ)*X 2 1+(-832826157/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4236564063/10000000000 : ℝ)*X 0 0+(1792901/4000000 : ℝ)*X 0 1+(400188981/1000000000 : ℝ)*X 0 2+(4236564063/10000000000 : ℝ)*X 1 0+(1792901/4000000 : ℝ)*X 1 1+(400188981/1000000000 : ℝ)*X 1 2+(4236564063/10000000000 : ℝ)*X 2 0+(1792901/4000000 : ℝ)*X 2 1+(400188981/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (262248572402292399529373739/21835000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1914763649/100000000000000 : ℝ)*(base19) + (569709007/25000000000000 : ℝ)*(base23) + (2158917/20000000000000 : ℝ)*(lower2) + (6361273/2000000000000 : ℝ)*(upper3) + (363907939/100000000000000 : ℝ)*(upper5) + (1743882850608423/50000000000000 : ℝ)*(major0) + (1743882850608423/50000000000000 : ℝ)*(major1) + (1743882850608423/50000000000000 : ℝ)*(major2) + (4915580015198069/100000000000000 : ℝ)*(sp0) + (4915609817474013/100000000000000 : ℝ)*(sp1) + (4915609453401633/100000000000000 : ℝ)*(sp2) + (205990907536303/10000000000000 : ℝ)*(sp3) + (31717039593/100000000000000 : ℝ)*(sp4) + (2038896811/20000000000000 : ℝ)*(sp7) + (411983853969417/20000000000000 : ℝ)*(f.failure) + (2457805866118831/50000000000000 : ℝ)*(f.sum) + (114394184029099/21835000000000000000000000000 : ℝ)*base65 + (53350721067718087/43670000000000000000000000000000 : ℝ)*base68 + (634532187783128087/43670000000000000000000000000000 : ℝ)*base70 + (117701229286968087/43670000000000000000000000000000 : ℝ)*base72 + (90979554579569/21835000000000000000000000000 : ℝ)*base73 + (42991156018588087/43670000000000000000000000000000 : ℝ)*base76 + (20635384695851913/43670000000000000000000000000000 : ℝ)*base77 + (641581863067301913/43670000000000000000000000000000 : ℝ)*base79 + (8266546039381/1364687500000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (10479/40000000000000000000 : ℝ)*base90 + (10479/40000000000000000000 : ℝ)*base92 + (10479/40000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (186026614883033917724182623/21835000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1321571321/100000000000000 : ℝ)*(base19) + (1432736119/100000000000000 : ℝ)*(base23) + (174196487/100000000000000 : ℝ)*(upper3) + (20669733/50000000000000 : ℝ)*(lower4) + (88144919/50000000000000 : ℝ)*(upper5) + (1762372857116611/50000000000000 : ℝ)*(major0) + (1762372857116611/50000000000000 : ℝ)*(major1) + (1762372857116611/50000000000000 : ℝ)*(major2) + (1350194307/6250000000000 : ℝ)*(sp1) + (5866773891/25000000000000 : ℝ)*(sp2) + (4967731003443669/100000000000000 : ℝ)*(sp4) + (4967708078763437/100000000000000 : ℝ)*(sp5) + (4967706103611987/100000000000000 : ℝ)*(sp6) + (520440035258587/25000000000000 : ℝ)*(sp7) + (520440035258587/25000000000000 : ℝ)*(f.failure) + (4967731003443669/100000000000000 : ℝ)*(f.sum) + (38693002054623/21835000000000000000000000000 : ℝ)*base65 + (192067346015050541/43670000000000000000000000000000 : ℝ)*base67 + (137090700622149459/43670000000000000000000000000000 : ℝ)*base70 + (145563257284499459/43670000000000000000000000000000 : ℝ)*base72 + (13704119325593/21835000000000000000000000000 : ℝ)*base73 + (206866033990660541/43670000000000000000000000000000 : ℝ)*base75 + (184032849964809459/43670000000000000000000000000000 : ℝ)*base78 + (404969221304999459/43670000000000000000000000000000 : ℝ)*base80 + (14103418438493/5458750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (519731/50000000000000000000 : ℝ)*base89 + (519731/50000000000000000000 : ℝ)*base91 + (519731/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1586_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1939/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2229/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1586_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1586_s5_0 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1763985593/10000000000 : ℝ)*x 0 + (1355943743/2500000000 : ℝ)*x 1 + (5220566011/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1763985593/10000000000 : ℝ)^4669 ≤ (10834547686681/100000000000000 : ℝ)^3645 := by
    have hnat : (1763985593 : ℕ)^4669*100000000000000^3645 ≤ 10834547686681^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1763985593 10000000000 10834547686681 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1355943743/2500000000 : ℝ)^4669 ≤ (178409642769/390625000000 : ℝ)^3645 := by
    have hnat : (1355943743 : ℕ)^4669*390625000000^3645 ≤ 178409642769^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355943743 2500000000 178409642769 390625000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5220566011/10000000000 : ℝ)^4669 ≤ (8698516750859/20000000000000 : ℝ)^3645 := by
    have hnat : (5220566011 : ℕ)^4669*20000000000000^3645 ≤ 8698516750859^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220566011 10000000000 8698516750859 20000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1763985593/10000000000 : ℝ), (1355943743/2500000000 : ℝ), (5220566011/10000000000 : ℝ)] ![(10834547686681/100000000000000 : ℝ), (178409642769/390625000000 : ℝ), (8698516750859/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1763985593/10000000000 : ℝ)|^4669 ≤ (10834547686681/100000000000000 : ℝ)^3645
        have hw : |(-1763985593/10000000000 : ℝ)|=(1763985593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1355943743/2500000000 : ℝ)|^4669 ≤ (178409642769/390625000000 : ℝ)^3645
        have hw : |(1355943743/2500000000 : ℝ)|=(1355943743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5220566011/10000000000 : ℝ)|^4669 ≤ (8698516750859/20000000000000 : ℝ)^3645
        have hw : |(5220566011/10000000000 : ℝ)|=(5220566011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s5_1 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069439781/2000000000 : ℝ)*x 0 + (-466978757/2500000000 : ℝ)*x 1 + (522056601/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069439781/2000000000 : ℝ)^4669 ≤ (1793940795013/4000000000000 : ℝ)^3645 := by
    have hnat : (1069439781 : ℕ)^4669*4000000000000^3645 ≤ 1793940795013^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069439781 2000000000 1793940795013 4000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (466978757/2500000000 : ℝ)^4669 ≤ (2914724090507/25000000000000 : ℝ)^3645 := by
    have hnat : (466978757 : ℕ)^4669*25000000000000^3645 ≤ 2914724090507^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466978757 2500000000 2914724090507 25000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (522056601/1000000000 : ℝ)^4669 ≤ (43492583743623/100000000000000 : ℝ)^3645 := by
    have hnat : (522056601 : ℕ)^4669*100000000000000^3645 ≤ 43492583743623^3645*1000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522056601 1000000000 43492583743623 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069439781/2000000000 : ℝ), (-466978757/2500000000 : ℝ), (522056601/1000000000 : ℝ)] ![(1793940795013/4000000000000 : ℝ), (2914724090507/25000000000000 : ℝ), (43492583743623/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069439781/2000000000 : ℝ)|^4669 ≤ (1793940795013/4000000000000 : ℝ)^3645
        have hw : |(1069439781/2000000000 : ℝ)|=(1069439781/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-466978757/2500000000 : ℝ)|^4669 ≤ (2914724090507/25000000000000 : ℝ)^3645
        have hw : |(-466978757/2500000000 : ℝ)|=(466978757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(522056601/1000000000 : ℝ)|^4669 ≤ (43492583743623/100000000000000 : ℝ)^3645
        have hw : |(522056601/1000000000 : ℝ)|=(522056601/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s5_2 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673599453/5000000000 : ℝ)*x 0 + (5220566009/10000000000 : ℝ)*x 1 + (-466978757/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673599453/5000000000 : ℝ)^4669 ≤ (44848519886069/100000000000000 : ℝ)^3645 := by
    have hnat : (2673599453 : ℕ)^4669*100000000000000^3645 ≤ 44848519886069^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673599453 5000000000 44848519886069 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220566009/10000000000 : ℝ)^4669 ≤ (5436572966619/12500000000000 : ℝ)^3645 := by
    have hnat : (5220566009 : ℕ)^4669*12500000000000^3645 ≤ 5436572966619^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220566009 10000000000 5436572966619 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466978757/2500000000 : ℝ)^4669 ≤ (2914724090507/25000000000000 : ℝ)^3645 := by
    have hnat : (466978757 : ℕ)^4669*25000000000000^3645 ≤ 2914724090507^3645*2500000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466978757 2500000000 2914724090507 25000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673599453/5000000000 : ℝ), (5220566009/10000000000 : ℝ), (-466978757/2500000000 : ℝ)] ![(44848519886069/100000000000000 : ℝ), (5436572966619/12500000000000 : ℝ), (2914724090507/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673599453/5000000000 : ℝ)|^4669 ≤ (44848519886069/100000000000000 : ℝ)^3645
        have hw : |(2673599453/5000000000 : ℝ)|=(2673599453/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220566009/10000000000 : ℝ)|^4669 ≤ (5436572966619/12500000000000 : ℝ)^3645
        have hw : |(5220566009/10000000000 : ℝ)|=(5220566009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-466978757/2500000000 : ℝ)|^4669 ≤ (2914724090507/25000000000000 : ℝ)^3645
        have hw : |(-466978757/2500000000 : ℝ)|=(466978757/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s5_3 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2118256223/5000000000 : ℝ)*x 0 + (3999600413/10000000000 : ℝ)*x 1 + (4484520603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2118256223/5000000000 : ℝ)^4669 ≤ (260023723161/781250000000 : ℝ)^3645 := by
    have hnat : (2118256223 : ℕ)^4669*781250000000^3645 ≤ 260023723161^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2118256223 5000000000 260023723161 781250000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3999600413/10000000000 : ℝ)^4669 ≤ (15458951169483/50000000000000 : ℝ)^3645 := by
    have hnat : (3999600413 : ℕ)^4669*50000000000000^3645 ≤ 15458951169483^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3999600413 10000000000 15458951169483 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4484520603/10000000000 : ℝ)^4669 ≤ (3579906107571/10000000000000 : ℝ)^3645 := by
    have hnat : (4484520603 : ℕ)^4669*10000000000000^3645 ≤ 3579906107571^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4484520603 10000000000 3579906107571 10000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2118256223/5000000000 : ℝ), (3999600413/10000000000 : ℝ), (4484520603/10000000000 : ℝ)] ![(260023723161/781250000000 : ℝ), (15458951169483/50000000000000 : ℝ), (3579906107571/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2118256223/5000000000 : ℝ)|^4669 ≤ (260023723161/781250000000 : ℝ)^3645
        have hw : |(2118256223/5000000000 : ℝ)|=(2118256223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3999600413/10000000000 : ℝ)|^4669 ≤ (15458951169483/50000000000000 : ℝ)^3645
        have hw : |(3999600413/10000000000 : ℝ)|=(3999600413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4484520603/10000000000 : ℝ)|^4669 ≤ (3579906107571/10000000000000 : ℝ)^3645
        have hw : |(4484520603/10000000000 : ℝ)|=(4484520603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s5_4 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-882005939/5000000000 : ℝ)*x 0 + (5221628051/10000000000 : ℝ)*x 1 + (5422705033/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (882005939/5000000000 : ℝ)^4669 ≤ (2166950897379/20000000000000 : ℝ)^3645 := by
    have hnat : (882005939 : ℕ)^4669*20000000000000^3645 ≤ 2166950897379^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882005939 5000000000 2166950897379 20000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221628051/10000000000 : ℝ)^4669 ≤ (21751958799291/50000000000000 : ℝ)^3645 := by
    have hnat : (5221628051 : ℕ)^4669*50000000000000^3645 ≤ 21751958799291^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221628051 10000000000 21751958799291 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422705033/10000000000 : ℝ)^4669 ≤ (913226558147/2000000000000 : ℝ)^3645 := by
    have hnat : (5422705033 : ℕ)^4669*2000000000000^3645 ≤ 913226558147^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422705033 10000000000 913226558147 2000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-882005939/5000000000 : ℝ), (5221628051/10000000000 : ℝ), (5422705033/10000000000 : ℝ)] ![(2166950897379/20000000000000 : ℝ), (21751958799291/50000000000000 : ℝ), (913226558147/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-882005939/5000000000 : ℝ)|^4669 ≤ (2166950897379/20000000000000 : ℝ)^3645
        have hw : |(-882005939/5000000000 : ℝ)|=(882005939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221628051/10000000000 : ℝ)|^4669 ≤ (21751958799291/50000000000000 : ℝ)^3645
        have hw : |(5221628051/10000000000 : ℝ)|=(5221628051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422705033/10000000000 : ℝ)|^4669 ≤ (913226558147/2000000000000 : ℝ)^3645
        have hw : |(5422705033/10000000000 : ℝ)|=(5422705033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s5_5 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10338549/19531250 : ℝ)*x 0 + (-832888009/5000000000 : ℝ)*x 1 + (2711352487/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10338549/19531250 : ℝ)^4669 ≤ (22135336543197/50000000000000 : ℝ)^3645 := by
    have hnat : (10338549 : ℕ)^4669*50000000000000^3645 ≤ 22135336543197^3645*19531250^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10338549 19531250 22135336543197 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (832888009/5000000000 : ℝ)^4669 ≤ (5033999812673/50000000000000 : ℝ)^3645 := by
    have hnat : (832888009 : ℕ)^4669*50000000000000^3645 ≤ 5033999812673^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      832888009 5000000000 5033999812673 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2711352487/5000000000 : ℝ)^4669 ≤ (22830663635489/50000000000000 : ℝ)^3645 := by
    have hnat : (2711352487 : ℕ)^4669*50000000000000^3645 ≤ 22830663635489^3645*5000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711352487 5000000000 22830663635489 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10338549/19531250 : ℝ), (-832888009/5000000000 : ℝ), (2711352487/5000000000 : ℝ)] ![(22135336543197/50000000000000 : ℝ), (5033999812673/50000000000000 : ℝ), (22830663635489/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10338549/19531250 : ℝ)|^4669 ≤ (22135336543197/50000000000000 : ℝ)^3645
        have hw : |(10338549/19531250 : ℝ)|=(10338549/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-832888009/5000000000 : ℝ)|^4669 ≤ (5033999812673/50000000000000 : ℝ)^3645
        have hw : |(-832888009/5000000000 : ℝ)|=(832888009/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2711352487/5000000000 : ℝ)|^4669 ≤ (22830663635489/50000000000000 : ℝ)^3645
        have hw : |(2711352487/5000000000 : ℝ)|=(2711352487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s5_6 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293337063/10000000000 : ℝ)*x 0 + (1084541001/2000000000 : ℝ)*x 1 + (-1665776009/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293337063/10000000000 : ℝ)^4669 ≤ (5533834102321/12500000000000 : ℝ)^3645 := by
    have hnat : (5293337063 : ℕ)^4669*12500000000000^3645 ≤ 5533834102321^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293337063 10000000000 5533834102321 12500000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084541001/2000000000 : ℝ)^4669 ≤ (45661327605343/100000000000000 : ℝ)^3645 := by
    have hnat : (1084541001 : ℕ)^4669*100000000000000^3645 ≤ 45661327605343^3645*2000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084541001 2000000000 45661327605343 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1665776009/10000000000 : ℝ)^4669 ≤ (2516999888917/25000000000000 : ℝ)^3645 := by
    have hnat : (1665776009 : ℕ)^4669*25000000000000^3645 ≤ 2516999888917^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1665776009 10000000000 2516999888917 25000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293337063/10000000000 : ℝ), (1084541001/2000000000 : ℝ), (-1665776009/10000000000 : ℝ)] ![(5533834102321/12500000000000 : ℝ), (45661327605343/100000000000000 : ℝ), (2516999888917/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293337063/10000000000 : ℝ)|^4669 ≤ (5533834102321/12500000000000 : ℝ)^3645
        have hw : |(5293337063/10000000000 : ℝ)|=(5293337063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084541001/2000000000 : ℝ)|^4669 ≤ (45661327605343/100000000000000 : ℝ)^3645
        have hw : |(1084541001/2000000000 : ℝ)|=(1084541001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1665776009/10000000000 : ℝ)|^4669 ≤ (2516999888917/25000000000000 : ℝ)^3645
        have hw : |(-1665776009/10000000000 : ℝ)|=(1665776009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1586_s5_7 (p : ℝ) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4236575053/10000000000 : ℝ)*x 0 + (4481986051/10000000000 : ℝ)*x 1 + (4002153709/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4236575053/10000000000 : ℝ)^4669 ≤ (16641833299743/50000000000000 : ℝ)^3645 := by
    have hnat : (4236575053 : ℕ)^4669*50000000000000^3645 ≤ 16641833299743^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4236575053 10000000000 16641833299743 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4481986051/10000000000 : ℝ)^4669 ≤ (17886573113561/50000000000000 : ℝ)^3645 := by
    have hnat : (4481986051 : ℕ)^4669*50000000000000^3645 ≤ 17886573113561^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481986051 10000000000 17886573113561 50000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4002153709/10000000000 : ℝ)^4669 ≤ (30943187158541/100000000000000 : ℝ)^3645 := by
    have hnat : (4002153709 : ℕ)^4669*100000000000000^3645 ≤ 30943187158541^3645*10000000000^4669 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002153709 10000000000 30943187158541 100000000000000 4669 3645 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4669/1024 : ℝ)) 4669 3645 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4236575053/10000000000 : ℝ), (4481986051/10000000000 : ℝ), (4002153709/10000000000 : ℝ)] ![(16641833299743/50000000000000 : ℝ), (17886573113561/50000000000000 : ℝ), (30943187158541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4236575053/10000000000 : ℝ)|^4669 ≤ (16641833299743/50000000000000 : ℝ)^3645
        have hw : |(4236575053/10000000000 : ℝ)|=(4236575053/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4481986051/10000000000 : ℝ)|^4669 ≤ (17886573113561/50000000000000 : ℝ)^3645
        have hw : |(4481986051/10000000000 : ℝ)|=(4481986051/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4002153709/10000000000 : ℝ)|^4669 ≤ (30943187158541/100000000000000 : ℝ)^3645
        have hw : |(4002153709/10000000000 : ℝ)|=(4002153709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1586_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2793/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15483/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11169/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7743/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11169/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7743/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11169/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11169/100000 : ℝ) ^ (4667/1024 : ℝ) ≤ (71619881175869/1562500000000000000 : ℝ) := by
    have hpowers : (11169/100000 : ℝ)^4667 ≤ (71619881175869/1562500000000000000 : ℝ)^1024 := by
      have hnat : (11169 : ℕ)^4667*1562500000000000000^1024 ≤ 71619881175869^1024*100000^4667 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11169 100000 71619881175869 1562500000000000000 4667 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11169/100000 : ℝ)) (X := (71619881175869/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7743/50000 : ℝ) ^ (4667/1024 : ℝ) ≤ (20326061034837959/100000000000000000000 : ℝ) := by
    have hpowers : (7743/50000 : ℝ)^4667 ≤ (20326061034837959/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7743 : ℕ)^4667*100000000000000000000^1024 ≤ 20326061034837959^1024*50000^4667 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7743 50000 20326061034837959 100000000000000000000 4667 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7743/50000 : ℝ)) (X := (20326061034837959/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (781321619881175869/781250000000000000 : ℝ) ≤ (5000100568086653/5000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (781321619881175869/781250000000000000 : ℝ)^1024 ≤ (5000100568086653/5000000000000000 : ℝ)^4667 := by
      have hnat : (781321619881175869 : ℕ)^1024*5000000000000000^4667 ≤ 5000100568086653^4667*781250000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        781321619881175869 781250000000000000 5000100568086653 5000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000100568086653/5000000000000000 : ℝ)) (X := (781321619881175869/781250000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4000996389337203743/4000000000000000000 : ℝ) ≤ (5000273249277113/5000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (4000996389337203743/4000000000000000000 : ℝ)^1024 ≤ (5000273249277113/5000000000000000 : ℝ)^4667 := by
      have hnat : (4000996389337203743 : ℕ)^1024*5000000000000000^4667 ≤ 5000273249277113^4667*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4000996389337203743 4000000000000000000 5000273249277113 5000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000273249277113/5000000000000000 : ℝ)) (X := (4000996389337203743/4000000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50020326061034837959/50000000000000000000 : ℝ) ≤ (5000445930467573/5000000000000000 : ℝ) ^ (4667/1024 : ℝ) := by
    have hpowers : (50020326061034837959/50000000000000000000 : ℝ)^1024 ≤ (5000445930467573/5000000000000000 : ℝ)^4667 := by
      have hnat : (50020326061034837959 : ℕ)^1024*5000000000000000^4667 ≤ 5000445930467573^4667*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020326061034837959 50000000000000000000 5000445930467573 5000000000000000 1024 4667 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000445930467573/5000000000000000 : ℝ)) (X := (50020326061034837959/50000000000000000000 : ℝ)) (by norm_num) 4667 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(71619881175869/1562500000000000000 : ℝ) ≤ ((7193858933332528507/7195000000000000000 : ℝ)+2*(2878019841/3597500000000 : ℝ)*(11169/100000 : ℝ))^(4667/1024 : ℝ) := by
    rw [show (7193858933332528507/7195000000000000000 : ℝ)+2*(2878019841/3597500000000 : ℝ)*(11169/100000 : ℝ)=(5000100568086653/5000000000000000 : ℝ) by norm_num, show 1+2*(71619881175869/1562500000000000000 : ℝ)=(781321619881175869/781250000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(20326061034837959/100000000000000000000 : ℝ)+(71619881175869/1562500000000000000 : ℝ) ≤ ((7193858933332528507/7195000000000000000 : ℝ)+(2878019841/3597500000000 : ℝ)*((7743/50000 : ℝ)+(11169/100000 : ℝ)))^(4667/1024 : ℝ) := by
    rw [show (7193858933332528507/7195000000000000000 : ℝ)+(2878019841/3597500000000 : ℝ)*((7743/50000 : ℝ)+(11169/100000 : ℝ))=(5000273249277113/5000000000000000 : ℝ) by norm_num, show 1+(20326061034837959/100000000000000000000 : ℝ)+(71619881175869/1562500000000000000 : ℝ)=(4000996389337203743/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(20326061034837959/100000000000000000000 : ℝ) ≤ ((7193858933332528507/7195000000000000000 : ℝ)+2*(2878019841/3597500000000 : ℝ)*(7743/50000 : ℝ))^(4667/1024 : ℝ) := by
    rw [show (7193858933332528507/7195000000000000000 : ℝ)+2*(2878019841/3597500000000 : ℝ)*(7743/50000 : ℝ)=(5000445930467573/5000000000000000 : ℝ) by norm_num, show 1+2*(20326061034837959/100000000000000000000 : ℝ)=(50020326061034837959/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7193858933332528507/7195000000000000000 : ℝ)*(X 1 0+X 2 0)+(2878019841/3597500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (7193858933332528507/7195000000000000000 : ℝ)) (alpha := (2878019841/3597500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7193858933332528507/7195000000000000000 : ℝ)*(X 0 1+X 2 1)+(2878019841/3597500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (7193858933332528507/7195000000000000000 : ℝ)) (alpha := (2878019841/3597500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7193858933332528507/7195000000000000000 : ℝ)*(X 0 2+X 1 2)+(2878019841/3597500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4667/1024 : ℝ)) (lo := (11169/100000 : ℝ)) (hi := (7743/50000 : ℝ)) (c := (7193858933332528507/7195000000000000000 : ℝ)) (alpha := (2878019841/3597500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1763985593/10000000000 : ℝ)*X 0 0+(1355943743/2500000000 : ℝ)*X 0 1+(5220566011/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069439781/2000000000 : ℝ)*X 1 0+(-466978757/2500000000 : ℝ)*X 1 1+(522056601/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673599453/5000000000 : ℝ)*X 2 0+(5220566009/10000000000 : ℝ)*X 2 1+(-466978757/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2118256223/5000000000 : ℝ)*X 0 0+(3999600413/10000000000 : ℝ)*X 0 1+(4484520603/10000000000 : ℝ)*X 0 2+(2118256223/5000000000 : ℝ)*X 1 0+(3999600413/10000000000 : ℝ)*X 1 1+(4484520603/10000000000 : ℝ)*X 1 2+(2118256223/5000000000 : ℝ)*X 2 0+(3999600413/10000000000 : ℝ)*X 2 1+(4484520603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-882005939/5000000000 : ℝ)*X 0 0+(5221628051/10000000000 : ℝ)*X 0 1+(5422705033/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((10338549/19531250 : ℝ)*X 1 0+(-832888009/5000000000 : ℝ)*X 1 1+(2711352487/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293337063/10000000000 : ℝ)*X 2 0+(1084541001/2000000000 : ℝ)*X 2 1+(-1665776009/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4236575053/10000000000 : ℝ)*X 0 0+(4481986051/10000000000 : ℝ)*X 0 1+(4002153709/10000000000 : ℝ)*X 0 2+(4236575053/10000000000 : ℝ)*X 1 0+(4481986051/10000000000 : ℝ)*X 1 1+(4002153709/10000000000 : ℝ)*X 1 2+(4236575053/10000000000 : ℝ)*X 2 0+(4481986051/10000000000 : ℝ)*X 2 1+(4002153709/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1586_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (894555507570351272139497823/179875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (416424349/50000000000000 : ℝ)*(base19) + (777977773/100000000000000 : ℝ)*(base23) + (14916341/50000000000000 : ℝ)*(lower2) + (122581289/100000000000000 : ℝ)*(upper3) + (323373/390625000000 : ℝ)*(upper5) + (3491638709964937/100000000000000 : ℝ)*(major0) + (3491638709964937/100000000000000 : ℝ)*(major1) + (3491638709964937/100000000000000 : ℝ)*(major2) + (2460528465988441/50000000000000 : ℝ)*(sp0) + (2460534851346817/50000000000000 : ℝ)*(sp1) + (61513371969557/1250000000000 : ℝ)*(sp2) + (6444376660097/312500000000 : ℝ)*(sp3) + (13603565451/100000000000000 : ℝ)*(sp4) + (6187382943/100000000000000 : ℝ)*(sp7) + (2062206718613983/100000000000000 : ℝ)*(f.failure) + (4921070535542333/100000000000000 : ℝ)*(f.sum) + (3560922263351/1439000000000000000000000000 : ℝ)*base65 + (2956877757944040941/719500000000000000000000000000000 : ℝ)*base68 + (7100103024962959059/719500000000000000000000000000000 : ℝ)*base69 + (5753457831271459059/719500000000000000000000000000000 : ℝ)*base71 + (4948833103843/1439000000000000000000000000 : ℝ)*base74 + (11406880545240459059/719500000000000000000000000000000 : ℝ)*base75 + (2025655956766459059/719500000000000000000000000000000 : ℝ)*base77 + (3569866661723459059/719500000000000000000000000000000 : ℝ)*base79 + (7736701376283/1439000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1385321/200000000000000000000 : ℝ)*base90 + (1385321/200000000000000000000 : ℝ)*base92 + (1385321/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100815322329212740284529329/35975000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (146561493/25000000000000 : ℝ)*(base19) + (142038449/25000000000000 : ℝ)*(base23) + (86870693/50000000000000 : ℝ)*(lower1) + (3680567/50000000000000 : ℝ)*(upper2) + (48352209/100000000000000 : ℝ)*(upper3) + (9718541/10000000000000 : ℝ)*(upper5) + (352863467980717/10000000000000 : ℝ)*(major0) + (352863467980717/10000000000000 : ℝ)*(major1) + (352863467980717/10000000000000 : ℝ)*(major2) + (26136923/3125000000000 : ℝ)*(sp1) + (2486606126047083/50000000000000 : ℝ)*(sp4) + (2486605414733329/50000000000000 : ℝ)*(sp5) + (4973211683940369/100000000000000 : ℝ)*(sp6) + (1042028507053887/50000000000000 : ℝ)*(sp7) + (1042028507053887/50000000000000 : ℝ)*(f.failure) + (2486606126047083/50000000000000 : ℝ)*(f.sum) + (2319901911737/719500000000000000000000000 : ℝ)*base65 + (694260050989799519/71950000000000000000000000000000 : ℝ)*base67 + (342851912116999519/71950000000000000000000000000000 : ℝ)*base69 + (339583888291099519/71950000000000000000000000000000 : ℝ)*base71 + (1433282676851/719500000000000000000000000 : ℝ)*base73 + (229256476927699519/71950000000000000000000000000000 : ℝ)*base75 + (368553385668249519/71950000000000000000000000000000 : ℝ)*base77 + (951927651520749519/71950000000000000000000000000000 : ℝ)*base79 + (758225485081/287800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (751369/100000000000000000000 : ℝ)*base90 + (751369/100000000000000000000 : ℝ)*base92 + (751369/100000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1586_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7743/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11169/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1586_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1586_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5453/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1586_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1586_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1586_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4667/1024 : ℝ) ≤ p) (hpb : p ≤ (4669/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (3386313/2000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15771/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5453/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2793/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15483/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1586_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
