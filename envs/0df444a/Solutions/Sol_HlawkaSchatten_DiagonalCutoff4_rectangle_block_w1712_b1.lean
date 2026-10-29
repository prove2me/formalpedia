-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1712_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:53:36.289426+00:00
-- url     : https://prove2.me/submissions/64aa1d88-bea5-4b8e-bff3-e213613b5c6b

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
theorem support_rectangle_w1712_s3_0 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1404882361/10000000000 : ℝ)*x 0 + (5468748859/10000000000 : ℝ)*x 1 + (642317849/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1404882361/10000000000 : ℝ)^5319 ≤ (2199697930087/25000000000000 : ℝ)^4295 := by
    have hnat : (1404882361 : ℕ)^5319*25000000000000^4295 ≤ 2199697930087^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404882361 10000000000 2199697930087 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468748859/10000000000 : ℝ)^5319 ≤ (2959893585407/6250000000000 : ℝ)^4295 := by
    have hnat : (5468748859 : ℕ)^5319*6250000000000^4295 ≤ 2959893585407^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468748859 10000000000 2959893585407 6250000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642317849/1250000000 : ℝ)^5319 ≤ (43842910886951/100000000000000 : ℝ)^4295 := by
    have hnat : (642317849 : ℕ)^5319*100000000000000^4295 ≤ 43842910886951^4295*1250000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642317849 1250000000 43842910886951 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1404882361/10000000000 : ℝ), (5468748859/10000000000 : ℝ), (642317849/1250000000 : ℝ)] ![(2199697930087/25000000000000 : ℝ), (2959893585407/6250000000000 : ℝ), (43842910886951/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1404882361/10000000000 : ℝ)|^5319 ≤ (2199697930087/25000000000000 : ℝ)^4295
        have hw : |(-1404882361/10000000000 : ℝ)|=(1404882361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468748859/10000000000 : ℝ)|^5319 ≤ (2959893585407/6250000000000 : ℝ)^4295
        have hw : |(5468748859/10000000000 : ℝ)|=(5468748859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642317849/1250000000 : ℝ)|^5319 ≤ (43842910886951/100000000000000 : ℝ)^4295
        have hw : |(642317849/1250000000 : ℝ)|=(642317849/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s3_1 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1335711179/2500000000 : ℝ)*x 0 + (-1576074573/10000000000 : ℝ)*x 1 + (2569271383/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1335711179/2500000000 : ℝ)^5319 ≤ (4601177262097/10000000000000 : ℝ)^4295 := by
    have hnat : (1335711179 : ℕ)^5319*10000000000000^4295 ≤ 4601177262097^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335711179 2500000000 4601177262097 10000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1576074573/10000000000 : ℝ)^5319 ≤ (5072658379413/50000000000000 : ℝ)^4295 := by
    have hnat : (1576074573 : ℕ)^5319*50000000000000^4295 ≤ 5072658379413^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1576074573 10000000000 5072658379413 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2569271383/5000000000 : ℝ)^5319 ≤ (1753716424489/4000000000000 : ℝ)^4295 := by
    have hnat : (2569271383 : ℕ)^5319*4000000000000^4295 ≤ 1753716424489^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569271383 5000000000 1753716424489 4000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1335711179/2500000000 : ℝ), (-1576074573/10000000000 : ℝ), (2569271383/5000000000 : ℝ)] ![(4601177262097/10000000000000 : ℝ), (5072658379413/50000000000000 : ℝ), (1753716424489/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1335711179/2500000000 : ℝ)|^5319 ≤ (4601177262097/10000000000000 : ℝ)^4295
        have hw : |(1335711179/2500000000 : ℝ)|=(1335711179/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1576074573/10000000000 : ℝ)|^5319 ≤ (5072658379413/50000000000000 : ℝ)^4295
        have hw : |(-1576074573/10000000000 : ℝ)|=(1576074573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2569271383/5000000000 : ℝ)|^5319 ≤ (1753716424489/4000000000000 : ℝ)^4295
        have hw : |(2569271383/5000000000 : ℝ)|=(2569271383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s3_2 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5342844699/10000000000 : ℝ)*x 0 + (2569271383/5000000000 : ℝ)*x 1 + (-394018649/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5342844699/10000000000 : ℝ)^5319 ≤ (2875735777479/6250000000000 : ℝ)^4295 := by
    have hnat : (5342844699 : ℕ)^5319*6250000000000^4295 ≤ 2875735777479^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5342844699 10000000000 2875735777479 6250000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2569271383/5000000000 : ℝ)^5319 ≤ (1753716424489/4000000000000 : ℝ)^4295 := by
    have hnat : (2569271383 : ℕ)^5319*4000000000000^4295 ≤ 1753716424489^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2569271383 5000000000 1753716424489 4000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (394018649/2500000000 : ℝ)^5319 ≤ (10145316942177/100000000000000 : ℝ)^4295 := by
    have hnat : (394018649 : ℕ)^5319*100000000000000^4295 ≤ 10145316942177^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      394018649 2500000000 10145316942177 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5342844699/10000000000 : ℝ), (2569271383/5000000000 : ℝ), (-394018649/2500000000 : ℝ)] ![(2875735777479/6250000000000 : ℝ), (1753716424489/4000000000000 : ℝ), (10145316942177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5342844699/10000000000 : ℝ)|^5319 ≤ (2875735777479/6250000000000 : ℝ)^4295
        have hw : |(5342844699/10000000000 : ℝ)|=(5342844699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2569271383/5000000000 : ℝ)|^5319 ≤ (1753716424489/4000000000000 : ℝ)^4295
        have hw : |(2569271383/5000000000 : ℝ)|=(2569271383/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-394018649/2500000000 : ℝ)|^5319 ≤ (10145316942177/100000000000000 : ℝ)^4295
        have hw : |(-394018649/2500000000 : ℝ)|=(394018649/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s3_3 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2051074147/5000000000 : ℝ)*x 0 + (727805243/2000000000 : ℝ)*x 1 + (920147853/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2051074147/5000000000 : ℝ)^5319 ≤ (414626245563/1250000000000 : ℝ)^4295 := by
    have hnat : (2051074147 : ℕ)^5319*1250000000000^4295 ≤ 414626245563^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2051074147 5000000000 414626245563 1250000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (727805243/2000000000 : ℝ)^5319 ≤ (14298375458239/50000000000000 : ℝ)^4295 := by
    have hnat : (727805243 : ℕ)^5319*50000000000000^4295 ≤ 14298375458239^4295*2000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      727805243 2000000000 14298375458239 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (920147853/2000000000 : ℝ)^5319 ≤ (38233149424717/100000000000000 : ℝ)^4295 := by
    have hnat : (920147853 : ℕ)^5319*100000000000000^4295 ≤ 38233149424717^4295*2000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      920147853 2000000000 38233149424717 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2051074147/5000000000 : ℝ), (727805243/2000000000 : ℝ), (920147853/2000000000 : ℝ)] ![(414626245563/1250000000000 : ℝ), (14298375458239/50000000000000 : ℝ), (38233149424717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2051074147/5000000000 : ℝ)|^5319 ≤ (414626245563/1250000000000 : ℝ)^4295
        have hw : |(2051074147/5000000000 : ℝ)|=(2051074147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(727805243/2000000000 : ℝ)|^5319 ≤ (14298375458239/50000000000000 : ℝ)^4295
        have hw : |(727805243/2000000000 : ℝ)|=(727805243/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(920147853/2000000000 : ℝ)|^5319 ≤ (38233149424717/100000000000000 : ℝ)^4295
        have hw : |(920147853/2000000000 : ℝ)|=(920147853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s3_4 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-702515851/5000000000 : ℝ)*x 0 + (2571103003/5000000000 : ℝ)*x 1 + (2732515511/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (702515851/5000000000 : ℝ)^5319 ≤ (2199987514023/25000000000000 : ℝ)^4295 := by
    have hnat : (702515851 : ℕ)^5319*25000000000000^4295 ≤ 2199987514023^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      702515851 5000000000 2199987514023 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571103003/5000000000 : ℝ)^5319 ≤ (21940810543463/50000000000000 : ℝ)^4295 := by
    have hnat : (2571103003 : ℕ)^5319*50000000000000^4295 ≤ 21940810543463^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571103003 5000000000 21940810543463 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732515511/5000000000 : ℝ)^5319 ≤ (9463685770217/20000000000000 : ℝ)^4295 := by
    have hnat : (2732515511 : ℕ)^5319*20000000000000^4295 ≤ 9463685770217^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732515511 5000000000 9463685770217 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-702515851/5000000000 : ℝ), (2571103003/5000000000 : ℝ), (2732515511/5000000000 : ℝ)] ![(2199987514023/25000000000000 : ℝ), (21940810543463/50000000000000 : ℝ), (9463685770217/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-702515851/5000000000 : ℝ)|^5319 ≤ (2199987514023/25000000000000 : ℝ)^4295
        have hw : |(-702515851/5000000000 : ℝ)|=(702515851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2571103003/5000000000 : ℝ)|^5319 ≤ (21940810543463/50000000000000 : ℝ)^4295
        have hw : |(2571103003/5000000000 : ℝ)|=(2571103003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732515511/5000000000 : ℝ)|^5319 ≤ (9463685770217/20000000000000 : ℝ)^4295
        have hw : |(2732515511/5000000000 : ℝ)|=(2732515511/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s3_5 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254454123/10000000000 : ℝ)*x 0 + (-124958613/1000000000 : ℝ)*x 1 + (2732515557/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254454123/10000000000 : ℝ)^5319 ≤ (22535474392731/50000000000000 : ℝ)^4295 := by
    have hnat : (5254454123 : ℕ)^5319*50000000000000^4295 ≤ 22535474392731^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254454123 10000000000 22535474392731 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (124958613/1000000000 : ℝ)^5319 ≤ (1522124271923/20000000000000 : ℝ)^4295 := by
    have hnat : (124958613 : ℕ)^5319*20000000000000^4295 ≤ 1522124271923^4295*1000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      124958613 1000000000 1522124271923 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732515557/5000000000 : ℝ)^5319 ≤ (23659214918787/50000000000000 : ℝ)^4295 := by
    have hnat : (2732515557 : ℕ)^5319*50000000000000^4295 ≤ 23659214918787^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732515557 5000000000 23659214918787 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254454123/10000000000 : ℝ), (-124958613/1000000000 : ℝ), (2732515557/5000000000 : ℝ)] ![(22535474392731/50000000000000 : ℝ), (1522124271923/20000000000000 : ℝ), (23659214918787/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254454123/10000000000 : ℝ)|^5319 ≤ (22535474392731/50000000000000 : ℝ)^4295
        have hw : |(5254454123/10000000000 : ℝ)|=(5254454123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-124958613/1000000000 : ℝ)|^5319 ≤ (1522124271923/20000000000000 : ℝ)^4295
        have hw : |(-124958613/1000000000 : ℝ)|=(124958613/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732515557/5000000000 : ℝ)|^5319 ≤ (23659214918787/50000000000000 : ℝ)^4295
        have hw : |(2732515557/5000000000 : ℝ)|=(2732515557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s3_6 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (525445409/1000000000 : ℝ)*x 0 + (5465031057/10000000000 : ℝ)*x 1 + (-624793129/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (525445409/1000000000 : ℝ)^5319 ≤ (45070948434913/100000000000000 : ℝ)^4295 := by
    have hnat : (525445409 : ℕ)^5319*100000000000000^4295 ≤ 45070948434913^4295*1000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525445409 1000000000 45070948434913 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465031057/10000000000 : ℝ)^5319 ≤ (47318429226379/100000000000000 : ℝ)^4295 := by
    have hnat : (5465031057 : ℕ)^5319*100000000000000^4295 ≤ 47318429226379^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465031057 10000000000 47318429226379 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (624793129/5000000000 : ℝ)^5319 ≤ (7610622325067/100000000000000 : ℝ)^4295 := by
    have hnat : (624793129 : ℕ)^5319*100000000000000^4295 ≤ 7610622325067^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      624793129 5000000000 7610622325067 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(525445409/1000000000 : ℝ), (5465031057/10000000000 : ℝ), (-624793129/5000000000 : ℝ)] ![(45070948434913/100000000000000 : ℝ), (47318429226379/100000000000000 : ℝ), (7610622325067/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(525445409/1000000000 : ℝ)|^5319 ≤ (45070948434913/100000000000000 : ℝ)^4295
        have hw : |(525445409/1000000000 : ℝ)|=(525445409/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465031057/10000000000 : ℝ)|^5319 ≤ (47318429226379/100000000000000 : ℝ)^4295
        have hw : |(5465031057/10000000000 : ℝ)|=(5465031057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-624793129/5000000000 : ℝ)|^5319 ≤ (7610622325067/100000000000000 : ℝ)^4295
        have hw : |(-624793129/5000000000 : ℝ)|=(624793129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s3_7 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4102582777/10000000000 : ℝ)*x 0 + (4590070291/10000000000 : ℝ)*x 1 + (1824927317/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4102582777/10000000000 : ℝ)^5319 ≤ (8293612639797/25000000000000 : ℝ)^4295 := by
    have hnat : (4102582777 : ℕ)^5319*25000000000000^4295 ≤ 8293612639797^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4102582777 10000000000 8293612639797 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4590070291/10000000000 : ℝ)^5319 ≤ (3812337989903/10000000000000 : ℝ)^4295 := by
    have hnat : (4590070291 : ℕ)^5319*10000000000000^4295 ≤ 3812337989903^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4590070291 10000000000 3812337989903 10000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1824927317/5000000000 : ℝ)^5319 ≤ (224235699439/781250000000 : ℝ)^4295 := by
    have hnat : (1824927317 : ℕ)^5319*781250000000^4295 ≤ 224235699439^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824927317 5000000000 224235699439 781250000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4102582777/10000000000 : ℝ), (4590070291/10000000000 : ℝ), (1824927317/5000000000 : ℝ)] ![(8293612639797/25000000000000 : ℝ), (3812337989903/10000000000000 : ℝ), (224235699439/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4102582777/10000000000 : ℝ)|^5319 ≤ (8293612639797/25000000000000 : ℝ)^4295
        have hw : |(4102582777/10000000000 : ℝ)|=(4102582777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4590070291/10000000000 : ℝ)|^5319 ≤ (3812337989903/10000000000000 : ℝ)^4295
        have hw : |(4590070291/10000000000 : ℝ)|=(4590070291/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1824927317/5000000000 : ℝ)|^5319 ≤ (224235699439/781250000000 : ℝ)^4295
        have hw : |(1824927317/5000000000 : ℝ)|=(1824927317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1712_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5013/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17079/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10017/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17089/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10017/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10017/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17089/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10017/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10017/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17089/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10017/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10017/100000 : ℝ) ^ (5311/1024 : ℝ) ≤ (656602489197317/100000000000000000000 : ℝ) := by
    have hpowers : (10017/100000 : ℝ)^5311 ≤ (656602489197317/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10017 : ℕ)^5311*100000000000000000000^1024 ≤ 656602489197317^1024*100000^5311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10017 100000 656602489197317 100000000000000000000 5311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10017/100000 : ℝ)) (X := (656602489197317/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17089/100000 : ℝ) ^ (5311/1024 : ℝ) ≤ (524127473785793/5000000000000000000 : ℝ) := by
    have hpowers : (17089/100000 : ℝ)^5311 ≤ (524127473785793/5000000000000000000 : ℝ)^1024 := by
      have hnat : (17089 : ℕ)^5311*5000000000000000000^1024 ≤ 524127473785793^1024*100000^5311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17089 100000 524127473785793 5000000000000000000 5311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17089/100000 : ℝ)) (X := (524127473785793/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000656602489197317/50000000000000000000 : ℝ) ≤ (2000005063885411/2000000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (50000656602489197317/50000000000000000000 : ℝ)^1024 ≤ (2000005063885411/2000000000000000 : ℝ)^5311 := by
      have hnat : (50000656602489197317 : ℕ)^1024*2000000000000000^5311 ≤ 2000005063885411^5311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000656602489197317 50000000000000000000 2000005063885411 2000000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000005063885411/2000000000000000 : ℝ)) (X := (50000656602489197317/50000000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100011139151964913177/100000000000000000000 : ℝ) ≤ (1000021476141673/1000000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (100011139151964913177/100000000000000000000 : ℝ)^1024 ≤ (1000021476141673/1000000000000000 : ℝ)^5311 := by
      have hnat : (100011139151964913177 : ℕ)^1024*1000000000000000^5311 ≤ 1000021476141673^5311*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011139151964913177 100000000000000000000 1000021476141673 1000000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000021476141673/1000000000000000 : ℝ)) (X := (100011139151964913177/100000000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2500524127473785793/2500000000000000000 : ℝ) ≤ (2000080840681281/2000000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (2500524127473785793/2500000000000000000 : ℝ)^1024 ≤ (2000080840681281/2000000000000000 : ℝ)^5311 := by
      have hnat : (2500524127473785793 : ℕ)^1024*2000000000000000^5311 ≤ 2000080840681281^5311*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500524127473785793 2500000000000000000 2000080840681281 2000000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000080840681281/2000000000000000 : ℝ)) (X := (2500524127473785793/2500000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(656602489197317/100000000000000000000 : ℝ) ≤ ((7071638377816698401/7072000000000000000 : ℝ)+2*(7577679587/28288000000000 : ℝ)*(10017/100000 : ℝ))^(5311/1024 : ℝ) := by
    rw [show (7071638377816698401/7072000000000000000 : ℝ)+2*(7577679587/28288000000000 : ℝ)*(10017/100000 : ℝ)=(2000005063885411/2000000000000000 : ℝ) by norm_num, show 1+2*(656602489197317/100000000000000000000 : ℝ)=(50000656602489197317/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(524127473785793/5000000000000000000 : ℝ)+(656602489197317/100000000000000000000 : ℝ) ≤ ((7071638377816698401/7072000000000000000 : ℝ)+(7577679587/28288000000000 : ℝ)*((17089/100000 : ℝ)+(10017/100000 : ℝ)))^(5311/1024 : ℝ) := by
    rw [show (7071638377816698401/7072000000000000000 : ℝ)+(7577679587/28288000000000 : ℝ)*((17089/100000 : ℝ)+(10017/100000 : ℝ))=(1000021476141673/1000000000000000 : ℝ) by norm_num, show 1+(524127473785793/5000000000000000000 : ℝ)+(656602489197317/100000000000000000000 : ℝ)=(100011139151964913177/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(524127473785793/5000000000000000000 : ℝ) ≤ ((7071638377816698401/7072000000000000000 : ℝ)+2*(7577679587/28288000000000 : ℝ)*(17089/100000 : ℝ))^(5311/1024 : ℝ) := by
    rw [show (7071638377816698401/7072000000000000000 : ℝ)+2*(7577679587/28288000000000 : ℝ)*(17089/100000 : ℝ)=(2000080840681281/2000000000000000 : ℝ) by norm_num, show 1+2*(524127473785793/5000000000000000000 : ℝ)=(2500524127473785793/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7071638377816698401/7072000000000000000 : ℝ)*(X 1 0+X 2 0)+(7577679587/28288000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (10017/100000 : ℝ)) (hi := (17089/100000 : ℝ)) (c := (7071638377816698401/7072000000000000000 : ℝ)) (alpha := (7577679587/28288000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7071638377816698401/7072000000000000000 : ℝ)*(X 0 1+X 2 1)+(7577679587/28288000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (10017/100000 : ℝ)) (hi := (17089/100000 : ℝ)) (c := (7071638377816698401/7072000000000000000 : ℝ)) (alpha := (7577679587/28288000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7071638377816698401/7072000000000000000 : ℝ)*(X 0 2+X 1 2)+(7577679587/28288000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (10017/100000 : ℝ)) (hi := (17089/100000 : ℝ)) (c := (7071638377816698401/7072000000000000000 : ℝ)) (alpha := (7577679587/28288000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1404882361/10000000000 : ℝ)*X 0 0+(5468748859/10000000000 : ℝ)*X 0 1+(642317849/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1335711179/2500000000 : ℝ)*X 1 0+(-1576074573/10000000000 : ℝ)*X 1 1+(2569271383/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5342844699/10000000000 : ℝ)*X 2 0+(2569271383/5000000000 : ℝ)*X 2 1+(-394018649/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2051074147/5000000000 : ℝ)*X 0 0+(727805243/2000000000 : ℝ)*X 0 1+(920147853/2000000000 : ℝ)*X 0 2+(2051074147/5000000000 : ℝ)*X 1 0+(727805243/2000000000 : ℝ)*X 1 1+(920147853/2000000000 : ℝ)*X 1 2+(2051074147/5000000000 : ℝ)*X 2 0+(727805243/2000000000 : ℝ)*X 2 1+(920147853/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-702515851/5000000000 : ℝ)*X 0 0+(2571103003/5000000000 : ℝ)*X 0 1+(2732515511/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5254454123/10000000000 : ℝ)*X 1 0+(-124958613/1000000000 : ℝ)*X 1 1+(2732515557/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((525445409/1000000000 : ℝ)*X 2 0+(5465031057/10000000000 : ℝ)*X 2 1+(-624793129/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4102582777/10000000000 : ℝ)*X 0 0+(4590070291/10000000000 : ℝ)*X 0 1+(1824927317/5000000000 : ℝ)*X 0 2+(4102582777/10000000000 : ℝ)*X 1 0+(4590070291/10000000000 : ℝ)*X 1 1+(1824927317/5000000000 : ℝ)*X 1 2+(4102582777/10000000000 : ℝ)*X 2 0+(4590070291/10000000000 : ℝ)*X 2 1+(1824927317/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (19860480982231649621841/1768000000000000000000000000 : ℝ) := by norm_num
    linear_combination (419887997/25000000000000 : ℝ)*(base19) + (784418563/50000000000000 : ℝ)*(base23) + (27002439/50000000000000 : ℝ)*(lower2) + (284561937/100000000000000 : ℝ)*(upper3) + (196722211/100000000000000 : ℝ)*(upper5) + (508533478883661/25000000000000 : ℝ)*(major0) + (508533478883661/25000000000000 : ℝ)*(major1) + (508533478883661/25000000000000 : ℝ)*(major2) + (189276792208343/6250000000000 : ℝ)*(sp0) + (30284430475431/1000000000000 : ℝ)*(sp1) + (3028443158257963/100000000000000 : ℝ)*(sp2) + (32494267682103/3125000000000 : ℝ)*(sp3) + (16051761601/100000000000000 : ℝ)*(sp4) + (6163703441/100000000000000 : ℝ)*(sp7) + (1039822729530737/100000000000000 : ℝ)*(f.failure) + (3028444727095089/100000000000000 : ℝ)*(f.sum) + (1473828175787/1768000000000000000000000000 : ℝ)*base65 + (828811020553723939/176800000000000000000000000000000 : ℝ)*base68 + (904901494348123939/176800000000000000000000000000000 : ℝ)*base70 + (732469732124676061/176800000000000000000000000000000 : ℝ)*base71 + (7739840498293/1768000000000000000000000000 : ℝ)*base74 + (791280598514276061/176800000000000000000000000000000 : ℝ)*base75 + (517829553216923939/176800000000000000000000000000000 : ℝ)*base78 + (329462380198276061/176800000000000000000000000000000 : ℝ)*base79 + (9877397432013/1768000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2072141/1250000000000000000000 : ℝ)*base89 + (2072141/1250000000000000000000 : ℝ)*base91 + (2072141/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (12027040281027313037316507/884000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (492546599/25000000000000 : ℝ)*(base19) + (980929043/50000000000000 : ℝ)*(base23) + (620158993/100000000000000 : ℝ)*(lower1) + (133186377/50000000000000 : ℝ)*(upper3) + (15440797/100000000000000 : ℝ)*(lower4) + (275068017/100000000000000 : ℝ)*(upper5) + (5201516856477/250000000000 : ℝ)*(major0) + (5201516856477/250000000000 : ℝ)*(major1) + (5201516856477/250000000000 : ℝ)*(major2) + (54274351/5000000000000 : ℝ)*(sp1) + (774408499756323/25000000000000 : ℝ)*(sp4) + (774407735837969/25000000000000 : ℝ)*(sp5) + (1548816018583603/50000000000000 : ℝ)*(sp6) + (531789516323999/50000000000000 : ℝ)*(sp7) + (531789516323999/50000000000000 : ℝ)*(f.failure) + (774408499756323/25000000000000 : ℝ)*(f.sum) + (1811372995329/442000000000000000000000000 : ℝ)*base66 + (7832781153583277/1768000000000000000000000000000 : ℝ)*base67 + (1822995578335277/1768000000000000000000000000000 : ℝ)*base69 + (884770385391277/1768000000000000000000000000000 : ℝ)*base71 + (1033135469601/442000000000000000000000000 : ℝ)*base74 + (2785567690655277/1768000000000000000000000000000 : ℝ)*base75 + (11140935782895277/1768000000000000000000000000000 : ℝ)*base77 + (17691833387263277/1768000000000000000000000000000 : ℝ)*base79 + (2689513897253/442000000000000000000000000 : ℝ)*base82 + (879107/625000000000000000000 : ℝ)*base89 + (879107/625000000000000000000 : ℝ)*base91 + (879107/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1712_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5013/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17079/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1712_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1712_s4_0 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1404886499/10000000000 : ℝ)*x 0 + (5468732267/10000000000 : ℝ)*x 1 + (1284639149/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1404886499/10000000000 : ℝ)^5319 ≤ (8798823815581/100000000000000 : ℝ)^4295 := by
    have hnat : (1404886499 : ℕ)^5319*100000000000000^4295 ≤ 8798823815581^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1404886499 10000000000 8798823815581 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5468732267/10000000000 : ℝ)^5319 ≤ (9471623885309/20000000000000 : ℝ)^4295 := by
    have hnat : (5468732267 : ℕ)^5319*20000000000000^4295 ≤ 9471623885309^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468732267 10000000000 9471623885309 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284639149/2500000000 : ℝ)^5319 ≤ (43843056745307/100000000000000 : ℝ)^4295 := by
    have hnat : (1284639149 : ℕ)^5319*100000000000000^4295 ≤ 43843056745307^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284639149 2500000000 43843056745307 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1404886499/10000000000 : ℝ), (5468732267/10000000000 : ℝ), (1284639149/2500000000 : ℝ)] ![(8798823815581/100000000000000 : ℝ), (9471623885309/20000000000000 : ℝ), (43843056745307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1404886499/10000000000 : ℝ)|^5319 ≤ (8798823815581/100000000000000 : ℝ)^4295
        have hw : |(-1404886499/10000000000 : ℝ)|=(1404886499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5468732267/10000000000 : ℝ)|^5319 ≤ (9471623885309/20000000000000 : ℝ)^4295
        have hw : |(5468732267/10000000000 : ℝ)|=(5468732267/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1284639149/2500000000 : ℝ)|^5319 ≤ (43843056745307/100000000000000 : ℝ)^4295
        have hw : |(1284639149/2500000000 : ℝ)|=(1284639149/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s4_1 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5342840059/10000000000 : ℝ)*x 0 + (-197007789/1250000000 : ℝ)*x 1 + (1027711343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5342840059/10000000000 : ℝ)^5319 ≤ (46011722953799/100000000000000 : ℝ)^4295 := by
    have hnat : (5342840059 : ℕ)^5319*100000000000000^4295 ≤ 46011722953799^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5342840059 10000000000 46011722953799 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (197007789/1250000000 : ℝ)^5319 ≤ (253630475421/2500000000000 : ℝ)^4295 := by
    have hnat : (197007789 : ℕ)^5319*2500000000000^4295 ≤ 253630475421^4295*1250000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      197007789 1250000000 253630475421 2500000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027711343/2000000000 : ℝ)^5319 ≤ (43843058002707/100000000000000 : ℝ)^4295 := by
    have hnat : (1027711343 : ℕ)^5319*100000000000000^4295 ≤ 43843058002707^4295*2000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027711343 2000000000 43843058002707 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5342840059/10000000000 : ℝ), (-197007789/1250000000 : ℝ), (1027711343/2000000000 : ℝ)] ![(46011722953799/100000000000000 : ℝ), (253630475421/2500000000000 : ℝ), (43843058002707/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5342840059/10000000000 : ℝ)|^5319 ≤ (46011722953799/100000000000000 : ℝ)^4295
        have hw : |(5342840059/10000000000 : ℝ)|=(5342840059/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-197007789/1250000000 : ℝ)|^5319 ≤ (253630475421/2500000000000 : ℝ)^4295
        have hw : |(-197007789/1250000000 : ℝ)|=(197007789/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027711343/2000000000 : ℝ)|^5319 ≤ (43843058002707/100000000000000 : ℝ)^4295
        have hw : |(1027711343/2000000000 : ℝ)|=(1027711343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s4_2 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2671420073/5000000000 : ℝ)*x 0 + (321159789/625000000 : ℝ)*x 1 + (-1576062317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2671420073/5000000000 : ℝ)^5319 ≤ (46011723881659/100000000000000 : ℝ)^4295 := by
    have hnat : (2671420073 : ℕ)^5319*100000000000000^4295 ≤ 46011723881659^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2671420073 5000000000 46011723881659 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (321159789/625000000 : ℝ)^5319 ≤ (21921528520583/50000000000000 : ℝ)^4295 := by
    have hnat : (321159789 : ℕ)^5319*50000000000000^4295 ≤ 21921528520583^4295*625000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      321159789 625000000 21921528520583 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1576062317/10000000000 : ℝ)^5319 ≤ (10145219056699/100000000000000 : ℝ)^4295 := by
    have hnat : (1576062317 : ℕ)^5319*100000000000000^4295 ≤ 10145219056699^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1576062317 10000000000 10145219056699 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2671420073/5000000000 : ℝ), (321159789/625000000 : ℝ), (-1576062317/10000000000 : ℝ)] ![(46011723881659/100000000000000 : ℝ), (21921528520583/50000000000000 : ℝ), (10145219056699/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2671420073/5000000000 : ℝ)|^5319 ≤ (46011723881659/100000000000000 : ℝ)^4295
        have hw : |(2671420073/5000000000 : ℝ)|=(2671420073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(321159789/625000000 : ℝ)|^5319 ≤ (21921528520583/50000000000000 : ℝ)^4295
        have hw : |(321159789/625000000 : ℝ)|=(321159789/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1576062317/10000000000 : ℝ)|^5319 ≤ (10145219056699/100000000000000 : ℝ)^4295
        have hw : |(-1576062317/10000000000 : ℝ)|=(1576062317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s4_3 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4102151233/10000000000 : ℝ)*x 0 + (181953523/500000000 : ℝ)*x 1 + (2300347283/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4102151233/10000000000 : ℝ)^5319 ≤ (33170129075827/100000000000000 : ℝ)^4295 := by
    have hnat : (4102151233 : ℕ)^5319*100000000000000^4295 ≤ 33170129075827^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4102151233 10000000000 33170129075827 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (181953523/500000000 : ℝ)^5319 ≤ (3574647688213/12500000000000 : ℝ)^4295 := by
    have hnat : (181953523 : ℕ)^5319*12500000000000^4295 ≤ 3574647688213^4295*500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181953523 500000000 3574647688213 12500000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2300347283/5000000000 : ℝ)^5319 ≤ (1911634470243/5000000000000 : ℝ)^4295 := by
    have hnat : (2300347283 : ℕ)^5319*5000000000000^4295 ≤ 1911634470243^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2300347283 5000000000 1911634470243 5000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4102151233/10000000000 : ℝ), (181953523/500000000 : ℝ), (2300347283/5000000000 : ℝ)] ![(33170129075827/100000000000000 : ℝ), (3574647688213/12500000000000 : ℝ), (1911634470243/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4102151233/10000000000 : ℝ)|^5319 ≤ (33170129075827/100000000000000 : ℝ)^4295
        have hw : |(4102151233/10000000000 : ℝ)|=(4102151233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(181953523/500000000 : ℝ)|^5319 ≤ (3574647688213/12500000000000 : ℝ)^4295
        have hw : |(181953523/500000000 : ℝ)|=(181953523/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2300347283/5000000000 : ℝ)|^5319 ≤ (1911634470243/5000000000000 : ℝ)^4295
        have hw : |(2300347283/5000000000 : ℝ)|=(2300347283/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s4_4 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1405035733/10000000000 : ℝ)*x 0 + (2571109587/5000000000 : ℝ)*x 1 + (5465015127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1405035733/10000000000 : ℝ)^5319 ≤ (4399990661101/50000000000000 : ℝ)^4295 := by
    have hnat : (1405035733 : ℕ)^5319*50000000000000^4295 ≤ 4399990661101^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1405035733 10000000000 4399990661101 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2571109587/5000000000 : ℝ)^5319 ≤ (21940880124351/50000000000000 : ℝ)^4295 := by
    have hnat : (2571109587 : ℕ)^5319*50000000000000^4295 ≤ 21940880124351^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2571109587 5000000000 21940880124351 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465015127/10000000000 : ℝ)^5319 ≤ (47318258413689/100000000000000 : ℝ)^4295 := by
    have hnat : (5465015127 : ℕ)^5319*100000000000000^4295 ≤ 47318258413689^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465015127 10000000000 47318258413689 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1405035733/10000000000 : ℝ), (2571109587/5000000000 : ℝ), (5465015127/10000000000 : ℝ)] ![(4399990661101/50000000000000 : ℝ), (21940880124351/50000000000000 : ℝ), (47318258413689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1405035733/10000000000 : ℝ)|^5319 ≤ (4399990661101/50000000000000 : ℝ)^4295
        have hw : |(-1405035733/10000000000 : ℝ)|=(1405035733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2571109587/5000000000 : ℝ)|^5319 ≤ (21940880124351/50000000000000 : ℝ)^4295
        have hw : |(2571109587/5000000000 : ℝ)|=(2571109587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465015127/10000000000 : ℝ)|^5319 ≤ (47318258413689/100000000000000 : ℝ)^4295
        have hw : |(5465015127/10000000000 : ℝ)|=(5465015127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s4_5 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1050891539/2000000000 : ℝ)*x 0 + (-1249603811/10000000000 : ℝ)*x 1 + (2732507569/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1050891539/2000000000 : ℝ)^5319 ≤ (45070986729837/100000000000000 : ℝ)^4295 := by
    have hnat : (1050891539 : ℕ)^5319*100000000000000^4295 ≤ 45070986729837^4295*2000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050891539 2000000000 45070986729837 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249603811/10000000000 : ℝ)^5319 ≤ (118918042507/1562500000000 : ℝ)^4295 := by
    have hnat : (1249603811 : ℕ)^5319*1562500000000^4295 ≤ 118918042507^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249603811 10000000000 118918042507 1562500000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732507569/5000000000 : ℝ)^5319 ≤ (47318258531639/100000000000000 : ℝ)^4295 := by
    have hnat : (2732507569 : ℕ)^5319*100000000000000^4295 ≤ 47318258531639^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732507569 5000000000 47318258531639 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1050891539/2000000000 : ℝ), (-1249603811/10000000000 : ℝ), (2732507569/5000000000 : ℝ)] ![(45070986729837/100000000000000 : ℝ), (118918042507/1562500000000 : ℝ), (47318258531639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1050891539/2000000000 : ℝ)|^5319 ≤ (45070986729837/100000000000000 : ℝ)^4295
        have hw : |(1050891539/2000000000 : ℝ)|=(1050891539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1249603811/10000000000 : ℝ)|^5319 ≤ (118918042507/1562500000000 : ℝ)^4295
        have hw : |(-1249603811/10000000000 : ℝ)|=(1249603811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732507569/5000000000 : ℝ)|^5319 ≤ (47318258531639/100000000000000 : ℝ)^4295
        have hw : |(2732507569/5000000000 : ℝ)|=(2732507569/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s4_6 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5254457727/10000000000 : ℝ)*x 0 + (2732507547/5000000000 : ℝ)*x 1 + (-1249603829/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5254457727/10000000000 : ℝ)^5319 ≤ (9014197413953/20000000000000 : ℝ)^4295 := by
    have hnat : (5254457727 : ℕ)^5319*20000000000000^4295 ≤ 9014197413953^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5254457727 10000000000 9014197413953 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2732507547/5000000000 : ℝ)^5319 ≤ (147869556437/312500000000 : ℝ)^4295 := by
    have hnat : (2732507547 : ℕ)^5319*312500000000^4295 ≤ 147869556437^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732507547 5000000000 147869556437 312500000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1249603829/10000000000 : ℝ)^5319 ≤ (1522150971243/20000000000000 : ℝ)^4295 := by
    have hnat : (1249603829 : ℕ)^5319*20000000000000^4295 ≤ 1522150971243^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249603829 10000000000 1522150971243 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5254457727/10000000000 : ℝ), (2732507547/5000000000 : ℝ), (-1249603829/10000000000 : ℝ)] ![(9014197413953/20000000000000 : ℝ), (147869556437/312500000000 : ℝ), (1522150971243/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5254457727/10000000000 : ℝ)|^5319 ≤ (9014197413953/20000000000000 : ℝ)^4295
        have hw : |(5254457727/10000000000 : ℝ)|=(5254457727/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2732507547/5000000000 : ℝ)|^5319 ≤ (147869556437/312500000000 : ℝ)^4295
        have hw : |(2732507547/5000000000 : ℝ)|=(2732507547/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1249603829/10000000000 : ℝ)|^5319 ≤ (1522150971243/20000000000000 : ℝ)^4295
        have hw : |(-1249603829/10000000000 : ℝ)|=(1249603829/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_s4_7 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4102585997/10000000000 : ℝ)*x 0 + (2295013759/5000000000 : ℝ)*x 1 + (1824948249/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4102585997/10000000000 : ℝ)^5319 ≤ (2073405175293/6250000000000 : ℝ)^4295 := by
    have hnat : (4102585997 : ℕ)^5319*6250000000000^4295 ≤ 2073405175293^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4102585997 10000000000 2073405175293 6250000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2295013759/5000000000 : ℝ)^5319 ≤ (38122939944177/100000000000000 : ℝ)^4295 := by
    have hnat : (2295013759 : ℕ)^5319*100000000000000^4295 ≤ 38122939944177^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2295013759 5000000000 38122939944177 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1824948249/5000000000 : ℝ)^5319 ≤ (7175644308593/25000000000000 : ℝ)^4295 := by
    have hnat : (1824948249 : ℕ)^5319*25000000000000^4295 ≤ 7175644308593^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1824948249 5000000000 7175644308593 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4102585997/10000000000 : ℝ), (2295013759/5000000000 : ℝ), (1824948249/5000000000 : ℝ)] ![(2073405175293/6250000000000 : ℝ), (38122939944177/100000000000000 : ℝ), (7175644308593/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4102585997/10000000000 : ℝ)|^5319 ≤ (2073405175293/6250000000000 : ℝ)^4295
        have hw : |(4102585997/10000000000 : ℝ)|=(4102585997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2295013759/5000000000 : ℝ)|^5319 ≤ (38122939944177/100000000000000 : ℝ)^4295
        have hw : |(2295013759/5000000000 : ℝ)|=(2295013759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1824948249/5000000000 : ℝ)|^5319 ≤ (7175644308593/25000000000000 : ℝ)^4295
        have hw : |(1824948249/5000000000 : ℝ)|=(1824948249/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1712_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5013/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10027/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8539/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5013/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17079/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5013/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5013/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17079/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5013/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5013/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17079/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5013/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5013/50000 : ℝ) ^ (5311/1024 : ℝ) ≤ (659667983482337/100000000000000000000 : ℝ) := by
    have hpowers : (5013/50000 : ℝ)^5311 ≤ (659667983482337/100000000000000000000 : ℝ)^1024 := by
      have hnat : (5013 : ℕ)^5311*100000000000000000000^1024 ≤ 659667983482337^1024*50000^5311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5013 50000 659667983482337 100000000000000000000 5311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5013/50000 : ℝ)) (X := (659667983482337/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17079/100000 : ℝ) ^ (5311/1024 : ℝ) ≤ (2090154762178869/20000000000000000000 : ℝ) := by
    have hpowers : (17079/100000 : ℝ)^5311 ≤ (2090154762178869/20000000000000000000 : ℝ)^1024 := by
      have hnat : (17079 : ℕ)^5311*20000000000000000000^1024 ≤ 2090154762178869^1024*100000^5311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17079 100000 2090154762178869 20000000000000000000 5311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17079/100000 : ℝ)) (X := (2090154762178869/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000659667983482337/50000000000000000000 : ℝ) ≤ (1250003179704473/1250000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (50000659667983482337/50000000000000000000 : ℝ)^1024 ≤ (1250003179704473/1250000000000000 : ℝ)^5311 := by
      have hnat : (50000659667983482337 : ℕ)^1024*1250000000000000^5311 ≤ 1250003179704473^5311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000659667983482337 50000000000000000000 1250003179704473 1250000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250003179704473/1250000000000000 : ℝ)) (X := (50000659667983482337/50000000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50005555220897188341/50000000000000000000 : ℝ) ≤ (5000107103956577/5000000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (50005555220897188341/50000000000000000000 : ℝ)^1024 ≤ (5000107103956577/5000000000000000 : ℝ)^5311 := by
      have hnat : (50005555220897188341 : ℕ)^1024*5000000000000000^5311 ≤ 5000107103956577^5311*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005555220897188341 50000000000000000000 5000107103956577 5000000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000107103956577/5000000000000000 : ℝ)) (X := (50005555220897188341/50000000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10002090154762178869/10000000000000000000 : ℝ) ≤ (2500100744547631/2500000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (10002090154762178869/10000000000000000000 : ℝ)^1024 ≤ (2500100744547631/2500000000000000 : ℝ)^5311 := by
      have hnat : (10002090154762178869 : ℕ)^1024*2500000000000000^5311 ≤ 2500100744547631^5311*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002090154762178869 10000000000000000000 2500100744547631 2500000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500100744547631/2500000000000000 : ℝ)) (X := (10002090154762178869/10000000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(659667983482337/100000000000000000000 : ℝ) ≤ ((734649939479618347/734687500000000000 : ℝ)+2*(6292342579/23510000000000 : ℝ)*(5013/50000 : ℝ))^(5311/1024 : ℝ) := by
    rw [show (734649939479618347/734687500000000000 : ℝ)+2*(6292342579/23510000000000 : ℝ)*(5013/50000 : ℝ)=(1250003179704473/1250000000000000 : ℝ) by norm_num, show 1+2*(659667983482337/100000000000000000000 : ℝ)=(50000659667983482337/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2090154762178869/20000000000000000000 : ℝ)+(659667983482337/100000000000000000000 : ℝ) ≤ ((734649939479618347/734687500000000000 : ℝ)+(6292342579/23510000000000 : ℝ)*((17079/100000 : ℝ)+(5013/50000 : ℝ)))^(5311/1024 : ℝ) := by
    rw [show (734649939479618347/734687500000000000 : ℝ)+(6292342579/23510000000000 : ℝ)*((17079/100000 : ℝ)+(5013/50000 : ℝ))=(5000107103956577/5000000000000000 : ℝ) by norm_num, show 1+(2090154762178869/20000000000000000000 : ℝ)+(659667983482337/100000000000000000000 : ℝ)=(50005555220897188341/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2090154762178869/20000000000000000000 : ℝ) ≤ ((734649939479618347/734687500000000000 : ℝ)+2*(6292342579/23510000000000 : ℝ)*(17079/100000 : ℝ))^(5311/1024 : ℝ) := by
    rw [show (734649939479618347/734687500000000000 : ℝ)+2*(6292342579/23510000000000 : ℝ)*(17079/100000 : ℝ)=(2500100744547631/2500000000000000 : ℝ) by norm_num, show 1+2*(2090154762178869/20000000000000000000 : ℝ)=(10002090154762178869/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (734649939479618347/734687500000000000 : ℝ)*(X 1 0+X 2 0)+(6292342579/23510000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (5013/50000 : ℝ)) (hi := (17079/100000 : ℝ)) (c := (734649939479618347/734687500000000000 : ℝ)) (alpha := (6292342579/23510000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (734649939479618347/734687500000000000 : ℝ)*(X 0 1+X 2 1)+(6292342579/23510000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (5013/50000 : ℝ)) (hi := (17079/100000 : ℝ)) (c := (734649939479618347/734687500000000000 : ℝ)) (alpha := (6292342579/23510000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (734649939479618347/734687500000000000 : ℝ)*(X 0 2+X 1 2)+(6292342579/23510000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (5013/50000 : ℝ)) (hi := (17079/100000 : ℝ)) (c := (734649939479618347/734687500000000000 : ℝ)) (alpha := (6292342579/23510000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1404886499/10000000000 : ℝ)*X 0 0+(5468732267/10000000000 : ℝ)*X 0 1+(1284639149/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5342840059/10000000000 : ℝ)*X 1 0+(-197007789/1250000000 : ℝ)*X 1 1+(1027711343/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2671420073/5000000000 : ℝ)*X 2 0+(321159789/625000000 : ℝ)*X 2 1+(-1576062317/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4102151233/10000000000 : ℝ)*X 0 0+(181953523/500000000 : ℝ)*X 0 1+(2300347283/5000000000 : ℝ)*X 0 2+(4102151233/10000000000 : ℝ)*X 1 0+(181953523/500000000 : ℝ)*X 1 1+(2300347283/5000000000 : ℝ)*X 1 2+(4102151233/10000000000 : ℝ)*X 2 0+(181953523/500000000 : ℝ)*X 2 1+(2300347283/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1405035733/10000000000 : ℝ)*X 0 0+(2571109587/5000000000 : ℝ)*X 0 1+(5465015127/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1050891539/2000000000 : ℝ)*X 1 0+(-1249603811/10000000000 : ℝ)*X 1 1+(2732507569/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5254457727/10000000000 : ℝ)*X 2 0+(2732507547/5000000000 : ℝ)*X 2 1+(-1249603829/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4102585997/10000000000 : ℝ)*X 0 0+(2295013759/5000000000 : ℝ)*X 0 1+(1824948249/5000000000 : ℝ)*X 0 2+(4102585997/10000000000 : ℝ)*X 1 0+(2295013759/5000000000 : ℝ)*X 1 1+(1824948249/5000000000 : ℝ)*X 1 2+(4102585997/10000000000 : ℝ)*X 2 0+(2295013759/5000000000 : ℝ)*X 2 1+(1824948249/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (117999414961720847315884311/36734375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8732181/2000000000000 : ℝ)*(base19) + (235856421/50000000000000 : ℝ)*(base23) + (7594303/100000000000000 : ℝ)*(lower2) + (35805609/50000000000000 : ℝ)*(upper3) + (8089733/12500000000000 : ℝ)*(upper5) + (508576524569883/25000000000000 : ℝ)*(major0) + (508576524569883/25000000000000 : ℝ)*(major1) + (508576524569883/25000000000000 : ℝ)*(major2) + (23661686954663/781250000000 : ℝ)*(sp0) + (3028700905771127/100000000000000 : ℝ)*(sp1) + (605740174133467/20000000000000 : ℝ)*(sp2) + (207981796944391/20000000000000 : ℝ)*(sp3) + (2706091657/50000000000000 : ℝ)*(sp4) + (1762382453/100000000000000 : ℝ)*(sp7) + (129988843388051/12500000000000 : ℝ)*(f.failure) + (3028701342380177/100000000000000 : ℝ)*(f.sum) + (6014509368449/1175500000000000000000000000 : ℝ)*base65 + (45765484885676737/9183593750000000000000000000000 : ℝ)*base68 + (28649790466993403/2295898437500000000000000000000 : ℝ)*base70 + (73606115561785073/36734375000000000000000000000000 : ℝ)*base72 + (6999352117613/1175500000000000000000000000 : ℝ)*base73 + (263934490003660073/36734375000000000000000000000000 : ℝ)*base76 + (7491029160783681/4591796875000000000000000000000 : ℝ)*base78 + (7203840267113889/1147949218750000000000000000000 : ℝ)*base80 + (5317388471977/2351000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (168457/156250000000000000000 : ℝ)*base90 + (168457/156250000000000000000 : ℝ)*base92 + (168457/156250000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (211918362233544844943013501/36734375000000000000000000000000 : ℝ) := by norm_num
    linear_combination (797903787/100000000000000 : ℝ)*(base19) + (88233539/10000000000000 : ℝ)*(base23) + (257578623/100000000000000 : ℝ)*(lower1) + (2691931/2500000000000 : ℝ)*(upper3) + (1310193/4000000000000 : ℝ)*(lower4) + (124343357/100000000000000 : ℝ)*(upper5) + (65025047316541/3125000000000 : ℝ)*(major0) + (65025047316541/3125000000000 : ℝ)*(major1) + (65025047316541/3125000000000 : ℝ)*(major2) + (95949321/50000000000000 : ℝ)*(sp2) + (1548962119321131/50000000000000 : ℝ)*(sp4) + (1548961720369237/50000000000000 : ℝ)*(sp5) + (309792316440823/10000000000000 : ℝ)*(sp6) + (1063678597318379/100000000000000 : ℝ)*(sp7) + (1063678597318379/100000000000000 : ℝ)*(f.failure) + (1548962119321131/50000000000000 : ℝ)*(f.sum) + (1873051459471/2351000000000000000000000000 : ℝ)*base66 + (301516747994218809/18367187500000000000000000000000 : ℝ)*base68 + (9668265811978523/2295898437500000000000000000000 : ℝ)*base70 + (905853734448328243/36734375000000000000000000000000 : ℝ)*base72 + (3366010302853/587750000000000000000000000 : ℝ)*base74 + (2401484521389875059/18367187500000000000000000000000 : ℝ)*base76 + (272351713678203243/36734375000000000000000000000000 : ℝ)*base78 + (248810205030468809/18367187500000000000000000000000 : ℝ)*base80 + (574979494719/1175500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (8620447/1250000000000000000000 : ℝ)*base89 + (8620447/1250000000000000000000 : ℝ)*base91 + (8620447/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1712_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17079/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5013/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10027/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8539/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1712_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1712_box_0 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1087805169/10000000000 : ℝ)*x 0 + (5416169863/10000000000 : ℝ)*x 1 + (5416170591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087805169/10000000000 : ℝ)^5319 ≤ (1281972619083/20000000000000 : ℝ)^4295 := by
    have hnat : (1087805169 : ℕ)^5319*20000000000000^4295 ≤ 1281972619083^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087805169 10000000000 1281972619083 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416169863/10000000000 : ℝ)^5319 ≤ (46795064551287/100000000000000 : ℝ)^4295 := by
    have hnat : (5416169863 : ℕ)^5319*100000000000000^4295 ≤ 46795064551287^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416169863 10000000000 46795064551287 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416170591/10000000000 : ℝ)^5319 ≤ (23397536170361/50000000000000 : ℝ)^4295 := by
    have hnat : (5416170591 : ℕ)^5319*50000000000000^4295 ≤ 23397536170361^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416170591 10000000000 23397536170361 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1087805169/10000000000 : ℝ), (5416169863/10000000000 : ℝ), (5416170591/10000000000 : ℝ)] ![(1281972619083/20000000000000 : ℝ), (46795064551287/100000000000000 : ℝ), (23397536170361/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1087805169/10000000000 : ℝ)|^5319 ≤ (1281972619083/20000000000000 : ℝ)^4295
        have hw : |(-1087805169/10000000000 : ℝ)|=(1087805169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416169863/10000000000 : ℝ)|^5319 ≤ (46795064551287/100000000000000 : ℝ)^4295
        have hw : |(5416169863/10000000000 : ℝ)|=(5416169863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416170591/10000000000 : ℝ)|^5319 ≤ (23397536170361/50000000000000 : ℝ)^4295
        have hw : |(5416170591/10000000000 : ℝ)|=(5416170591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_1 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612652551/5000000000 : ℝ)*x 0 + (-1358883809/10000000000 : ℝ)*x 1 + (5416170079/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612652551/5000000000 : ℝ)^5319 ≤ (44761511823557/100000000000000 : ℝ)^4295 := by
    have hnat : (2612652551 : ℕ)^5319*100000000000000^4295 ≤ 44761511823557^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612652551 5000000000 44761511823557 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358883809/10000000000 : ℝ)^5319 ≤ (2110855321891/25000000000000 : ℝ)^4295 := by
    have hnat : (1358883809 : ℕ)^5319*25000000000000^4295 ≤ 2110855321891^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358883809 10000000000 2110855321891 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416170079/10000000000 : ℝ)^5319 ≤ (23397533431219/50000000000000 : ℝ)^4295 := by
    have hnat : (5416170079 : ℕ)^5319*50000000000000^4295 ≤ 23397533431219^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416170079 10000000000 23397533431219 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612652551/5000000000 : ℝ), (-1358883809/10000000000 : ℝ), (5416170079/10000000000 : ℝ)] ![(44761511823557/100000000000000 : ℝ), (2110855321891/25000000000000 : ℝ), (23397533431219/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612652551/5000000000 : ℝ)|^5319 ≤ (44761511823557/100000000000000 : ℝ)^4295
        have hw : |(2612652551/5000000000 : ℝ)|=(2612652551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1358883809/10000000000 : ℝ)|^5319 ≤ (2110855321891/25000000000000 : ℝ)^4295
        have hw : |(-1358883809/10000000000 : ℝ)|=(1358883809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416170079/10000000000 : ℝ)|^5319 ≤ (23397533431219/50000000000000 : ℝ)^4295
        have hw : |(5416170079/10000000000 : ℝ)|=(5416170079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_2 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225304811/10000000000 : ℝ)*x 0 + (5416170413/10000000000 : ℝ)*x 1 + (-339720937/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225304811/10000000000 : ℝ)^5319 ≤ (44761508736441/100000000000000 : ℝ)^4295 := by
    have hnat : (5225304811 : ℕ)^5319*100000000000000^4295 ≤ 44761508736441^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225304811 10000000000 44761508736441 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416170413/10000000000 : ℝ)^5319 ≤ (23397535218081/50000000000000 : ℝ)^4295 := by
    have hnat : (5416170413 : ℕ)^5319*50000000000000^4295 ≤ 23397535218081^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416170413 10000000000 23397535218081 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339720937/2500000000 : ℝ)^5319 ≤ (337736832727/4000000000000 : ℝ)^4295 := by
    have hnat : (339720937 : ℕ)^5319*4000000000000^4295 ≤ 337736832727^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339720937 2500000000 337736832727 4000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225304811/10000000000 : ℝ), (5416170413/10000000000 : ℝ), (-339720937/2500000000 : ℝ)] ![(44761508736441/100000000000000 : ℝ), (23397535218081/50000000000000 : ℝ), (337736832727/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225304811/10000000000 : ℝ)|^5319 ≤ (44761508736441/100000000000000 : ℝ)^4295
        have hw : |(5225304811/10000000000 : ℝ)|=(5225304811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416170413/10000000000 : ℝ)|^5319 ≤ (23397535218081/50000000000000 : ℝ)^4295
        have hw : |(5416170413/10000000000 : ℝ)|=(5416170413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-339720937/2500000000 : ℝ)|^5319 ≤ (337736832727/4000000000000 : ℝ)^4295
        have hw : |(-339720937/2500000000 : ℝ)|=(339720937/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_3 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1120948933/2500000000 : ℝ)*x 0 + (1966432803/5000000000 : ℝ)*x 1 + (1966432921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120948933/2500000000 : ℝ)^5319 ≤ (37033293991823/100000000000000 : ℝ)^4295 := by
    have hnat : (1120948933 : ℕ)^5319*100000000000000^4295 ≤ 37033293991823^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120948933 2500000000 37033293991823 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1966432803/5000000000 : ℝ)^5319 ≤ (15741675912827/50000000000000 : ℝ)^4295 := by
    have hnat : (1966432803 : ℕ)^5319*50000000000000^4295 ≤ 15741675912827^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966432803 5000000000 15741675912827 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1966432921/5000000000 : ℝ)^5319 ≤ (31483354165303/100000000000000 : ℝ)^4295 := by
    have hnat : (1966432921 : ℕ)^5319*100000000000000^4295 ≤ 31483354165303^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966432921 5000000000 31483354165303 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120948933/2500000000 : ℝ), (1966432803/5000000000 : ℝ), (1966432921/5000000000 : ℝ)] ![(37033293991823/100000000000000 : ℝ), (15741675912827/50000000000000 : ℝ), (31483354165303/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120948933/2500000000 : ℝ)|^5319 ≤ (37033293991823/100000000000000 : ℝ)^4295
        have hw : |(1120948933/2500000000 : ℝ)|=(1120948933/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1966432803/5000000000 : ℝ)|^5319 ≤ (15741675912827/50000000000000 : ℝ)^4295
        have hw : |(1966432803/5000000000 : ℝ)|=(1966432803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1966432921/5000000000 : ℝ)|^5319 ≤ (31483354165303/100000000000000 : ℝ)^4295
        have hw : |(1966432921/5000000000 : ℝ)|=(1966432921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_4 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1742567223/10000000000 : ℝ)*x 0 + (258878109/500000000 : ℝ)*x 1 + (517756217/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1742567223/10000000000 : ℝ)^5319 ≤ (2297769194149/20000000000000 : ℝ)^4295 := by
    have hnat : (1742567223 : ℕ)^5319*20000000000000^4295 ≤ 2297769194149^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1742567223 10000000000 2297769194149 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258878109/500000000 : ℝ)^5319 ≤ (22127788530827/50000000000000 : ℝ)^4295 := by
    have hnat : (258878109 : ℕ)^5319*50000000000000^4295 ≤ 22127788530827^4295*500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258878109 500000000 22127788530827 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517756217/1000000000 : ℝ)^5319 ≤ (221277884779/500000000000 : ℝ)^4295 := by
    have hnat : (517756217 : ℕ)^5319*500000000000^4295 ≤ 221277884779^4295*1000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517756217 1000000000 221277884779 500000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1742567223/10000000000 : ℝ), (258878109/500000000 : ℝ), (517756217/1000000000 : ℝ)] ![(2297769194149/20000000000000 : ℝ), (22127788530827/50000000000000 : ℝ), (221277884779/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1742567223/10000000000 : ℝ)|^5319 ≤ (2297769194149/20000000000000 : ℝ)^4295
        have hw : |(-1742567223/10000000000 : ℝ)|=(1742567223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258878109/500000000 : ℝ)|^5319 ≤ (22127788530827/50000000000000 : ℝ)^4295
        have hw : |(258878109/500000000 : ℝ)|=(258878109/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517756217/1000000000 : ℝ)|^5319 ≤ (221277884779/500000000000 : ℝ)^4295
        have hw : |(517756217/1000000000 : ℝ)|=(517756217/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_5 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1346761527/2500000000 : ℝ)*x 0 + (-1464150487/10000000000 : ℝ)*x 1 + (5177562207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1346761527/2500000000 : ℝ)^5319 ≤ (46483646982539/100000000000000 : ℝ)^4295 := by
    have hnat : (1346761527 : ℕ)^5319*100000000000000^4295 ≤ 46483646982539^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346761527 2500000000 46483646982539 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1464150487/10000000000 : ℝ)^5319 ≤ (463038782507/5000000000000 : ℝ)^4295 := by
    have hnat : (1464150487 : ℕ)^5319*5000000000000^4295 ≤ 463038782507^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464150487 10000000000 463038782507 5000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177562207/10000000000 : ℝ)^5319 ≤ (22127788673731/50000000000000 : ℝ)^4295 := by
    have hnat : (5177562207 : ℕ)^5319*50000000000000^4295 ≤ 22127788673731^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177562207 10000000000 22127788673731 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1346761527/2500000000 : ℝ), (-1464150487/10000000000 : ℝ), (5177562207/10000000000 : ℝ)] ![(46483646982539/100000000000000 : ℝ), (463038782507/5000000000000 : ℝ), (22127788673731/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1346761527/2500000000 : ℝ)|^5319 ≤ (46483646982539/100000000000000 : ℝ)^4295
        have hw : |(1346761527/2500000000 : ℝ)|=(1346761527/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1464150487/10000000000 : ℝ)|^5319 ≤ (463038782507/5000000000000 : ℝ)^4295
        have hw : |(-1464150487/10000000000 : ℝ)|=(1464150487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177562207/10000000000 : ℝ)|^5319 ≤ (22127788673731/50000000000000 : ℝ)^4295
        have hw : |(5177562207/10000000000 : ℝ)|=(5177562207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_6 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5387045893/10000000000 : ℝ)*x 0 + (5177562627/10000000000 : ℝ)*x 1 + (-1464150213/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5387045893/10000000000 : ℝ)^5319 ≤ (46483644685043/100000000000000 : ℝ)^4295 := by
    have hnat : (5387045893 : ℕ)^5319*100000000000000^4295 ≤ 46483644685043^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5387045893 10000000000 46483644685043 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177562627/10000000000 : ℝ)^5319 ≤ (5531947724169/12500000000000 : ℝ)^4295 := by
    have hnat : (5177562627 : ℕ)^5319*12500000000000^4295 ≤ 5531947724169^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177562627 10000000000 5531947724169 12500000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1464150213/10000000000 : ℝ)^5319 ≤ (9260773503897/100000000000000 : ℝ)^4295 := by
    have hnat : (1464150213 : ℕ)^5319*100000000000000^4295 ≤ 9260773503897^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1464150213 10000000000 9260773503897 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5387045893/10000000000 : ℝ), (5177562627/10000000000 : ℝ), (-1464150213/10000000000 : ℝ)] ![(46483644685043/100000000000000 : ℝ), (5531947724169/12500000000000 : ℝ), (9260773503897/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5387045893/10000000000 : ℝ)|^5319 ≤ (46483644685043/100000000000000 : ℝ)^4295
        have hw : |(5387045893/10000000000 : ℝ)|=(5387045893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177562627/10000000000 : ℝ)|^5319 ≤ (5531947724169/12500000000000 : ℝ)^4295
        have hw : |(5177562627/10000000000 : ℝ)|=(5177562627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1464150213/10000000000 : ℝ)|^5319 ≤ (9260773503897/100000000000000 : ℝ)^4295
        have hw : |(-1464150213/10000000000 : ℝ)|=(1464150213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_7 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (740950343/2000000000 : ℝ)*x 0 + (172862543/400000000 : ℝ)*x 1 + (2160781831/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (740950343/2000000000 : ℝ)^5319 ≤ (29237756836293/100000000000000 : ℝ)^4295 := by
    have hnat : (740950343 : ℕ)^5319*100000000000000^4295 ≤ 29237756836293^4295*2000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      740950343 2000000000 29237756836293 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (172862543/400000000 : ℝ)^5319 ≤ (35381121132039/100000000000000 : ℝ)^4295 := by
    have hnat : (172862543 : ℕ)^5319*100000000000000^4295 ≤ 35381121132039^4295*400000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      172862543 400000000 35381121132039 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2160781831/5000000000 : ℝ)^5319 ≤ (35381122014137/100000000000000 : ℝ)^4295 := by
    have hnat : (2160781831 : ℕ)^5319*100000000000000^4295 ≤ 35381122014137^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160781831 5000000000 35381122014137 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(740950343/2000000000 : ℝ), (172862543/400000000 : ℝ), (2160781831/5000000000 : ℝ)] ![(29237756836293/100000000000000 : ℝ), (35381121132039/100000000000000 : ℝ), (35381122014137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(740950343/2000000000 : ℝ)|^5319 ≤ (29237756836293/100000000000000 : ℝ)^4295
        have hw : |(740950343/2000000000 : ℝ)|=(740950343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(172862543/400000000 : ℝ)|^5319 ≤ (35381121132039/100000000000000 : ℝ)^4295
        have hw : |(172862543/400000000 : ℝ)|=(172862543/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2160781831/5000000000 : ℝ)|^5319 ≤ (35381122014137/100000000000000 : ℝ)^4295
        have hw : |(2160781831/5000000000 : ℝ)|=(2160781831/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_8 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1601712901/10000000000 : ℝ)*x 0 + (5001351713/10000000000 : ℝ)*x 1 + (1091766299/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1601712901/10000000000 : ℝ)^5319 ≤ (10350094753779/100000000000000 : ℝ)^4295 := by
    have hnat : (1601712901 : ℕ)^5319*100000000000000^4295 ≤ 10350094753779^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1601712901 10000000000 10350094753779 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5001351713/10000000000 : ℝ)^5319 ≤ (42397943107561/100000000000000 : ℝ)^4295 := by
    have hnat : (5001351713 : ℕ)^5319*100000000000000^4295 ≤ 42397943107561^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5001351713 10000000000 42397943107561 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1091766299/2000000000 : ℝ)^5319 ≤ (11812990530317/25000000000000 : ℝ)^4295 := by
    have hnat : (1091766299 : ℕ)^5319*25000000000000^4295 ≤ 11812990530317^4295*2000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1091766299 2000000000 11812990530317 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1601712901/10000000000 : ℝ), (5001351713/10000000000 : ℝ), (1091766299/2000000000 : ℝ)] ![(10350094753779/100000000000000 : ℝ), (42397943107561/100000000000000 : ℝ), (11812990530317/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1601712901/10000000000 : ℝ)|^5319 ≤ (10350094753779/100000000000000 : ℝ)^4295
        have hw : |(-1601712901/10000000000 : ℝ)|=(1601712901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5001351713/10000000000 : ℝ)|^5319 ≤ (42397943107561/100000000000000 : ℝ)^4295
        have hw : |(5001351713/10000000000 : ℝ)|=(5001351713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1091766299/2000000000 : ℝ)|^5319 ≤ (11812990530317/25000000000000 : ℝ)^4295
        have hw : |(1091766299/2000000000 : ℝ)|=(1091766299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_9 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598203487/5000000000 : ℝ)*x 0 + (-133928841/1000000000 : ℝ)*x 1 + (5458831197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598203487/5000000000 : ℝ)^5319 ≤ (44455144241291/100000000000000 : ℝ)^4295 := by
    have hnat : (2598203487 : ℕ)^5319*100000000000000^4295 ≤ 44455144241291^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598203487 5000000000 44455144241291 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (133928841/1000000000 : ℝ)^5319 ≤ (8292896815151/100000000000000 : ℝ)^4295 := by
    have hnat : (133928841 : ℕ)^5319*100000000000000^4295 ≤ 8292896815151^4295*1000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133928841 1000000000 8292896815151 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5458831197/10000000000 : ℝ)^5319 ≤ (23625979463383/50000000000000 : ℝ)^4295 := by
    have hnat : (5458831197 : ℕ)^5319*50000000000000^4295 ≤ 23625979463383^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5458831197 10000000000 23625979463383 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598203487/5000000000 : ℝ), (-133928841/1000000000 : ℝ), (5458831197/10000000000 : ℝ)] ![(44455144241291/100000000000000 : ℝ), (8292896815151/100000000000000 : ℝ), (23625979463383/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598203487/5000000000 : ℝ)|^5319 ≤ (44455144241291/100000000000000 : ℝ)^4295
        have hw : |(2598203487/5000000000 : ℝ)|=(2598203487/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-133928841/1000000000 : ℝ)|^5319 ≤ (8292896815151/100000000000000 : ℝ)^4295
        have hw : |(-133928841/1000000000 : ℝ)|=(133928841/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5458831197/10000000000 : ℝ)|^5319 ≤ (23625979463383/50000000000000 : ℝ)^4295
        have hw : |(5458831197/10000000000 : ℝ)|=(5458831197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_10 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039281153/2000000000 : ℝ)*x 0 + (545883229/1000000000 : ℝ)*x 1 + (-1339288553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039281153/2000000000 : ℝ)^5319 ≤ (22227565716193/50000000000000 : ℝ)^4295 := by
    have hnat : (1039281153 : ℕ)^5319*50000000000000^4295 ≤ 22227565716193^4295*2000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039281153 2000000000 22227565716193 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545883229/1000000000 : ℝ)^5319 ≤ (9450394128703/20000000000000 : ℝ)^4295 := by
    have hnat : (545883229 : ℕ)^5319*20000000000000^4295 ≤ 9450394128703^4295*1000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545883229 1000000000 9450394128703 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1339288553/10000000000 : ℝ)^5319 ≤ (8292897911717/100000000000000 : ℝ)^4295 := by
    have hnat : (1339288553 : ℕ)^5319*100000000000000^4295 ≤ 8292897911717^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1339288553 10000000000 8292897911717 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039281153/2000000000 : ℝ), (545883229/1000000000 : ℝ), (-1339288553/10000000000 : ℝ)] ![(22227565716193/50000000000000 : ℝ), (9450394128703/20000000000000 : ℝ), (8292897911717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039281153/2000000000 : ℝ)|^5319 ≤ (22227565716193/50000000000000 : ℝ)^4295
        have hw : |(1039281153/2000000000 : ℝ)|=(1039281153/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545883229/1000000000 : ℝ)|^5319 ≤ (9450394128703/20000000000000 : ℝ)^4295
        have hw : |(545883229/1000000000 : ℝ)|=(545883229/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1339288553/10000000000 : ℝ)|^5319 ≤ (8292897911717/100000000000000 : ℝ)^4295
        have hw : |(-1339288553/10000000000 : ℝ)|=(1339288553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_11 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4618100287/10000000000 : ℝ)*x 0 + (241449271/625000000 : ℝ)*x 1 + (965796901/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4618100287/10000000000 : ℝ)^5319 ≤ (38411900923943/100000000000000 : ℝ)^4295 := by
    have hnat : (4618100287 : ℕ)^5319*100000000000000^4295 ≤ 38411900923943^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4618100287 10000000000 38411900923943 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241449271/625000000 : ℝ)^5319 ≤ (15397026570669/50000000000000 : ℝ)^4295 := by
    have hnat : (241449271 : ℕ)^5319*50000000000000^4295 ≤ 15397026570669^4295*625000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241449271 625000000 15397026570669 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (965796901/2500000000 : ℝ)^5319 ≤ (30794045915323/100000000000000 : ℝ)^4295 := by
    have hnat : (965796901 : ℕ)^5319*100000000000000^4295 ≤ 30794045915323^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      965796901 2500000000 30794045915323 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4618100287/10000000000 : ℝ), (241449271/625000000 : ℝ), (965796901/2500000000 : ℝ)] ![(38411900923943/100000000000000 : ℝ), (15397026570669/50000000000000 : ℝ), (30794045915323/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4618100287/10000000000 : ℝ)|^5319 ≤ (38411900923943/100000000000000 : ℝ)^4295
        have hw : |(4618100287/10000000000 : ℝ)|=(4618100287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241449271/625000000 : ℝ)|^5319 ≤ (15397026570669/50000000000000 : ℝ)^4295
        have hw : |(241449271/625000000 : ℝ)|=(241449271/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(965796901/2500000000 : ℝ)|^5319 ≤ (30794045915323/100000000000000 : ℝ)^4295
        have hw : |(965796901/2500000000 : ℝ)|=(965796901/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_12 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1223148147/10000000000 : ℝ)*x 0 + (698010043/1250000000 : ℝ)*x 1 + (5152461351/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1223148147/10000000000 : ℝ)^5319 ≤ (3705858025867/50000000000000 : ℝ)^4295 := by
    have hnat : (1223148147 : ℕ)^5319*50000000000000^4295 ≤ 3705858025867^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1223148147 10000000000 3705858025867 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (698010043/1250000000 : ℝ)^5319 ≤ (24299128403119/50000000000000 : ℝ)^4295 := by
    have hnat : (698010043 : ℕ)^5319*50000000000000^4295 ≤ 24299128403119^4295*1250000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      698010043 1250000000 24299128403119 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152461351/10000000000 : ℝ)^5319 ≤ (21995013562799/50000000000000 : ℝ)^4295 := by
    have hnat : (5152461351 : ℕ)^5319*50000000000000^4295 ≤ 21995013562799^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152461351 10000000000 21995013562799 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1223148147/10000000000 : ℝ), (698010043/1250000000 : ℝ), (5152461351/10000000000 : ℝ)] ![(3705858025867/50000000000000 : ℝ), (24299128403119/50000000000000 : ℝ), (21995013562799/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1223148147/10000000000 : ℝ)|^5319 ≤ (3705858025867/50000000000000 : ℝ)^4295
        have hw : |(-1223148147/10000000000 : ℝ)|=(1223148147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(698010043/1250000000 : ℝ)|^5319 ≤ (24299128403119/50000000000000 : ℝ)^4295
        have hw : |(698010043/1250000000 : ℝ)|=(698010043/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152461351/10000000000 : ℝ)|^5319 ≤ (21995013562799/50000000000000 : ℝ)^4295
        have hw : |(5152461351/10000000000 : ℝ)|=(5152461351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_13 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5404092007/10000000000 : ℝ)*x 0 + (-1474779809/10000000000 : ℝ)*x 1 + (5152461081/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5404092007/10000000000 : ℝ)^5319 ≤ (46665868596889/100000000000000 : ℝ)^4295 := by
    have hnat : (5404092007 : ℕ)^5319*100000000000000^4295 ≤ 46665868596889^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404092007 10000000000 46665868596889 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1474779809/10000000000 : ℝ)^5319 ≤ (292003347409/3125000000000 : ℝ)^4295 := by
    have hnat : (1474779809 : ℕ)^5319*3125000000000^4295 ≤ 292003347409^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1474779809 10000000000 292003347409 3125000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152461081/10000000000 : ℝ)^5319 ≤ (8798004854167/20000000000000 : ℝ)^4295 := by
    have hnat : (5152461081 : ℕ)^5319*20000000000000^4295 ≤ 8798004854167^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152461081 10000000000 8798004854167 20000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5404092007/10000000000 : ℝ), (-1474779809/10000000000 : ℝ), (5152461081/10000000000 : ℝ)] ![(46665868596889/100000000000000 : ℝ), (292003347409/3125000000000 : ℝ), (8798004854167/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5404092007/10000000000 : ℝ)|^5319 ≤ (46665868596889/100000000000000 : ℝ)^4295
        have hw : |(5404092007/10000000000 : ℝ)|=(5404092007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1474779809/10000000000 : ℝ)|^5319 ≤ (292003347409/3125000000000 : ℝ)^4295
        have hw : |(-1474779809/10000000000 : ℝ)|=(1474779809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152461081/10000000000 : ℝ)|^5319 ≤ (8798004854167/20000000000000 : ℝ)^4295
        have hw : |(5152461081/10000000000 : ℝ)|=(5152461081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_14 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1351023039/2500000000 : ℝ)*x 0 + (2576230479/5000000000 : ℝ)*x 1 + (-368694943/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1351023039/2500000000 : ℝ)^5319 ≤ (46665870190307/100000000000000 : ℝ)^4295 := by
    have hnat : (1351023039 : ℕ)^5319*100000000000000^4295 ≤ 46665870190307^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351023039 2500000000 46665870190307 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2576230479/5000000000 : ℝ)^5319 ≤ (10997505742583/25000000000000 : ℝ)^4295 := by
    have hnat : (2576230479 : ℕ)^5319*25000000000000^4295 ≤ 10997505742583^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576230479 5000000000 10997505742583 25000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (368694943/2500000000 : ℝ)^5319 ≤ (9344106826767/100000000000000 : ℝ)^4295 := by
    have hnat : (368694943 : ℕ)^5319*100000000000000^4295 ≤ 9344106826767^4295*2500000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      368694943 2500000000 9344106826767 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1351023039/2500000000 : ℝ), (2576230479/5000000000 : ℝ), (-368694943/2500000000 : ℝ)] ![(46665870190307/100000000000000 : ℝ), (10997505742583/25000000000000 : ℝ), (9344106826767/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1351023039/2500000000 : ℝ)|^5319 ≤ (46665870190307/100000000000000 : ℝ)^4295
        have hw : |(1351023039/2500000000 : ℝ)|=(1351023039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2576230479/5000000000 : ℝ)|^5319 ≤ (10997505742583/25000000000000 : ℝ)^4295
        have hw : |(2576230479/5000000000 : ℝ)|=(2576230479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-368694943/2500000000 : ℝ)|^5319 ≤ (9344106826767/100000000000000 : ℝ)^4295
        have hw : |(-368694943/2500000000 : ℝ)|=(368694943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1712_box_15 (p : ℝ) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3619814189/10000000000 : ℝ)*x 0 + (2181171659/5000000000 : ℝ)*x 1 + (436234279/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3619814189/10000000000 : ℝ)^5319 ≤ (1136395957223/4000000000000 : ℝ)^4295 := by
    have hnat : (3619814189 : ℕ)^5319*4000000000000^4295 ≤ 1136395957223^4295*10000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3619814189 10000000000 1136395957223 4000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2181171659/5000000000 : ℝ)^5319 ≤ (35795053212081/100000000000000 : ℝ)^4295 := by
    have hnat : (2181171659 : ℕ)^5319*100000000000000^4295 ≤ 35795053212081^4295*5000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2181171659 5000000000 35795053212081 100000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (436234279/1000000000 : ℝ)^5319 ≤ (17897523923329/50000000000000 : ℝ)^4295 := by
    have hnat : (436234279 : ℕ)^5319*50000000000000^4295 ≤ 17897523923329^4295*1000000000^5319 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      436234279 1000000000 17897523923329 50000000000000 5319 4295 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5319/1024 : ℝ)) 5319 4295 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3619814189/10000000000 : ℝ), (2181171659/5000000000 : ℝ), (436234279/1000000000 : ℝ)] ![(1136395957223/4000000000000 : ℝ), (35795053212081/100000000000000 : ℝ), (17897523923329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3619814189/10000000000 : ℝ)|^5319 ≤ (1136395957223/4000000000000 : ℝ)^4295
        have hw : |(3619814189/10000000000 : ℝ)|=(3619814189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2181171659/5000000000 : ℝ)|^5319 ≤ (35795053212081/100000000000000 : ℝ)^4295
        have hw : |(2181171659/5000000000 : ℝ)|=(2181171659/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(436234279/1000000000 : ℝ)|^5319 ≤ (17897523923329/50000000000000 : ℝ)^4295
        have hw : |(436234279/1000000000 : ℝ)|=(436234279/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1712_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8539/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10027/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(13353/20000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58449/100000 : ℝ) ∧ (40773/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90451/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8539/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10027/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8539/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10027/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8539/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10027/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8539/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10027/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8539/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10027/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8539/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10027/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10027/100000 : ℝ) ^ (5311/1024 : ℝ) ≤ (132001861166063/20000000000000000000 : ℝ) := by
    have hpowers : (10027/100000 : ℝ)^5311 ≤ (132001861166063/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10027 : ℕ)^5311*20000000000000000000^1024 ≤ 132001861166063^1024*100000^5311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10027 100000 132001861166063 20000000000000000000 5311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10027/100000 : ℝ)) (X := (132001861166063/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8539/50000 : ℝ) ^ (5311/1024 : ℝ) ≤ (2611900131387553/25000000000000000000 : ℝ) := by
    have hpowers : (8539/50000 : ℝ)^5311 ≤ (2611900131387553/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8539 : ℕ)^5311*25000000000000000000^1024 ≤ 2611900131387553^1024*50000^5311 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8539 50000 2611900131387553 25000000000000000000 5311 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8539/50000 : ℝ)) (X := (2611900131387553/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000132001861166063/10000000000000000000 : ℝ) ≤ (10000025450797537/10000000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (10000132001861166063/10000000000000000000 : ℝ)^1024 ≤ (10000025450797537/10000000000000000 : ℝ)^5311 := by
      have hnat : (10000132001861166063 : ℕ)^1024*10000000000000000^5311 ≤ 10000025450797537^5311*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000132001861166063 10000000000000000000 10000025450797537 10000000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000025450797537/10000000000000000 : ℝ)) (X := (10000132001861166063/10000000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100011107609831380527/100000000000000000000 : ℝ) ≤ (10000214153315713/10000000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (100011107609831380527/100000000000000000000 : ℝ)^1024 ≤ (10000214153315713/10000000000000000 : ℝ)^5311 := by
      have hnat : (100011107609831380527 : ℕ)^1024*10000000000000000^5311 ≤ 10000214153315713^5311*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100011107609831380527 100000000000000000000 10000214153315713 10000000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000214153315713/10000000000000000 : ℝ)) (X := (100011107609831380527/100000000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12502611900131387553/12500000000000000000 : ℝ) ≤ (10000402855833889/10000000000000000 : ℝ) ^ (5311/1024 : ℝ) := by
    have hpowers : (12502611900131387553/12500000000000000000 : ℝ)^1024 ≤ (10000402855833889/10000000000000000 : ℝ)^5311 := by
      have hnat : (12502611900131387553 : ℕ)^1024*10000000000000000^5311 ≤ 10000402855833889^5311*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502611900131387553 12500000000000000000 10000402855833889 10000000000000000 1024 5311 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000402855833889/10000000000000000 : ℝ)) (X := (12502611900131387553/12500000000000000000 : ℝ)) (by norm_num) 5311 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(132001861166063/20000000000000000000 : ℝ) ≤ ((70506395213273931883/70510000000000000000 : ℝ)+2*(5896953693/22034375000000 : ℝ)*(10027/100000 : ℝ))^(5311/1024 : ℝ) := by
    rw [show (70506395213273931883/70510000000000000000 : ℝ)+2*(5896953693/22034375000000 : ℝ)*(10027/100000 : ℝ)=(10000025450797537/10000000000000000 : ℝ) by norm_num, show 1+2*(132001861166063/20000000000000000000 : ℝ)=(10000132001861166063/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2611900131387553/25000000000000000000 : ℝ)+(132001861166063/20000000000000000000 : ℝ) ≤ ((70506395213273931883/70510000000000000000 : ℝ)+(5896953693/22034375000000 : ℝ)*((8539/50000 : ℝ)+(10027/100000 : ℝ)))^(5311/1024 : ℝ) := by
    rw [show (70506395213273931883/70510000000000000000 : ℝ)+(5896953693/22034375000000 : ℝ)*((8539/50000 : ℝ)+(10027/100000 : ℝ))=(10000214153315713/10000000000000000 : ℝ) by norm_num, show 1+(2611900131387553/25000000000000000000 : ℝ)+(132001861166063/20000000000000000000 : ℝ)=(100011107609831380527/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2611900131387553/25000000000000000000 : ℝ) ≤ ((70506395213273931883/70510000000000000000 : ℝ)+2*(5896953693/22034375000000 : ℝ)*(8539/50000 : ℝ))^(5311/1024 : ℝ) := by
    rw [show (70506395213273931883/70510000000000000000 : ℝ)+2*(5896953693/22034375000000 : ℝ)*(8539/50000 : ℝ)=(10000402855833889/10000000000000000 : ℝ) by norm_num, show 1+2*(2611900131387553/25000000000000000000 : ℝ)=(12502611900131387553/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (70506395213273931883/70510000000000000000 : ℝ)*(X 1 0+X 2 0)+(5896953693/22034375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (10027/100000 : ℝ)) (hi := (8539/50000 : ℝ)) (c := (70506395213273931883/70510000000000000000 : ℝ)) (alpha := (5896953693/22034375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (70506395213273931883/70510000000000000000 : ℝ)*(X 0 1+X 2 1)+(5896953693/22034375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (10027/100000 : ℝ)) (hi := (8539/50000 : ℝ)) (c := (70506395213273931883/70510000000000000000 : ℝ)) (alpha := (5896953693/22034375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (70506395213273931883/70510000000000000000 : ℝ)*(X 0 2+X 1 2)+(5896953693/22034375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5311/1024 : ℝ)) (lo := (10027/100000 : ℝ)) (hi := (8539/50000 : ℝ)) (c := (70506395213273931883/70510000000000000000 : ℝ)) (alpha := (5896953693/22034375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1087805169/10000000000 : ℝ)*X 0 0+(5416169863/10000000000 : ℝ)*X 0 1+(5416170591/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2612652551/5000000000 : ℝ)*X 1 0+(-1358883809/10000000000 : ℝ)*X 1 1+(5416170079/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5225304811/10000000000 : ℝ)*X 2 0+(5416170413/10000000000 : ℝ)*X 2 1+(-339720937/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1120948933/2500000000 : ℝ)*X 0 0+(1966432803/5000000000 : ℝ)*X 0 1+(1966432921/5000000000 : ℝ)*X 0 2+(1120948933/2500000000 : ℝ)*X 1 0+(1966432803/5000000000 : ℝ)*X 1 1+(1966432921/5000000000 : ℝ)*X 1 2+(1120948933/2500000000 : ℝ)*X 2 0+(1966432803/5000000000 : ℝ)*X 2 1+(1966432921/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1742567223/10000000000 : ℝ)*X 0 0+(258878109/500000000 : ℝ)*X 0 1+(517756217/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1346761527/2500000000 : ℝ)*X 1 0+(-1464150487/10000000000 : ℝ)*X 1 1+(5177562207/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5387045893/10000000000 : ℝ)*X 2 0+(5177562627/10000000000 : ℝ)*X 2 1+(-1464150213/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((740950343/2000000000 : ℝ)*X 0 0+(172862543/400000000 : ℝ)*X 0 1+(2160781831/5000000000 : ℝ)*X 0 2+(740950343/2000000000 : ℝ)*X 1 0+(172862543/400000000 : ℝ)*X 1 1+(2160781831/5000000000 : ℝ)*X 1 2+(740950343/2000000000 : ℝ)*X 2 0+(172862543/400000000 : ℝ)*X 2 1+(2160781831/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1601712901/10000000000 : ℝ)*X 0 0+(5001351713/10000000000 : ℝ)*X 0 1+(1091766299/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2598203487/5000000000 : ℝ)*X 1 0+(-133928841/1000000000 : ℝ)*X 1 1+(5458831197/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1039281153/2000000000 : ℝ)*X 2 0+(545883229/1000000000 : ℝ)*X 2 1+(-1339288553/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4618100287/10000000000 : ℝ)*X 0 0+(241449271/625000000 : ℝ)*X 0 1+(965796901/2500000000 : ℝ)*X 0 2+(4618100287/10000000000 : ℝ)*X 1 0+(241449271/625000000 : ℝ)*X 1 1+(965796901/2500000000 : ℝ)*X 1 2+(4618100287/10000000000 : ℝ)*X 2 0+(241449271/625000000 : ℝ)*X 2 1+(965796901/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1223148147/10000000000 : ℝ)*X 0 0+(698010043/1250000000 : ℝ)*X 0 1+(5152461351/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5404092007/10000000000 : ℝ)*X 1 0+(-1474779809/10000000000 : ℝ)*X 1 1+(5152461081/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1351023039/2500000000 : ℝ)*X 2 0+(2576230479/5000000000 : ℝ)*X 2 1+(-368694943/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3619814189/10000000000 : ℝ)*X 0 0+(2181171659/5000000000 : ℝ)*X 0 1+(436234279/1000000000 : ℝ)*X 0 2+(3619814189/10000000000 : ℝ)*X 1 0+(2181171659/5000000000 : ℝ)*X 1 1+(436234279/1000000000 : ℝ)*X 1 2+(3619814189/10000000000 : ℝ)*X 2 0+(2181171659/5000000000 : ℝ)*X 2 1+(436234279/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1712_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-13353/20000 : ℝ) ≤ (-1176862789835377271031729595073469/1762750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2185701/12500000000000 : ℝ)*(upper1) + (2317727/50000000000000 : ℝ)*(upper4) + (49177177/100000000000000 : ℝ)*(upper5) + (680858913129727/50000000000000 : ℝ)*(major0) + (680858913129727/50000000000000 : ℝ)*(major1) + (680858913129727/50000000000000 : ℝ)*(major2) + (175040949/50000000000000 : ℝ)*(sp1) + (1328017/250000000000 : ℝ)*(sp3) + (2049596365917131/100000000000000 : ℝ)*(sp4) + (2049597204103773/100000000000000 : ℝ)*(sp5) + (2049572305518541/100000000000000 : ℝ)*(sp6) + (696091862778777/100000000000000 : ℝ)*(sp7) + (59413427/5000000000000 : ℝ)*(sp8) + (2524866713/10000000000000 : ℝ)*(sp14) + (348046196992789/50000000000000 : ℝ)*(f.failure) + (2049597554185671/100000000000000 : ℝ)*(f.sum) + (101067427836697/17627500000000000000000000000 : ℝ)*base65 + (40251119818873085941/3525500000000000000000000000000000 : ℝ)*base67 + (21981113770463585941/3525500000000000000000000000000000 : ℝ)*base69 + (44143074179343085941/3525500000000000000000000000000000 : ℝ)*base71 + (110121030998597/17627500000000000000000000000 : ℝ)*base73 + (35914470127697085941/3525500000000000000000000000000000 : ℝ)*base75 + (28234518738361585941/3525500000000000000000000000000000 : ℝ)*base77 + (18790121044124585941/3525500000000000000000000000000000 : ℝ)*base79 + (152787198988749/35255000000000000000000000000 : ℝ)*base81 + (3688577/625000000000000000000 : ℝ)*base89 + (3688577/625000000000000000000 : ℝ)*base91 + (3688577/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (58449/100000 : ℝ) ≤ (1030360938663301336999655386591023/1762750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10047461/100000000000000 : ℝ)*(lower1) + (21053049/100000000000000 : ℝ)*(lower4) + (6589063/100000000000000 : ℝ)*(lower5) + (1467109003316527/100000000000000 : ℝ)*(major0) + (1467109003316527/100000000000000 : ℝ)*(major1) + (1467109003316527/100000000000000 : ℝ)*(major2) + (1082381385593667/50000000000000 : ℝ)*(sp0) + (2164765159178259/100000000000000 : ℝ)*(sp1) + (2164764793957357/100000000000000 : ℝ)*(sp2) + (374983171416543/50000000000000 : ℝ)*(sp3) + (2255417027/100000000000000 : ℝ)*(sp6) + (646408497/100000000000000 : ℝ)*(sp7) + (15121569/800000000000 : ℝ)*(sp9) + (85563741/2000000000000 : ℝ)*(sp12) + (46872936827599/6250000000000 : ℝ)*(f.failure) + (135297940585899/6250000000000 : ℝ)*(f.sum) + (56407099004447/35255000000000000000000000000 : ℝ)*base65 + (18367653725021669659/7051000000000000000000000000000000 : ℝ)*base68 + (17565856571908669659/7051000000000000000000000000000000 : ℝ)*base70 + (26241978843263669659/7051000000000000000000000000000000 : ℝ)*base72 + (58742636240851/17627500000000000000000000000 : ℝ)*base73 + (9330710751849330341/7051000000000000000000000000000000 : ℝ)*base75 + (15705045318233669659/7051000000000000000000000000000000 : ℝ)*base78 + (7532155885349669659/7051000000000000000000000000000000 : ℝ)*base80 + (175047643551807/35255000000000000000000000000 : ℝ)*base81 + (1075157/78125000000000000000 : ℝ)*base89 + (1075157/78125000000000000000 : ℝ)*base91 + (1075157/78125000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (40773/50000 : ℝ) ≤ (718751308124295434036607564607053/881375000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (130531319/100000000000000 : ℝ)*(upper1) + (174533047/100000000000000 : ℝ)*(upper2) + (17195323/100000000000000 : ℝ)*(lower5) + (371617380101999/25000000000000 : ℝ)*(major0) + (371617380101999/25000000000000 : ℝ)*(major1) + (371617380101999/25000000000000 : ℝ)*(major2) + (36114495929/100000000000000 : ℝ)*(sp1) + (33583367907/50000000000000 : ℝ)*(sp2) + (990047503/25000000000000 : ℝ)*(sp3) + (3152734399/100000000000000 : ℝ)*(sp4) + (218588910002149/10000000000000 : ℝ)*(sp8) + (2185856138259959/100000000000000 : ℝ)*(sp9) + (87433003440803/4000000000000 : ℝ)*(sp10) + (47491242056199/6250000000000 : ℝ)*(sp11) + (189965958272299/25000000000000 : ℝ)*(f.failure) + (136618265797243/6250000000000 : ℝ)*(f.sum) + (55427555088421/35255000000000000000000000000 : ℝ)*base65 + (13112494640695965883/1762750000000000000000000000000000 : ℝ)*base68 + (15923219494704465883/1762750000000000000000000000000000 : ℝ)*base70 + (6646712005103465883/1762750000000000000000000000000000 : ℝ)*base72 + (43190254792321/35255000000000000000000000000 : ℝ)*base73 + (10975772412362965883/1762750000000000000000000000000000 : ℝ)*base76 + (12924657472592215883/1762750000000000000000000000000000 : ℝ)*base78 + (15539362011156465883/1762750000000000000000000000000000 : ℝ)*base80 + (160692108907419/35255000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (4811007/312500000000000000000 : ℝ)*base89 + (4811007/312500000000000000000 : ℝ)*base91 + (4811007/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-90451/100000 : ℝ) ≤ (-398597232116936026079192153590323/440687500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74591789/100000000000000 : ℝ)*(upper1) + (6314831/100000000000000 : ℝ)*(upper3) + (69550167/100000000000000 : ℝ)*(upper5) + (191990903240273/12500000000000 : ℝ)*(major0) + (191990903240273/12500000000000 : ℝ)*(major1) + (191990903240273/12500000000000 : ℝ)*(major2) + (163690359/6250000000000 : ℝ)*(sp4) + (169760219/50000000000000 : ℝ)*(sp5) + (10295490971/50000000000000 : ℝ)*(sp6) + (470931541/6250000000000 : ℝ)*(sp7) + (1158427758415249/50000000000000 : ℝ)*(sp12) + (2316857796355803/100000000000000 : ℝ)*(sp13) + (2316837544894299/100000000000000 : ℝ)*(sp14) + (49071152015147/6250000000000 : ℝ)*(sp15) + (383372054271/48828125000 : ℝ)*(f.failure) + (1158429067938121/50000000000000 : ℝ)*(f.sum) + (14328737798317/17627500000000000000000000000 : ℝ)*base65 + (4374230864106875941/881375000000000000000000000000000 : ℝ)*base68 + (1027682830902125941/881375000000000000000000000000000 : ℝ)*base70 + (2554313427346249059/881375000000000000000000000000000 : ℝ)*base71 + (91312917089619/35255000000000000000000000000 : ℝ)*base73 + (27717394586024750941/881375000000000000000000000000000 : ℝ)*base76 + (2793553042074374059/881375000000000000000000000000000 : ℝ)*base77 + (1800145953737375941/881375000000000000000000000000000 : ℝ)*base80 + (477871560113753/17627500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (7399/4882812500000000000 : ℝ)*base89 + (7399/4882812500000000000 : ℝ)*base91 + (7399/4882812500000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1712_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8539/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10027/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13353/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58449/100000 : ℝ) else (40773/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90451/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1712_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1712_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13353/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58449/100000 : ℝ) else (40773/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90451/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1712_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1712_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1712_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5311/1024 : ℝ) ≤ p) (hpb : p ≤ (5319/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (24452893/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17089/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10017/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(13353/20000 : ℝ) ≤ X j i ∧ X j i ≤ -(58449/100000 : ℝ) else (40773/50000 : ℝ) ≤ X j i ∧ X j i ≤ (90451/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1712_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
