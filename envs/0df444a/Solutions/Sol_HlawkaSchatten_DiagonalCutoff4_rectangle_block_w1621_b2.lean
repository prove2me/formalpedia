-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1621_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:58:15.217511+00:00
-- url     : https://prove2.me/submissions/0d178ece-f62f-48e8-b332-67a00cfe15b2

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
theorem support_rectangle_w1621_box_0 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1408118511/10000000000 : ℝ)*x 0 + (676912311/1250000000 : ℝ)*x 1 + (5415298507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1408118511/10000000000 : ℝ)^4803 ≤ (4139186488103/50000000000000 : ℝ)^3779 := by
    have hnat : (1408118511 : ℕ)^4803*50000000000000^3779 ≤ 4139186488103^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1408118511 10000000000 4139186488103 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676912311/1250000000 : ℝ)^4803 ≤ (716575209451/1562500000000 : ℝ)^3779 := by
    have hnat : (676912311 : ℕ)^4803*1562500000000^3779 ≤ 716575209451^3779*1250000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676912311 1250000000 716575209451 1562500000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415298507/10000000000 : ℝ)^4803 ≤ (11465203402343/25000000000000 : ℝ)^3779 := by
    have hnat : (5415298507 : ℕ)^4803*25000000000000^3779 ≤ 11465203402343^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415298507 10000000000 11465203402343 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1408118511/10000000000 : ℝ), (676912311/1250000000 : ℝ), (5415298507/10000000000 : ℝ)] ![(4139186488103/50000000000000 : ℝ), (716575209451/1562500000000 : ℝ), (11465203402343/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1408118511/10000000000 : ℝ)|^4803 ≤ (4139186488103/50000000000000 : ℝ)^3779
        have hw : |(-1408118511/10000000000 : ℝ)|=(1408118511/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676912311/1250000000 : ℝ)|^4803 ≤ (716575209451/1562500000000 : ℝ)^3779
        have hw : |(676912311/1250000000 : ℝ)|=(676912311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415298507/10000000000 : ℝ)|^4803 ≤ (11465203402343/25000000000000 : ℝ)^3779
        have hw : |(5415298507/10000000000 : ℝ)|=(5415298507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_1 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5251243989/10000000000 : ℝ)*x 0 + (-409635821/2500000000 : ℝ)*x 1 + (108305969/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5251243989/10000000000 : ℝ)^4803 ≤ (44102308368619/100000000000000 : ℝ)^3779 := by
    have hnat : (5251243989 : ℕ)^4803*100000000000000^3779 ≤ 44102308368619^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5251243989 10000000000 44102308368619 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (409635821/2500000000 : ℝ)^4803 ≤ (10036878617439/100000000000000 : ℝ)^3779 := by
    have hnat : (409635821 : ℕ)^4803*100000000000000^3779 ≤ 10036878617439^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409635821 2500000000 10036878617439 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (108305969/200000000 : ℝ)^4803 ≤ (917216259917/2000000000000 : ℝ)^3779 := by
    have hnat : (108305969 : ℕ)^4803*2000000000000^3779 ≤ 917216259917^3779*200000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108305969 200000000 917216259917 2000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5251243989/10000000000 : ℝ), (-409635821/2500000000 : ℝ), (108305969/200000000 : ℝ)] ![(44102308368619/100000000000000 : ℝ), (10036878617439/100000000000000 : ℝ), (917216259917/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5251243989/10000000000 : ℝ)|^4803 ≤ (44102308368619/100000000000000 : ℝ)^3779
        have hw : |(5251243989/10000000000 : ℝ)|=(5251243989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-409635821/2500000000 : ℝ)|^4803 ≤ (10036878617439/100000000000000 : ℝ)^3779
        have hw : |(-409635821/2500000000 : ℝ)|=(409635821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(108305969/200000000 : ℝ)|^4803 ≤ (917216259917/2000000000000 : ℝ)^3779
        have hw : |(108305969/200000000 : ℝ)|=(108305969/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_2 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (65640549/125000000 : ℝ)*x 0 + (5415298519/10000000000 : ℝ)*x 1 + (-409635821/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65640549/125000000 : ℝ)^4803 ≤ (44102307632101/100000000000000 : ℝ)^3779 := by
    have hnat : (65640549 : ℕ)^4803*100000000000000^3779 ≤ 44102307632101^3779*125000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65640549 125000000 44102307632101 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5415298519/10000000000 : ℝ)^4803 ≤ (22930406869267/50000000000000 : ℝ)^3779 := by
    have hnat : (5415298519 : ℕ)^4803*50000000000000^3779 ≤ 22930406869267^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415298519 10000000000 22930406869267 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (409635821/2500000000 : ℝ)^4803 ≤ (10036878617439/100000000000000 : ℝ)^3779 := by
    have hnat : (409635821 : ℕ)^4803*100000000000000^3779 ≤ 10036878617439^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      409635821 2500000000 10036878617439 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(65640549/125000000 : ℝ), (5415298519/10000000000 : ℝ), (-409635821/2500000000 : ℝ)] ![(44102307632101/100000000000000 : ℝ), (22930406869267/50000000000000 : ℝ), (10036878617439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(65640549/125000000 : ℝ)|^4803 ≤ (44102307632101/100000000000000 : ℝ)^3779
        have hw : |(65640549/125000000 : ℝ)|=(65640549/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5415298519/10000000000 : ℝ)|^4803 ≤ (22930406869267/50000000000000 : ℝ)^3779
        have hw : |(5415298519/10000000000 : ℝ)|=(5415298519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-409635821/2500000000 : ℝ)|^4803 ≤ (10036878617439/100000000000000 : ℝ)^3779
        have hw : |(-409635821/2500000000 : ℝ)|=(409635821/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_3 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1120626251/2500000000 : ℝ)*x 0 + (15924351/39062500 : ℝ)*x 1 + (407663383/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1120626251/2500000000 : ℝ)^4803 ≤ (1803279190317/5000000000000 : ℝ)^3779 := by
    have hnat : (1120626251 : ℕ)^4803*5000000000000^3779 ≤ 1803279190317^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1120626251 2500000000 1803279190317 5000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15924351/39062500 : ℝ)^4803 ≤ (3196720821653/10000000000000 : ℝ)^3779 := by
    have hnat : (15924351 : ℕ)^4803*10000000000000^3779 ≤ 3196720821653^3779*39062500^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15924351 39062500 3196720821653 10000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (407663383/1000000000 : ℝ)^4803 ≤ (31967207957403/100000000000000 : ℝ)^3779 := by
    have hnat : (407663383 : ℕ)^4803*100000000000000^3779 ≤ 31967207957403^3779*1000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      407663383 1000000000 31967207957403 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1120626251/2500000000 : ℝ), (15924351/39062500 : ℝ), (407663383/1000000000 : ℝ)] ![(1803279190317/5000000000000 : ℝ), (3196720821653/10000000000000 : ℝ), (31967207957403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1120626251/2500000000 : ℝ)|^4803 ≤ (1803279190317/5000000000000 : ℝ)^3779
        have hw : |(1120626251/2500000000 : ℝ)|=(1120626251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15924351/39062500 : ℝ)|^4803 ≤ (3196720821653/10000000000000 : ℝ)^3779
        have hw : |(15924351/39062500 : ℝ)|=(15924351/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(407663383/1000000000 : ℝ)|^4803 ≤ (31967207957403/100000000000000 : ℝ)^3779
        have hw : |(407663383/1000000000 : ℝ)|=(407663383/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_4 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1956574201/10000000000 : ℝ)*x 0 + (5214684507/10000000000 : ℝ)*x 1 + (5214685233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1956574201/10000000000 : ℝ)^4803 ≤ (12575123587387/100000000000000 : ℝ)^3779 := by
    have hnat : (1956574201 : ℕ)^4803*100000000000000^3779 ≤ 12575123587387^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1956574201 10000000000 12575123587387 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5214684507/10000000000 : ℝ)^4803 ≤ (5464054291871/12500000000000 : ℝ)^3779 := by
    have hnat : (5214684507 : ℕ)^4803*12500000000000^3779 ≤ 5464054291871^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214684507 10000000000 5464054291871 12500000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214685233/10000000000 : ℝ)^4803 ≤ (10928110517443/25000000000000 : ℝ)^3779 := by
    have hnat : (5214685233 : ℕ)^4803*25000000000000^3779 ≤ 10928110517443^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214685233 10000000000 10928110517443 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1956574201/10000000000 : ℝ), (5214684507/10000000000 : ℝ), (5214685233/10000000000 : ℝ)] ![(12575123587387/100000000000000 : ℝ), (5464054291871/12500000000000 : ℝ), (10928110517443/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1956574201/10000000000 : ℝ)|^4803 ≤ (12575123587387/100000000000000 : ℝ)^3779
        have hw : |(-1956574201/10000000000 : ℝ)|=(1956574201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5214684507/10000000000 : ℝ)|^4803 ≤ (5464054291871/12500000000000 : ℝ)^3779
        have hw : |(5214684507/10000000000 : ℝ)|=(5214684507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214685233/10000000000 : ℝ)|^4803 ≤ (10928110517443/25000000000000 : ℝ)^3779
        have hw : |(5214685233/10000000000 : ℝ)|=(5214685233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_5 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1077897633/2000000000 : ℝ)*x 0 + (-1723688851/10000000000 : ℝ)*x 1 + (5214685411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1077897633/2000000000 : ℝ)^4803 ≤ (22791591308329/50000000000000 : ℝ)^3779 := by
    have hnat : (1077897633 : ℕ)^4803*50000000000000^3779 ≤ 22791591308329^3779*2000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1077897633 2000000000 22791591308329 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1723688851/10000000000 : ℝ)^4803 ≤ (10704373404129/100000000000000 : ℝ)^3779 := by
    have hnat : (1723688851 : ℕ)^4803*100000000000000^3779 ≤ 10704373404129^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1723688851 10000000000 10704373404129 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5214685411/10000000000 : ℝ)^4803 ≤ (43712443966183/100000000000000 : ℝ)^3779 := by
    have hnat : (5214685411 : ℕ)^4803*100000000000000^3779 ≤ 43712443966183^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5214685411 10000000000 43712443966183 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1077897633/2000000000 : ℝ), (-1723688851/10000000000 : ℝ), (5214685411/10000000000 : ℝ)] ![(22791591308329/50000000000000 : ℝ), (10704373404129/100000000000000 : ℝ), (43712443966183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1077897633/2000000000 : ℝ)|^4803 ≤ (22791591308329/50000000000000 : ℝ)^3779
        have hw : |(1077897633/2000000000 : ℝ)|=(1077897633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1723688851/10000000000 : ℝ)|^4803 ≤ (10704373404129/100000000000000 : ℝ)^3779
        have hw : |(-1723688851/10000000000 : ℝ)|=(1723688851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5214685411/10000000000 : ℝ)|^4803 ≤ (43712443966183/100000000000000 : ℝ)^3779
        have hw : |(5214685411/10000000000 : ℝ)|=(5214685411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_6 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5389488177/10000000000 : ℝ)*x 0 + (130367127/250000000 : ℝ)*x 1 + (-5386529/31250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5389488177/10000000000 : ℝ)^4803 ≤ (22791591372827/50000000000000 : ℝ)^3779 := by
    have hnat : (5389488177 : ℕ)^4803*50000000000000^3779 ≤ 22791591372827^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389488177 10000000000 22791591372827 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (130367127/250000000 : ℝ)^4803 ≤ (4371244043971/10000000000000 : ℝ)^3779 := by
    have hnat : (130367127 : ℕ)^4803*10000000000000^3779 ≤ 4371244043971^3779*250000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130367127 250000000 4371244043971 10000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5386529/31250000 : ℝ)^4803 ≤ (2140875358039/20000000000000 : ℝ)^3779 := by
    have hnat : (5386529 : ℕ)^4803*20000000000000^3779 ≤ 2140875358039^3779*31250000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386529 31250000 2140875358039 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5389488177/10000000000 : ℝ), (130367127/250000000 : ℝ), (-5386529/31250000 : ℝ)] ![(22791591372827/50000000000000 : ℝ), (4371244043971/10000000000000 : ℝ), (2140875358039/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5389488177/10000000000 : ℝ)|^4803 ≤ (22791591372827/50000000000000 : ℝ)^3779
        have hw : |(5389488177/10000000000 : ℝ)|=(5389488177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(130367127/250000000 : ℝ)|^4803 ≤ (4371244043971/10000000000000 : ℝ)^3779
        have hw : |(130367127/250000000 : ℝ)|=(130367127/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-5386529/31250000 : ℝ)|^4803 ≤ (2140875358039/20000000000000 : ℝ)^3779
        have hw : |(-5386529/31250000 : ℝ)|=(5386529/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_7 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3918591997/10000000000 : ℝ)*x 0 + (2179126113/5000000000 : ℝ)*x 1 + (4358252481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3918591997/10000000000 : ℝ)^4803 ≤ (7600112732753/25000000000000 : ℝ)^3779 := by
    have hnat : (3918591997 : ℕ)^4803*25000000000000^3779 ≤ 7600112732753^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3918591997 10000000000 7600112732753 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2179126113/5000000000 : ℝ)^4803 ≤ (695995464613/2000000000000 : ℝ)^3779 := by
    have hnat : (2179126113 : ℕ)^4803*2000000000000^3779 ≤ 695995464613^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179126113 5000000000 695995464613 2000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4358252481/10000000000 : ℝ)^4803 ≤ (6959955163701/20000000000000 : ℝ)^3779 := by
    have hnat : (4358252481 : ℕ)^4803*20000000000000^3779 ≤ 6959955163701^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358252481 10000000000 6959955163701 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3918591997/10000000000 : ℝ), (2179126113/5000000000 : ℝ), (4358252481/10000000000 : ℝ)] ![(7600112732753/25000000000000 : ℝ), (695995464613/2000000000000 : ℝ), (6959955163701/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3918591997/10000000000 : ℝ)|^4803 ≤ (7600112732753/25000000000000 : ℝ)^3779
        have hw : |(3918591997/10000000000 : ℝ)|=(3918591997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2179126113/5000000000 : ℝ)|^4803 ≤ (695995464613/2000000000000 : ℝ)^3779
        have hw : |(2179126113/5000000000 : ℝ)|=(2179126113/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4358252481/10000000000 : ℝ)|^4803 ≤ (6959955163701/20000000000000 : ℝ)^3779
        have hw : |(4358252481/10000000000 : ℝ)|=(4358252481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_8 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1839850143/10000000000 : ℝ)*x 0 + (5071115757/10000000000 : ℝ)*x 1 + (544511083/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1839850143/10000000000 : ℝ)^4803 ≤ (1162946407403/10000000000000 : ℝ)^3779 := by
    have hnat : (1839850143 : ℕ)^4803*10000000000000^3779 ≤ 1162946407403^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1839850143 10000000000 1162946407403 10000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5071115757/10000000000 : ℝ)^4803 ≤ (21094298604233/50000000000000 : ℝ)^3779 := by
    have hnat : (5071115757 : ℕ)^4803*50000000000000^3779 ≤ 21094298604233^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5071115757 10000000000 21094298604233 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (544511083/1000000000 : ℝ)^4803 ≤ (115454846757/250000000000 : ℝ)^3779 := by
    have hnat : (544511083 : ℕ)^4803*250000000000^3779 ≤ 115454846757^3779*1000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      544511083 1000000000 115454846757 250000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1839850143/10000000000 : ℝ), (5071115757/10000000000 : ℝ), (544511083/1000000000 : ℝ)] ![(1162946407403/10000000000000 : ℝ), (21094298604233/50000000000000 : ℝ), (115454846757/250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1839850143/10000000000 : ℝ)|^4803 ≤ (1162946407403/10000000000000 : ℝ)^3779
        have hw : |(-1839850143/10000000000 : ℝ)|=(1839850143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5071115757/10000000000 : ℝ)|^4803 ≤ (21094298604233/50000000000000 : ℝ)^3779
        have hw : |(5071115757/10000000000 : ℝ)|=(5071115757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(544511083/1000000000 : ℝ)|^4803 ≤ (115454846757/250000000000 : ℝ)^3779
        have hw : |(544511083/1000000000 : ℝ)|=(544511083/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_9 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1046139543/2000000000 : ℝ)*x 0 + (-32508749/200000000 : ℝ)*x 1 + (5445110369/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1046139543/2000000000 : ℝ)^4803 ≤ (68567359317/156250000000 : ℝ)^3779 := by
    have hnat : (1046139543 : ℕ)^4803*156250000000^3779 ≤ 68567359317^3779*2000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046139543 2000000000 68567359317 156250000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (32508749/200000000 : ℝ)^4803 ≤ (248373907427/2500000000000 : ℝ)^3779 := by
    have hnat : (32508749 : ℕ)^4803*2500000000000^3779 ≤ 248373907427^3779*200000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32508749 200000000 248373907427 2500000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5445110369/10000000000 : ℝ)^4803 ≤ (23090966866711/50000000000000 : ℝ)^3779 := by
    have hnat : (5445110369 : ℕ)^4803*50000000000000^3779 ≤ 23090966866711^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445110369 10000000000 23090966866711 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1046139543/2000000000 : ℝ), (-32508749/200000000 : ℝ), (5445110369/10000000000 : ℝ)] ![(68567359317/156250000000 : ℝ), (248373907427/2500000000000 : ℝ), (23090966866711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1046139543/2000000000 : ℝ)|^4803 ≤ (68567359317/156250000000 : ℝ)^3779
        have hw : |(1046139543/2000000000 : ℝ)|=(1046139543/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-32508749/200000000 : ℝ)|^4803 ≤ (248373907427/2500000000000 : ℝ)^3779
        have hw : |(-32508749/200000000 : ℝ)|=(32508749/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5445110369/10000000000 : ℝ)|^4803 ≤ (23090966866711/50000000000000 : ℝ)^3779
        have hw : |(5445110369/10000000000 : ℝ)|=(5445110369/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_10 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5230697453/10000000000 : ℝ)*x 0 + (5445110517/10000000000 : ℝ)*x 1 + (-1625437603/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5230697453/10000000000 : ℝ)^4803 ≤ (10970776792303/25000000000000 : ℝ)^3779 := by
    have hnat : (5230697453 : ℕ)^4803*25000000000000^3779 ≤ 10970776792303^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230697453 10000000000 10970776792303 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5445110517/10000000000 : ℝ)^4803 ≤ (46181935328797/100000000000000 : ℝ)^3779 := by
    have hnat : (5445110517 : ℕ)^4803*100000000000000^3779 ≤ 46181935328797^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5445110517 10000000000 46181935328797 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1625437603/10000000000 : ℝ)^4803 ≤ (2483739371411/25000000000000 : ℝ)^3779 := by
    have hnat : (1625437603 : ℕ)^4803*25000000000000^3779 ≤ 2483739371411^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625437603 10000000000 2483739371411 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5230697453/10000000000 : ℝ), (5445110517/10000000000 : ℝ), (-1625437603/10000000000 : ℝ)] ![(10970776792303/25000000000000 : ℝ), (46181935328797/100000000000000 : ℝ), (2483739371411/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5230697453/10000000000 : ℝ)|^4803 ≤ (10970776792303/25000000000000 : ℝ)^3779
        have hw : |(5230697453/10000000000 : ℝ)|=(5230697453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5445110517/10000000000 : ℝ)|^4803 ≤ (46181935328797/100000000000000 : ℝ)^3779
        have hw : |(5445110517/10000000000 : ℝ)|=(5445110517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1625437603/10000000000 : ℝ)|^4803 ≤ (2483739371411/25000000000000 : ℝ)^3779
        have hw : |(-1625437603/10000000000 : ℝ)|=(1625437603/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_11 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4563912889/10000000000 : ℝ)*x 0 + (2017354369/5000000000 : ℝ)*x 1 + (806941701/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4563912889/10000000000 : ℝ)^4803 ≤ (7380020853323/20000000000000 : ℝ)^3779 := by
    have hnat : (4563912889 : ℕ)^4803*20000000000000^3779 ≤ 7380020853323^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4563912889 10000000000 7380020853323 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2017354369/5000000000 : ℝ)^4803 ≤ (6309989804231/20000000000000 : ℝ)^3779 := by
    have hnat : (2017354369 : ℕ)^4803*20000000000000^3779 ≤ 6309989804231^3779*5000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017354369 5000000000 6309989804231 20000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (806941701/2000000000 : ℝ)^4803 ≤ (15774973352739/50000000000000 : ℝ)^3779 := by
    have hnat : (806941701 : ℕ)^4803*50000000000000^3779 ≤ 15774973352739^3779*2000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      806941701 2000000000 15774973352739 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4563912889/10000000000 : ℝ), (2017354369/5000000000 : ℝ), (806941701/2000000000 : ℝ)] ![(7380020853323/20000000000000 : ℝ), (6309989804231/20000000000000 : ℝ), (15774973352739/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4563912889/10000000000 : ℝ)|^4803 ≤ (7380020853323/20000000000000 : ℝ)^3779
        have hw : |(4563912889/10000000000 : ℝ)|=(4563912889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2017354369/5000000000 : ℝ)|^4803 ≤ (6309989804231/20000000000000 : ℝ)^3779
        have hw : |(2017354369/5000000000 : ℝ)|=(2017354369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(806941701/2000000000 : ℝ)|^4803 ≤ (15774973352739/50000000000000 : ℝ)^3779
        have hw : |(806941701/2000000000 : ℝ)|=(806941701/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_12 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-95216191/625000000 : ℝ)*x 0 + (5553134157/10000000000 : ℝ)*x 1 + (5194820731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (95216191/625000000 : ℝ)^4803 ≤ (1143698398789/12500000000000 : ℝ)^3779 := by
    have hnat : (95216191 : ℕ)^4803*12500000000000^3779 ≤ 1143698398789^3779*625000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      95216191 625000000 1143698398789 12500000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5553134157/10000000000 : ℝ)^4803 ≤ (47349497780541/100000000000000 : ℝ)^3779 := by
    have hnat : (5553134157 : ℕ)^4803*100000000000000^3779 ≤ 47349497780541^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5553134157 10000000000 47349497780541 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194820731/10000000000 : ℝ)^4803 ≤ (10875228751887/25000000000000 : ℝ)^3779 := by
    have hnat : (5194820731 : ℕ)^4803*25000000000000^3779 ≤ 10875228751887^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194820731 10000000000 10875228751887 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-95216191/625000000 : ℝ), (5553134157/10000000000 : ℝ), (5194820731/10000000000 : ℝ)] ![(1143698398789/12500000000000 : ℝ), (47349497780541/100000000000000 : ℝ), (10875228751887/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-95216191/625000000 : ℝ)|^4803 ≤ (1143698398789/12500000000000 : ℝ)^3779
        have hw : |(-95216191/625000000 : ℝ)|=(95216191/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5553134157/10000000000 : ℝ)|^4803 ≤ (47349497780541/100000000000000 : ℝ)^3779
        have hw : |(5553134157/10000000000 : ℝ)|=(5553134157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194820731/10000000000 : ℝ)|^4803 ≤ (10875228751887/25000000000000 : ℝ)^3779
        have hw : |(5194820731/10000000000 : ℝ)|=(5194820731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_13 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5403184961/10000000000 : ℝ)*x 0 + (-108238967/625000000 : ℝ)*x 1 + (5194820361/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403184961/10000000000 : ℝ)^4803 ≤ (22865234266831/50000000000000 : ℝ)^3779 := by
    have hnat : (5403184961 : ℕ)^4803*50000000000000^3779 ≤ 22865234266831^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403184961 10000000000 22865234266831 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108238967/625000000 : ℝ)^4803 ≤ (10768620378041/100000000000000 : ℝ)^3779 := by
    have hnat : (108238967 : ℕ)^4803*100000000000000^3779 ≤ 10768620378041^3779*625000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108238967 625000000 10768620378041 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5194820361/10000000000 : ℝ)^4803 ≤ (43500911069643/100000000000000 : ℝ)^3779 := by
    have hnat : (5194820361 : ℕ)^4803*100000000000000^3779 ≤ 43500911069643^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5194820361 10000000000 43500911069643 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403184961/10000000000 : ℝ), (-108238967/625000000 : ℝ), (5194820361/10000000000 : ℝ)] ![(22865234266831/50000000000000 : ℝ), (10768620378041/100000000000000 : ℝ), (43500911069643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403184961/10000000000 : ℝ)|^4803 ≤ (22865234266831/50000000000000 : ℝ)^3779
        have hw : |(5403184961/10000000000 : ℝ)|=(5403184961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-108238967/625000000 : ℝ)|^4803 ≤ (10768620378041/100000000000000 : ℝ)^3779
        have hw : |(-108238967/625000000 : ℝ)|=(108238967/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5194820361/10000000000 : ℝ)|^4803 ≤ (43500911069643/100000000000000 : ℝ)^3779
        have hw : |(5194820361/10000000000 : ℝ)|=(5194820361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_14 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (540318479/1000000000 : ℝ)*x 0 + (1298705107/2500000000 : ℝ)*x 1 + (-1691234/9765625 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (540318479/1000000000 : ℝ)^4803 ≤ (45730466694213/100000000000000 : ℝ)^3779 := by
    have hnat : (540318479 : ℕ)^4803*100000000000000^3779 ≤ 45730466694213^3779*1000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540318479 1000000000 45730466694213 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1298705107/2500000000 : ℝ)^4803 ≤ (43500911782723/100000000000000 : ℝ)^3779 := by
    have hnat : (1298705107 : ℕ)^4803*100000000000000^3779 ≤ 43500911782723^3779*2500000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298705107 2500000000 43500911782723 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1691234/9765625 : ℝ)^4803 ≤ (5384310758037/50000000000000 : ℝ)^3779 := by
    have hnat : (1691234 : ℕ)^4803*50000000000000^3779 ≤ 5384310758037^3779*9765625^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1691234 9765625 5384310758037 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(540318479/1000000000 : ℝ), (1298705107/2500000000 : ℝ), (-1691234/9765625 : ℝ)] ![(45730466694213/100000000000000 : ℝ), (43500911782723/100000000000000 : ℝ), (5384310758037/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(540318479/1000000000 : ℝ)|^4803 ≤ (45730466694213/100000000000000 : ℝ)^3779
        have hw : |(540318479/1000000000 : ℝ)|=(540318479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1298705107/2500000000 : ℝ)|^4803 ≤ (43500911782723/100000000000000 : ℝ)^3779
        have hw : |(1298705107/2500000000 : ℝ)|=(1298705107/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1691234/9765625 : ℝ)|^4803 ≤ (5384310758037/50000000000000 : ℝ)^3779
        have hw : |(-1691234/9765625 : ℝ)|=(1691234/9765625 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1621_box_15 (p : ℝ) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3861128139/10000000000 : ℝ)*x 0 + (175443529/400000000 : ℝ)*x 1 + (4386088737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3861128139/10000000000 : ℝ)^4803 ≤ (29834975642577/100000000000000 : ℝ)^3779 := by
    have hnat : (3861128139 : ℕ)^4803*100000000000000^3779 ≤ 29834975642577^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3861128139 10000000000 29834975642577 100000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (175443529/400000000 : ℝ)^4803 ≤ (17541254784593/50000000000000 : ℝ)^3779 := by
    have hnat : (175443529 : ℕ)^4803*50000000000000^3779 ≤ 17541254784593^3779*400000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175443529 400000000 17541254784593 50000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4386088737/10000000000 : ℝ)^4803 ≤ (8770628693541/25000000000000 : ℝ)^3779 := by
    have hnat : (4386088737 : ℕ)^4803*25000000000000^3779 ≤ 8770628693541^3779*10000000000^4803 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4386088737 10000000000 8770628693541 25000000000000 4803 3779 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4803/1024 : ℝ)) 4803 3779 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3861128139/10000000000 : ℝ), (175443529/400000000 : ℝ), (4386088737/10000000000 : ℝ)] ![(29834975642577/100000000000000 : ℝ), (17541254784593/50000000000000 : ℝ), (8770628693541/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3861128139/10000000000 : ℝ)|^4803 ≤ (29834975642577/100000000000000 : ℝ)^3779
        have hw : |(3861128139/10000000000 : ℝ)|=(3861128139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(175443529/400000000 : ℝ)|^4803 ≤ (17541254784593/50000000000000 : ℝ)^3779
        have hw : |(175443529/400000000 : ℝ)|=(175443529/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4386088737/10000000000 : ℝ)|^4803 ≤ (8770628693541/25000000000000 : ℝ)^3779
        have hw : |(4386088737/10000000000 : ℝ)|=(4386088737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1621_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(16239/25000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58313/100000 : ℝ) ∧ (80651/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (2748/3125 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8161/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5253/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8161/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5253/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8161/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5253/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8161/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5253/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8161/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5253/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8161/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5253/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5253/50000 : ℝ) ^ (4799/1024 : ℝ) ≤ (1296920717278019/50000000000000000000 : ℝ) := by
    have hpowers : (5253/50000 : ℝ)^4799 ≤ (1296920717278019/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5253 : ℕ)^4799*50000000000000000000^1024 ≤ 1296920717278019^1024*50000^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5253 50000 1296920717278019 50000000000000000000 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5253/50000 : ℝ)) (X := (1296920717278019/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8161/50000 : ℝ) ^ (4799/1024 : ℝ) ≤ (10223838220814081/50000000000000000000 : ℝ) := by
    have hpowers : (8161/50000 : ℝ)^4799 ≤ (10223838220814081/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8161 : ℕ)^4799*50000000000000000000^1024 ≤ 10223838220814081^1024*50000^4799 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8161 50000 10223838220814081 50000000000000000000 4799 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8161/50000 : ℝ)) (X := (10223838220814081/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001296920717278019/25000000000000000000 : ℝ) ≤ (5000055345685277/5000000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (25001296920717278019/25000000000000000000 : ℝ)^1024 ≤ (5000055345685277/5000000000000000 : ℝ)^4799 := by
      have hnat : (25001296920717278019 : ℕ)^1024*5000000000000000^4799 ≤ 5000055345685277^4799*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001296920717278019 25000000000000000000 5000055345685277 5000000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000055345685277/5000000000000000 : ℝ)) (X := (25001296920717278019/25000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (500115207589380921/500000000000000000 : ℝ) ≤ (2000098322051883/2000000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (500115207589380921/500000000000000000 : ℝ)^1024 ≤ (2000098322051883/2000000000000000 : ℝ)^4799 := by
      have hnat : (500115207589380921 : ℕ)^1024*2000000000000000^4799 ≤ 2000098322051883^4799*500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500115207589380921 500000000000000000 2000098322051883 2000000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000098322051883/2000000000000000 : ℝ)) (X := (500115207589380921/500000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010223838220814081/25000000000000000000 : ℝ) ≤ (2500218132287069/2500000000000000 : ℝ) ^ (4799/1024 : ℝ) := by
    have hpowers : (25010223838220814081/25000000000000000000 : ℝ)^1024 ≤ (2500218132287069/2500000000000000 : ℝ)^4799 := by
      have hnat : (25010223838220814081 : ℕ)^1024*2500000000000000^4799 ≤ 2500218132287069^4799*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010223838220814081 25000000000000000000 2500218132287069 2500000000000000 1024 4799 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500218132287069/2500000000000000 : ℝ)) (X := (25010223838220814081/25000000000000000000 : ℝ)) (by norm_num) 4799 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1296920717278019/50000000000000000000 : ℝ) ≤ ((14538159978329598683/14540000000000000000 : ℝ)+2*(380918888861/581600000000000 : ℝ)*(5253/50000 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (14538159978329598683/14540000000000000000 : ℝ)+2*(380918888861/581600000000000 : ℝ)*(5253/50000 : ℝ)=(5000055345685277/5000000000000000 : ℝ) by norm_num, show 1+2*(1296920717278019/50000000000000000000 : ℝ)=(25001296920717278019/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10223838220814081/50000000000000000000 : ℝ)+(1296920717278019/50000000000000000000 : ℝ) ≤ ((14538159978329598683/14540000000000000000 : ℝ)+(380918888861/581600000000000 : ℝ)*((8161/50000 : ℝ)+(5253/50000 : ℝ)))^(4799/1024 : ℝ) := by
    rw [show (14538159978329598683/14540000000000000000 : ℝ)+(380918888861/581600000000000 : ℝ)*((8161/50000 : ℝ)+(5253/50000 : ℝ))=(2000098322051883/2000000000000000 : ℝ) by norm_num, show 1+(10223838220814081/50000000000000000000 : ℝ)+(1296920717278019/50000000000000000000 : ℝ)=(500115207589380921/500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10223838220814081/50000000000000000000 : ℝ) ≤ ((14538159978329598683/14540000000000000000 : ℝ)+2*(380918888861/581600000000000 : ℝ)*(8161/50000 : ℝ))^(4799/1024 : ℝ) := by
    rw [show (14538159978329598683/14540000000000000000 : ℝ)+2*(380918888861/581600000000000 : ℝ)*(8161/50000 : ℝ)=(2500218132287069/2500000000000000 : ℝ) by norm_num, show 1+2*(10223838220814081/50000000000000000000 : ℝ)=(25010223838220814081/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14538159978329598683/14540000000000000000 : ℝ)*(X 1 0+X 2 0)+(380918888861/581600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (5253/50000 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (14538159978329598683/14540000000000000000 : ℝ)) (alpha := (380918888861/581600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14538159978329598683/14540000000000000000 : ℝ)*(X 0 1+X 2 1)+(380918888861/581600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (5253/50000 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (14538159978329598683/14540000000000000000 : ℝ)) (alpha := (380918888861/581600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14538159978329598683/14540000000000000000 : ℝ)*(X 0 2+X 1 2)+(380918888861/581600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4799/1024 : ℝ)) (lo := (5253/50000 : ℝ)) (hi := (8161/50000 : ℝ)) (c := (14538159978329598683/14540000000000000000 : ℝ)) (alpha := (380918888861/581600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1408118511/10000000000 : ℝ)*X 0 0+(676912311/1250000000 : ℝ)*X 0 1+(5415298507/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5251243989/10000000000 : ℝ)*X 1 0+(-409635821/2500000000 : ℝ)*X 1 1+(108305969/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((65640549/125000000 : ℝ)*X 2 0+(5415298519/10000000000 : ℝ)*X 2 1+(-409635821/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1120626251/2500000000 : ℝ)*X 0 0+(15924351/39062500 : ℝ)*X 0 1+(407663383/1000000000 : ℝ)*X 0 2+(1120626251/2500000000 : ℝ)*X 1 0+(15924351/39062500 : ℝ)*X 1 1+(407663383/1000000000 : ℝ)*X 1 2+(1120626251/2500000000 : ℝ)*X 2 0+(15924351/39062500 : ℝ)*X 2 1+(407663383/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1956574201/10000000000 : ℝ)*X 0 0+(5214684507/10000000000 : ℝ)*X 0 1+(5214685233/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1077897633/2000000000 : ℝ)*X 1 0+(-1723688851/10000000000 : ℝ)*X 1 1+(5214685411/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5389488177/10000000000 : ℝ)*X 2 0+(130367127/250000000 : ℝ)*X 2 1+(-5386529/31250000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3918591997/10000000000 : ℝ)*X 0 0+(2179126113/5000000000 : ℝ)*X 0 1+(4358252481/10000000000 : ℝ)*X 0 2+(3918591997/10000000000 : ℝ)*X 1 0+(2179126113/5000000000 : ℝ)*X 1 1+(4358252481/10000000000 : ℝ)*X 1 2+(3918591997/10000000000 : ℝ)*X 2 0+(2179126113/5000000000 : ℝ)*X 2 1+(4358252481/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1839850143/10000000000 : ℝ)*X 0 0+(5071115757/10000000000 : ℝ)*X 0 1+(544511083/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1046139543/2000000000 : ℝ)*X 1 0+(-32508749/200000000 : ℝ)*X 1 1+(5445110369/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5230697453/10000000000 : ℝ)*X 2 0+(5445110517/10000000000 : ℝ)*X 2 1+(-1625437603/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4563912889/10000000000 : ℝ)*X 0 0+(2017354369/5000000000 : ℝ)*X 0 1+(806941701/2000000000 : ℝ)*X 0 2+(4563912889/10000000000 : ℝ)*X 1 0+(2017354369/5000000000 : ℝ)*X 1 1+(806941701/2000000000 : ℝ)*X 1 2+(4563912889/10000000000 : ℝ)*X 2 0+(2017354369/5000000000 : ℝ)*X 2 1+(806941701/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-95216191/625000000 : ℝ)*X 0 0+(5553134157/10000000000 : ℝ)*X 0 1+(5194820731/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5403184961/10000000000 : ℝ)*X 1 0+(-108238967/625000000 : ℝ)*X 1 1+(5194820361/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((540318479/1000000000 : ℝ)*X 2 0+(1298705107/2500000000 : ℝ)*X 2 1+(-1691234/9765625 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3861128139/10000000000 : ℝ)*X 0 0+(175443529/400000000 : ℝ)*X 0 1+(4386088737/10000000000 : ℝ)*X 0 2+(3861128139/10000000000 : ℝ)*X 1 0+(175443529/400000000 : ℝ)*X 1 1+(4386088737/10000000000 : ℝ)*X 1 2+(3861128139/10000000000 : ℝ)*X 2 0+(175443529/400000000 : ℝ)*X 2 1+(4386088737/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1621_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-16239/25000 : ℝ) ≤ (-9444240599782163071685364374301/14540000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1053989/1562500000000 : ℝ)*(upper1) + (118492419/100000000000000 : ℝ)*(lower4) + (60081319/100000000000000 : ℝ)*(upper5) + (34064302727617/2000000000000 : ℝ)*(major0) + (34064302727617/2000000000000 : ℝ)*(major1) + (34064302727617/2000000000000 : ℝ)*(major2) + (709978833/25000000000000 : ℝ)*(sp2) + (1614500929/100000000000000 : ℝ)*(sp3) + (2452853117006707/100000000000000 : ℝ)*(sp4) + (490559436323427/20000000000000 : ℝ)*(sp5) + (153303396122423/6250000000000 : ℝ)*(sp6) + (975222650950129/100000000000000 : ℝ)*(sp7) + (4060867393/100000000000000 : ℝ)*(sp12) + (11999251393/20000000000000 : ℝ)*(sp13) + (487612132725529/50000000000000 : ℝ)*(f.failure) + (24528571778741/1000000000000 : ℝ)*(f.sum) + (3521751836873/2908000000000000000000000000 : ℝ)*base65 + (20472107727386589/29080000000000000000000000000000 : ℝ)*base68 + (176754123040786589/29080000000000000000000000000000 : ℝ)*base70 + (150888825031666589/29080000000000000000000000000000 : ℝ)*base72 + (15898182973381/2908000000000000000000000000 : ℝ)*base73 + (225870238271666589/29080000000000000000000000000000 : ℝ)*base76 + (113260954914546589/29080000000000000000000000000000 : ℝ)*base78 + (203267347557226589/29080000000000000000000000000000 : ℝ)*base80 + (1651497509043/2908000000000000000000000000 : ℝ)*base82 + (188603/62500000000000000000 : ℝ)*base89 + (188603/62500000000000000000 : ℝ)*base91 + (188603/62500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58313/100000 : ℝ) ≤ (211976501534940876255949626647769/363500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (3481593/100000000000000 : ℝ)*(lower0) + (32009/800000000000 : ℝ)*(upper1) + (9867653/100000000000000 : ℝ)*(upper2) + (894769148102573/50000000000000 : ℝ)*(major0) + (894769148102573/50000000000000 : ℝ)*(major1) + (894769148102573/50000000000000 : ℝ)*(major2) + (316873371629363/12500000000000 : ℝ)*(sp0) + (1267492174999539/50000000000000 : ℝ)*(sp1) + (1267493466017999/50000000000000 : ℝ)*(sp2) + (1024650804554323/100000000000000 : ℝ)*(sp3) + (9126147/6250000000000 : ℝ)*(sp6) + (241068467/100000000000000 : ℝ)*(sp7) + (2728055271/100000000000000 : ℝ)*(sp9) + (52509723/50000000000000 : ℝ)*(sp12) + (102465104562279/10000000000000 : ℝ)*(f.failure) + (50699741561087/2000000000000 : ℝ)*(f.sum) + (45282904361013/14540000000000000000000000000 : ℝ)*base65 + (3400368471185536359/727000000000000000000000000000000 : ℝ)*base67 + (4290632411876536359/727000000000000000000000000000000 : ℝ)*base69 + (6535134606347536359/727000000000000000000000000000000 : ℝ)*base71 + (29182919853767/14540000000000000000000000000 : ℝ)*base74 + (5895113600261536359/727000000000000000000000000000000 : ℝ)*base75 + (9056945985408536359/727000000000000000000000000000000 : ℝ)*base77 + (3349163717989536359/727000000000000000000000000000000 : ℝ)*base79 + (49184635262147/14540000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (29147/12500000000000000000 : ℝ)*base90 + (29147/12500000000000000000 : ℝ)*base92 + (29147/12500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80651/100000 : ℝ) ≤ (146587159590035894163447868940619/181750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7125279/20000000000000 : ℝ)*(upper1) + (1853649/3125000000000 : ℝ)*(upper2) + (37373643/100000000000000 : ℝ)*(lower5) + (473006912006023/25000000000000 : ℝ)*(major0) + (473006912006023/25000000000000 : ℝ)*(major1) + (473006912006023/25000000000000 : ℝ)*(major2) + (11841579479/100000000000000 : ℝ)*(sp1) + (8533775261/50000000000000 : ℝ)*(sp2) + (7750247917/100000000000000 : ℝ)*(sp3) + (5335322869/100000000000000 : ℝ)*(sp4) + (1336915663850731/50000000000000 : ℝ)*(sp8) + (668456205361213/25000000000000 : ℝ)*(sp9) + (2673819595473809/100000000000000 : ℝ)*(sp10) + (135415811067073/12500000000000 : ℝ)*(sp11) + (1083334238784501/100000000000000 : ℝ)*(f.failure) + (2673836663024331/100000000000000 : ℝ)*(f.sum) + (50300692102627/7270000000000000000000000000 : ℝ)*base66 + (2468794895440442709/363500000000000000000000000000000 : ℝ)*base67 + (1241171897309442709/363500000000000000000000000000000 : ℝ)*base69 + (2214945944871442709/363500000000000000000000000000000 : ℝ)*base71 + (34808150523357/7270000000000000000000000000 : ℝ)*base74 + (2199775558445942709/363500000000000000000000000000000 : ℝ)*base75 + (1745878345390442709/363500000000000000000000000000000 : ℝ)*base77 + (3060936812011442709/363500000000000000000000000000000 : ℝ)*base79 + (31745099213047/7270000000000000000000000000 : ℝ)*base82 + (624607/125000000000000000000 : ℝ)*base89 + (624607/125000000000000000000 : ℝ)*base91 + (624607/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-2748/3125 : ℝ) ≤ (-25571119325384637984294300537/29080000000000000000000000000 : ℝ) := by norm_num
    linear_combination (6213533/25000000000000 : ℝ)*(upper3) + (37845113/50000000000000 : ℝ)*(lower4) + (14497183/25000000000000 : ℝ)*(upper5) + (1934638644368413/100000000000000 : ℝ)*(major0) + (1934638644368413/100000000000000 : ℝ)*(major1) + (1934638644368413/100000000000000 : ℝ)*(major2) + (16840291/625000000000 : ℝ)*(sp4) + (67187444299/100000000000000 : ℝ)*(sp5) + (43803478203/50000000000000 : ℝ)*(sp6) + (37787612459/100000000000000 : ℝ)*(sp7) + (697713362576511/25000000000000 : ℝ)*(sp12) + (174424309831769/6250000000000 : ℝ)*(sp13) + (1395384268898099/50000000000000 : ℝ)*(sp14) + (138461823622207/12500000000000 : ℝ)*(sp15) + (221546475318023/20000000000000 : ℝ)*(f.failure) + (697714036188151/25000000000000 : ℝ)*(f.sum) + (38020614657953/29080000000000000000000000000 : ℝ)*base65 + (1899721711433425079/1454000000000000000000000000000000 : ℝ)*base67 + (2615972677651425079/1454000000000000000000000000000000 : ℝ)*base69 + (334614121137425079/1454000000000000000000000000000000 : ℝ)*base71 + (217501135442833/29080000000000000000000000000 : ℝ)*base73 + (1075083368354574921/1454000000000000000000000000000000 : ℝ)*base76 + (6898167554424574921/1454000000000000000000000000000000 : ℝ)*base78 + (9206460120350574921/1454000000000000000000000000000000 : ℝ)*base80 + (135079132932353/29080000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (12539/25000000000000000000 : ℝ)*base90 + (12539/25000000000000000000 : ℝ)*base92 + (12539/25000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1621_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16239/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58313/100000 : ℝ) else (80651/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2748/3125 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1621_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1621_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16239/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58313/100000 : ℝ) else (80651/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2748/3125 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1621_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4799/1024 : ℝ) ≤ p) (hpb : p ≤ (4803/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (2183107/1250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8161/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5253/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(16239/25000 : ℝ) ≤ X j i ∧ X j i ≤ -(58313/100000 : ℝ) else (80651/100000 : ℝ) ≤ X j i ∧ X j i ≤ (2748/3125 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1621_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
