-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1043_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T13:48:35.161682+00:00
-- url     : https://prove2.me/submissions/d383e22d-0b34-482f-8e06-ac7bda248029

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
theorem support_rectangle_w1043_s0_0 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5526455513/10000000000 : ℝ)*x 0 + (-1335647317/5000000000 : ℝ)*x 1 + (1192286177/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5526455513/10000000000 : ℝ)^2059 ≤ (45415700645473/100000000000000 : ℝ)^1547 := by
    have hnat : (5526455513 : ℕ)^2059*100000000000000^1547 ≤ 45415700645473^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526455513 10000000000 45415700645473 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1335647317/5000000000 : ℝ)^2059 ≤ (8628947603497/50000000000000 : ℝ)^1547 := by
    have hnat : (1335647317 : ℕ)^2059*50000000000000^1547 ≤ 8628947603497^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1335647317 5000000000 8628947603497 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1192286177/2500000000 : ℝ)^2059 ≤ (1493056165241/4000000000000 : ℝ)^1547 := by
    have hnat : (1192286177 : ℕ)^2059*4000000000000^1547 ≤ 1493056165241^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1192286177 2500000000 1493056165241 4000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5526455513/10000000000 : ℝ), (-1335647317/5000000000 : ℝ), (1192286177/2500000000 : ℝ)] ![(45415700645473/100000000000000 : ℝ), (8628947603497/50000000000000 : ℝ), (1493056165241/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5526455513/10000000000 : ℝ)|^2059 ≤ (45415700645473/100000000000000 : ℝ)^1547
        have hw : |(5526455513/10000000000 : ℝ)|=(5526455513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1335647317/5000000000 : ℝ)|^2059 ≤ (8628947603497/50000000000000 : ℝ)^1547
        have hw : |(-1335647317/5000000000 : ℝ)|=(1335647317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1192286177/2500000000 : ℝ)|^2059 ≤ (1493056165241/4000000000000 : ℝ)^1547
        have hw : |(1192286177/2500000000 : ℝ)|=(1192286177/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s0_1 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-482247043/2500000000 : ℝ)*x 0 + (4801651517/10000000000 : ℝ)*x 1 + (6042488173/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (482247043/2500000000 : ℝ)^2059 ≤ (11189224381263/100000000000000 : ℝ)^1547 := by
    have hnat : (482247043 : ℕ)^2059*100000000000000^1547 ≤ 11189224381263^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482247043 2500000000 11189224381263 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4801651517/10000000000 : ℝ)^2059 ≤ (37665408163013/100000000000000 : ℝ)^1547 := by
    have hnat : (4801651517 : ℕ)^2059*100000000000000^1547 ≤ 37665408163013^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4801651517 10000000000 37665408163013 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6042488173/10000000000 : ℝ)^2059 ≤ (1278634186033/2500000000000 : ℝ)^1547 := by
    have hnat : (6042488173 : ℕ)^2059*2500000000000^1547 ≤ 1278634186033^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6042488173 10000000000 1278634186033 2500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-482247043/2500000000 : ℝ), (4801651517/10000000000 : ℝ), (6042488173/10000000000 : ℝ)] ![(11189224381263/100000000000000 : ℝ), (37665408163013/100000000000000 : ℝ), (1278634186033/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-482247043/2500000000 : ℝ)|^2059 ≤ (11189224381263/100000000000000 : ℝ)^1547
        have hw : |(-482247043/2500000000 : ℝ)|=(482247043/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4801651517/10000000000 : ℝ)|^2059 ≤ (37665408163013/100000000000000 : ℝ)^1547
        have hw : |(4801651517/10000000000 : ℝ)|=(4801651517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6042488173/10000000000 : ℝ)|^2059 ≤ (1278634186033/2500000000000 : ℝ)^1547
        have hw : |(6042488173/10000000000 : ℝ)|=(6042488173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s0_2 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1291758211/2500000000 : ℝ)*x 0 + (-701712719/5000000000 : ℝ)*x 1 + (15106221/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1291758211/2500000000 : ℝ)^2059 ≤ (20763694804027/50000000000000 : ℝ)^1547 := by
    have hnat : (1291758211 : ℕ)^2059*50000000000000^1547 ≤ 20763694804027^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1291758211 2500000000 20763694804027 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (701712719/5000000000 : ℝ)^2059 ≤ (3663620189119/50000000000000 : ℝ)^1547 := by
    have hnat : (701712719 : ℕ)^2059*50000000000000^1547 ≤ 3663620189119^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      701712719 5000000000 3663620189119 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15106221/25000000 : ℝ)^2059 ≤ (1598292812457/3125000000000 : ℝ)^1547 := by
    have hnat : (15106221 : ℕ)^2059*3125000000000^1547 ≤ 1598292812457^1547*25000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15106221 25000000 1598292812457 3125000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1291758211/2500000000 : ℝ), (-701712719/5000000000 : ℝ), (15106221/25000000 : ℝ)] ![(20763694804027/50000000000000 : ℝ), (3663620189119/50000000000000 : ℝ), (1598292812457/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1291758211/2500000000 : ℝ)|^2059 ≤ (20763694804027/50000000000000 : ℝ)^1547
        have hw : |(1291758211/2500000000 : ℝ)|=(1291758211/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-701712719/5000000000 : ℝ)|^2059 ≤ (3663620189119/50000000000000 : ℝ)^1547
        have hw : |(-701712719/5000000000 : ℝ)|=(701712719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(15106221/25000000 : ℝ)|^2059 ≤ (1598292812457/3125000000000 : ℝ)^1547
        have hw : |(15106221/25000000 : ℝ)|=(15106221/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s0_3 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1033405907/2000000000 : ℝ)*x 0 + (377655721/625000000 : ℝ)*x 1 + (-1403425447/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033405907/2000000000 : ℝ)^2059 ≤ (41527354211893/100000000000000 : ℝ)^1547 := by
    have hnat : (1033405907 : ℕ)^2059*100000000000000^1547 ≤ 41527354211893^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033405907 2000000000 41527354211893 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (377655721/625000000 : ℝ)^2059 ≤ (3196587832983/6250000000000 : ℝ)^1547 := by
    have hnat : (377655721 : ℕ)^2059*6250000000000^1547 ≤ 3196587832983^1547*625000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      377655721 625000000 3196587832983 6250000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1403425447/10000000000 : ℝ)^2059 ≤ (7327240440779/100000000000000 : ℝ)^1547 := by
    have hnat : (1403425447 : ℕ)^2059*100000000000000^1547 ≤ 7327240440779^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1403425447 10000000000 7327240440779 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033405907/2000000000 : ℝ), (377655721/625000000 : ℝ), (-1403425447/10000000000 : ℝ)] ![(41527354211893/100000000000000 : ℝ), (3196587832983/6250000000000 : ℝ), (7327240440779/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033405907/2000000000 : ℝ)|^2059 ≤ (41527354211893/100000000000000 : ℝ)^1547
        have hw : |(1033405907/2000000000 : ℝ)|=(1033405907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(377655721/625000000 : ℝ)|^2059 ≤ (3196587832983/6250000000000 : ℝ)^1547
        have hw : |(377655721/625000000 : ℝ)|=(377655721/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1403425447/10000000000 : ℝ)|^2059 ≤ (7327240440779/100000000000000 : ℝ)^1547
        have hw : |(-1403425447/10000000000 : ℝ)|=(1403425447/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s0_4 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1054934169/2500000000 : ℝ)*x 0 + (112303761/200000000 : ℝ)*x 1 + (3194415063/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054934169/2500000000 : ℝ)^2059 ≤ (15857642124887/50000000000000 : ℝ)^1547 := by
    have hnat : (1054934169 : ℕ)^2059*50000000000000^1547 ≤ 15857642124887^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054934169 2500000000 15857642124887 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112303761/200000000 : ℝ)^2059 ≤ (9277759717301/20000000000000 : ℝ)^1547 := by
    have hnat : (112303761 : ℕ)^2059*20000000000000^1547 ≤ 9277759717301^1547*200000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112303761 200000000 9277759717301 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3194415063/10000000000 : ℝ)^2059 ≤ (875836686251/4000000000000 : ℝ)^1547 := by
    have hnat : (3194415063 : ℕ)^2059*4000000000000^1547 ≤ 875836686251^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3194415063 10000000000 875836686251 4000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054934169/2500000000 : ℝ), (112303761/200000000 : ℝ), (3194415063/10000000000 : ℝ)] ![(15857642124887/50000000000000 : ℝ), (9277759717301/20000000000000 : ℝ), (875836686251/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054934169/2500000000 : ℝ)|^2059 ≤ (15857642124887/50000000000000 : ℝ)^1547
        have hw : |(1054934169/2500000000 : ℝ)|=(1054934169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112303761/200000000 : ℝ)|^2059 ≤ (9277759717301/20000000000000 : ℝ)^1547
        have hw : |(112303761/200000000 : ℝ)|=(112303761/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3194415063/10000000000 : ℝ)|^2059 ≤ (875836686251/4000000000000 : ℝ)^1547
        have hw : |(3194415063/10000000000 : ℝ)|=(3194415063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1043_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (0 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (28199/100000 : ℝ)*pair X 0 0 := by
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
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
  have base43 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*X 2 1) ≤ (0 : ℝ) := by
    linarith only [sign0]
  have base45 : ((-1 : ℝ)*X 1 2+(-1 : ℝ)*X 2 2) ≤ (0 : ℝ) := by
    linarith only [sign1]
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
  have hpowlo : (0 : ℝ) ^ (8235/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8235 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8235*1^2048 ≤ 0^2048*1^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8235/2048 : ℝ) ≤ (627805026084699637/25000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8235 ≤ (627805026084699637/25000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8235*25000000000000000000^2048 ≤ 627805026084699637^2048*5^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 627805026084699637 25000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (627805026084699637/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8235 := by
      have hnat : (1 : ℕ)^2048*1^8235 ≤ 1^8235*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25627805026084699637/25000000000000000000 : ℝ) ≤ (10061872031956309/10000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (25627805026084699637/25000000000000000000 : ℝ)^2048 ≤ (10061872031956309/10000000000000000 : ℝ)^8235 := by
      have hnat : (25627805026084699637 : ℕ)^2048*10000000000000000^8235 ≤ 10061872031956309^8235*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25627805026084699637 25000000000000000000 10061872031956309 10000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10061872031956309/10000000000000000 : ℝ)) (X := (25627805026084699637/25000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (13127805026084699637/12500000000000000000 : ℝ) ≤ (5061872031956309/5000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (13127805026084699637/12500000000000000000 : ℝ)^2048 ≤ (5061872031956309/5000000000000000 : ℝ)^8235 := by
      have hnat : (13127805026084699637 : ℕ)^2048*5000000000000000^8235 ≤ 5061872031956309^8235*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13127805026084699637 12500000000000000000 5061872031956309 5000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5061872031956309/5000000000000000 : ℝ)) (X := (13127805026084699637/12500000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(61872031956309/4000000000000000 : ℝ)*(0 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(61872031956309/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(627805026084699637/25000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(61872031956309/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8235/2048 : ℝ) := by
    rw [show (1 : ℝ)+(61872031956309/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10061872031956309/10000000000000000 : ℝ) by norm_num, show 1+(627805026084699637/25000000000000000000 : ℝ)+(0 : ℝ)=(25627805026084699637/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(627805026084699637/25000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(61872031956309/4000000000000000 : ℝ)*(2/5 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(61872031956309/4000000000000000 : ℝ)*(2/5 : ℝ)=(5061872031956309/5000000000000000 : ℝ) by norm_num, show 1+2*(627805026084699637/25000000000000000000 : ℝ)=(13127805026084699637/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(61872031956309/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61872031956309/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(61872031956309/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61872031956309/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(61872031956309/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (61872031956309/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((5526455513/10000000000 : ℝ)*X 1 0+(-1335647317/5000000000 : ℝ)*X 1 1+(1192286177/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s0_0 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((-482247043/2500000000 : ℝ)*X 0 0+(4801651517/10000000000 : ℝ)*X 0 1+(6042488173/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s0_1 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1291758211/2500000000 : ℝ)*X 1 0+(-701712719/5000000000 : ℝ)*X 1 1+(15106221/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s0_2 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1033405907/2000000000 : ℝ)*X 2 0+(377655721/625000000 : ℝ)*X 2 1+(-1403425447/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s0_3 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((1054934169/2500000000 : ℝ)*X 0 0+(112303761/200000000 : ℝ)*X 0 1+(3194415063/10000000000 : ℝ)*X 0 2+(1054934169/2500000000 : ℝ)*X 1 0+(112303761/200000000 : ℝ)*X 1 1+(3194415063/10000000000 : ℝ)*X 1 2+(1054934169/2500000000 : ℝ)*X 2 0+(112303761/200000000 : ℝ)*X 2 1+(3194415063/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s0_4 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(base43) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (32258738565680483763477/10000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (673358013/100000000000000 : ℝ)*(base19) + (870232131/100000000000000 : ℝ)*(base23) + (607461871/100000000000000 : ℝ)*(base39) + (202320347/100000000000000 : ℝ)*(base45) + (17438327/20000000000000 : ℝ)*(upper2) + (126813573/50000000000000 : ℝ)*(upper5) + (60949606693349/10000000000000 : ℝ)*(major0) + (60949606693349/10000000000000 : ℝ)*(major1) + (30474772973581/5000000000000 : ℝ)*(major2) + (647553723/100000000000000 : ℝ)*(sp0) + (402951025268099/50000000000000 : ℝ)*(sp1) + (402950364812231/50000000000000 : ℝ)*(sp2) + (402950893882969/50000000000000 : ℝ)*(sp3) + (206544684169889/50000000000000 : ℝ)*(sp4) + (206544684169889/50000000000000 : ℝ)*(f.failure) + (805902657998069/100000000000000 : ℝ)*(f.sum) + (194952420553899/40000000000000000000000000000 : ℝ)*base65 + (45626702047471/20000000000000000000000000000 : ℝ)*base68 + (39502638168841/40000000000000000000000000000 : ℝ)*base69 + (51182451827471/20000000000000000000000000000 : ℝ)*base72 + (119979688953899/40000000000000000000000000000 : ℝ)*base73 + (261142540968841/40000000000000000000000000000 : ℝ)*base75 + (156521941431159/40000000000000000000000000000 : ℝ)*base78 + (184925017831159/40000000000000000000000000000 : ℝ)*base80 + (124724094328841/20000000000000000000000000000 : ℝ)*base81 + (2624757/5000000000000000000000 : ℝ)*base89 + (2624757/5000000000000000000000 : ℝ)*base91 + (47375243/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1043_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (28199/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1043_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1043_s1_0 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-533829681/2500000000 : ℝ)*x 0 + (2864402131/5000000000 : ℝ)*x 1 + (1245219047/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (533829681/2500000000 : ℝ)^2059 ≤ (12809718057517/100000000000000 : ℝ)^1547 := by
    have hnat : (533829681 : ℕ)^2059*100000000000000^1547 ≤ 12809718057517^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533829681 2500000000 12809718057517 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2864402131/5000000000 : ℝ)^2059 ≤ (297763934287/625000000000 : ℝ)^1547 := by
    have hnat : (2864402131 : ℕ)^2059*625000000000^1547 ≤ 297763934287^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2864402131 5000000000 297763934287 625000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1245219047/2500000000 : ℝ)^2059 ≤ (39548052443133/100000000000000 : ℝ)^1547 := by
    have hnat : (1245219047 : ℕ)^2059*100000000000000^1547 ≤ 39548052443133^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1245219047 2500000000 39548052443133 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-533829681/2500000000 : ℝ), (2864402131/5000000000 : ℝ), (1245219047/2500000000 : ℝ)] ![(12809718057517/100000000000000 : ℝ), (297763934287/625000000000 : ℝ), (39548052443133/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-533829681/2500000000 : ℝ)|^2059 ≤ (12809718057517/100000000000000 : ℝ)^1547
        have hw : |(-533829681/2500000000 : ℝ)|=(533829681/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2864402131/5000000000 : ℝ)|^2059 ≤ (297763934287/625000000000 : ℝ)^1547
        have hw : |(2864402131/5000000000 : ℝ)|=(2864402131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1245219047/2500000000 : ℝ)|^2059 ≤ (39548052443133/100000000000000 : ℝ)^1547
        have hw : |(1245219047/2500000000 : ℝ)|=(1245219047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s1_1 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5424583041/10000000000 : ℝ)*x 0 + (-2541047691/10000000000 : ℝ)*x 1 + (4980876509/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5424583041/10000000000 : ℝ)^2059 ≤ (44304864745429/100000000000000 : ℝ)^1547 := by
    have hnat : (5424583041 : ℕ)^2059*100000000000000^1547 ≤ 44304864745429^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424583041 10000000000 44304864745429 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2541047691/10000000000 : ℝ)^2059 ≤ (201838492481/1250000000000 : ℝ)^1547 := by
    have hnat : (2541047691 : ℕ)^2059*1250000000000^1547 ≤ 201838492481^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541047691 10000000000 201838492481 1250000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4980876509/10000000000 : ℝ)^2059 ≤ (39548055835403/100000000000000 : ℝ)^1547 := by
    have hnat : (4980876509 : ℕ)^2059*100000000000000^1547 ≤ 39548055835403^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4980876509 10000000000 39548055835403 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5424583041/10000000000 : ℝ), (-2541047691/10000000000 : ℝ), (4980876509/10000000000 : ℝ)] ![(44304864745429/100000000000000 : ℝ), (201838492481/1250000000000 : ℝ), (39548055835403/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5424583041/10000000000 : ℝ)|^2059 ≤ (44304864745429/100000000000000 : ℝ)^1547
        have hw : |(5424583041/10000000000 : ℝ)|=(5424583041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2541047691/10000000000 : ℝ)|^2059 ≤ (201838492481/1250000000000 : ℝ)^1547
        have hw : |(-2541047691/10000000000 : ℝ)|=(2541047691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4980876509/10000000000 : ℝ)|^2059 ≤ (39548055835403/100000000000000 : ℝ)^1547
        have hw : |(4980876509/10000000000 : ℝ)|=(4980876509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s1_2 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2712291717/5000000000 : ℝ)*x 0 + (249043801/500000000 : ℝ)*x 1 + (-2541047797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2712291717/5000000000 : ℝ)^2059 ≤ (44304869017551/100000000000000 : ℝ)^1547 := by
    have hnat : (2712291717 : ℕ)^2059*100000000000000^1547 ≤ 44304869017551^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712291717 5000000000 44304869017551 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (249043801/500000000 : ℝ)^2059 ≤ (39548050667739/100000000000000 : ℝ)^1547 := by
    have hnat : (249043801 : ℕ)^2059*100000000000000^1547 ≤ 39548050667739^1547*500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249043801 500000000 39548050667739 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2541047797/10000000000 : ℝ)^2059 ≤ (3229416058997/20000000000000 : ℝ)^1547 := by
    have hnat : (2541047797 : ℕ)^2059*20000000000000^1547 ≤ 3229416058997^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2541047797 10000000000 3229416058997 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2712291717/5000000000 : ℝ), (249043801/500000000 : ℝ), (-2541047797/10000000000 : ℝ)] ![(44304869017551/100000000000000 : ℝ), (39548050667739/100000000000000 : ℝ), (3229416058997/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2712291717/5000000000 : ℝ)|^2059 ≤ (44304869017551/100000000000000 : ℝ)^1547
        have hw : |(2712291717/5000000000 : ℝ)|=(2712291717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(249043801/500000000 : ℝ)|^2059 ≤ (39548050667739/100000000000000 : ℝ)^1547
        have hw : |(249043801/500000000 : ℝ)|=(249043801/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2541047797/10000000000 : ℝ)|^2059 ≤ (3229416058997/20000000000000 : ℝ)^1547
        have hw : |(-2541047797/10000000000 : ℝ)|=(2541047797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s1_3 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4325702901/10000000000 : ℝ)*x 0 + (1829050877/5000000000 : ℝ)*x 1 + (5117245487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325702901/10000000000 : ℝ)^2059 ≤ (4097461429709/12500000000000 : ℝ)^1547 := by
    have hnat : (4325702901 : ℕ)^2059*12500000000000^1547 ≤ 4097461429709^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325702901 10000000000 4097461429709 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1829050877/5000000000 : ℝ)^2059 ≤ (1639040008907/6250000000000 : ℝ)^1547 := by
    have hnat : (1829050877 : ℕ)^2059*6250000000000^1547 ≤ 1639040008907^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1829050877 5000000000 1639040008907 6250000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5117245487/10000000000 : ℝ)^2059 ≤ (40995668404859/100000000000000 : ℝ)^1547 := by
    have hnat : (5117245487 : ℕ)^2059*100000000000000^1547 ≤ 40995668404859^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5117245487 10000000000 40995668404859 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325702901/10000000000 : ℝ), (1829050877/5000000000 : ℝ), (5117245487/10000000000 : ℝ)] ![(4097461429709/12500000000000 : ℝ), (1639040008907/6250000000000 : ℝ), (40995668404859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325702901/10000000000 : ℝ)|^2059 ≤ (4097461429709/12500000000000 : ℝ)^1547
        have hw : |(4325702901/10000000000 : ℝ)|=(4325702901/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1829050877/5000000000 : ℝ)|^2059 ≤ (1639040008907/6250000000000 : ℝ)^1547
        have hw : |(1829050877/5000000000 : ℝ)|=(1829050877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5117245487/10000000000 : ℝ)|^2059 ≤ (40995668404859/100000000000000 : ℝ)^1547
        have hw : |(5117245487/10000000000 : ℝ)|=(5117245487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s1_4 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2136277431/10000000000 : ℝ)*x 0 + (4991477871/10000000000 : ℝ)*x 1 + (2858991851/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2136277431/10000000000 : ℝ)^2059 ≤ (12817373337101/100000000000000 : ℝ)^1547 := by
    have hnat : (2136277431 : ℕ)^2059*100000000000000^1547 ≤ 12817373337101^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136277431 10000000000 12817373337101 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4991477871/10000000000 : ℝ)^2059 ≤ (39660128559013/100000000000000 : ℝ)^1547 := by
    have hnat : (4991477871 : ℕ)^2059*100000000000000^1547 ≤ 39660128559013^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4991477871 10000000000 39660128559013 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2858991851/5000000000 : ℝ)^2059 ≤ (11880624522823/25000000000000 : ℝ)^1547 := by
    have hnat : (2858991851 : ℕ)^2059*25000000000000^1547 ≤ 11880624522823^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2858991851 5000000000 11880624522823 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2136277431/10000000000 : ℝ), (4991477871/10000000000 : ℝ), (2858991851/5000000000 : ℝ)] ![(12817373337101/100000000000000 : ℝ), (39660128559013/100000000000000 : ℝ), (11880624522823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2136277431/10000000000 : ℝ)|^2059 ≤ (12817373337101/100000000000000 : ℝ)^1547
        have hw : |(-2136277431/10000000000 : ℝ)|=(2136277431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4991477871/10000000000 : ℝ)|^2059 ≤ (39660128559013/100000000000000 : ℝ)^1547
        have hw : |(4991477871/10000000000 : ℝ)|=(4991477871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2858991851/5000000000 : ℝ)|^2059 ≤ (11880624522823/25000000000000 : ℝ)^1547
        have hw : |(2858991851/5000000000 : ℝ)|=(2858991851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s1_5 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2616902807/5000000000 : ℝ)*x 0 + (-1803938911/10000000000 : ℝ)*x 1 + (5717984879/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2616902807/5000000000 : ℝ)^2059 ≤ (42243176800933/100000000000000 : ℝ)^1547 := by
    have hnat : (2616902807 : ℕ)^2059*100000000000000^1547 ≤ 42243176800933^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2616902807 5000000000 42243176800933 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1803938911/10000000000 : ℝ)^2059 ≤ (10234312076119/100000000000000 : ℝ)^1547 := by
    have hnat : (1803938911 : ℕ)^2059*100000000000000^1547 ≤ 10234312076119^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803938911 10000000000 10234312076119 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5717984879/10000000000 : ℝ)^2059 ≤ (2970156944433/6250000000000 : ℝ)^1547 := by
    have hnat : (5717984879 : ℕ)^2059*6250000000000^1547 ≤ 2970156944433^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5717984879 10000000000 2970156944433 6250000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2616902807/5000000000 : ℝ), (-1803938911/10000000000 : ℝ), (5717984879/10000000000 : ℝ)] ![(42243176800933/100000000000000 : ℝ), (10234312076119/100000000000000 : ℝ), (2970156944433/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2616902807/5000000000 : ℝ)|^2059 ≤ (42243176800933/100000000000000 : ℝ)^1547
        have hw : |(2616902807/5000000000 : ℝ)|=(2616902807/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1803938911/10000000000 : ℝ)|^2059 ≤ (10234312076119/100000000000000 : ℝ)^1547
        have hw : |(-1803938911/10000000000 : ℝ)|=(1803938911/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5717984879/10000000000 : ℝ)|^2059 ≤ (2970156944433/6250000000000 : ℝ)^1547
        have hw : |(5717984879/10000000000 : ℝ)|=(5717984879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s1_6 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5233803729/10000000000 : ℝ)*x 0 + (5717986947/10000000000 : ℝ)*x 1 + (-1803938563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5233803729/10000000000 : ℝ)^2059 ≤ (21121578275669/50000000000000 : ℝ)^1547 := by
    have hnat : (5233803729 : ℕ)^2059*50000000000000^1547 ≤ 21121578275669^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5233803729 10000000000 21121578275669 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5717986947/10000000000 : ℝ)^2059 ≤ (47522533986553/100000000000000 : ℝ)^1547 := by
    have hnat : (5717986947 : ℕ)^2059*100000000000000^1547 ≤ 47522533986553^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5717986947 10000000000 47522533986553 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1803938563/10000000000 : ℝ)^2059 ≤ (511715472419/5000000000000 : ℝ)^1547 := by
    have hnat : (1803938563 : ℕ)^2059*5000000000000^1547 ≤ 511715472419^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1803938563 10000000000 511715472419 5000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5233803729/10000000000 : ℝ), (5717986947/10000000000 : ℝ), (-1803938563/10000000000 : ℝ)] ![(21121578275669/50000000000000 : ℝ), (47522533986553/100000000000000 : ℝ), (511715472419/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5233803729/10000000000 : ℝ)|^2059 ≤ (21121578275669/50000000000000 : ℝ)^1547
        have hw : |(5233803729/10000000000 : ℝ)|=(5233803729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5717986947/10000000000 : ℝ)|^2059 ≤ (47522533986553/100000000000000 : ℝ)^1547
        have hw : |(5717986947/10000000000 : ℝ)|=(5717986947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1803938563/10000000000 : ℝ)|^2059 ≤ (511715472419/5000000000000 : ℝ)^1547
        have hw : |(-1803938563/10000000000 : ℝ)|=(1803938563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s1_7 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2163785087/5000000000 : ℝ)*x 0 + (5096559161/10000000000 : ℝ)*x 1 + (3679209203/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163785087/5000000000 : ℝ)^2059 ≤ (1639926294601/5000000000000 : ℝ)^1547 := by
    have hnat : (2163785087 : ℕ)^2059*5000000000000^1547 ≤ 1639926294601^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163785087 5000000000 1639926294601 5000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5096559161/10000000000 : ℝ)^2059 ≤ (40775243717063/100000000000000 : ℝ)^1547 := by
    have hnat : (5096559161 : ℕ)^2059*100000000000000^1547 ≤ 40775243717063^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5096559161 10000000000 40775243717063 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3679209203/10000000000 : ℝ)^2059 ≤ (26426230376269/100000000000000 : ℝ)^1547 := by
    have hnat : (3679209203 : ℕ)^2059*100000000000000^1547 ≤ 26426230376269^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3679209203 10000000000 26426230376269 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163785087/5000000000 : ℝ), (5096559161/10000000000 : ℝ), (3679209203/10000000000 : ℝ)] ![(1639926294601/5000000000000 : ℝ), (40775243717063/100000000000000 : ℝ), (26426230376269/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163785087/5000000000 : ℝ)|^2059 ≤ (1639926294601/5000000000000 : ℝ)^1547
        have hw : |(2163785087/5000000000 : ℝ)|=(2163785087/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5096559161/10000000000 : ℝ)|^2059 ≤ (40775243717063/100000000000000 : ℝ)^1547
        have hw : |(5096559161/10000000000 : ℝ)|=(5096559161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3679209203/10000000000 : ℝ)|^2059 ≤ (26426230376269/100000000000000 : ℝ)^1547
        have hw : |(3679209203/10000000000 : ℝ)|=(3679209203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s1_8 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1933417/2000000000 : ℝ)*x 0 + (2744884401/5000000000 : ℝ)*x 1 + (6379392407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1933417/2000000000 : ℝ)^2059 ≤ (4858580947/50000000000000 : ℝ)^1547 := by
    have hnat : (1933417 : ℕ)^2059*50000000000000^1547 ≤ 4858580947^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933417 2000000000 4858580947 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2744884401/5000000000 : ℝ)^2059 ≤ (22507437225659/50000000000000 : ℝ)^1547 := by
    have hnat : (2744884401 : ℕ)^2059*50000000000000^1547 ≤ 22507437225659^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2744884401 5000000000 22507437225659 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6379392407/10000000000 : ℝ)^2059 ≤ (219901633501/400000000000 : ℝ)^1547 := by
    have hnat : (6379392407 : ℕ)^2059*400000000000^1547 ≤ 219901633501^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6379392407 10000000000 219901633501 400000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1933417/2000000000 : ℝ), (2744884401/5000000000 : ℝ), (6379392407/10000000000 : ℝ)] ![(4858580947/50000000000000 : ℝ), (22507437225659/50000000000000 : ℝ), (219901633501/400000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1933417/2000000000 : ℝ)|^2059 ≤ (4858580947/50000000000000 : ℝ)^1547
        have hw : |(1933417/2000000000 : ℝ)|=(1933417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2744884401/5000000000 : ℝ)|^2059 ≤ (22507437225659/50000000000000 : ℝ)^1547
        have hw : |(2744884401/5000000000 : ℝ)|=(2744884401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6379392407/10000000000 : ℝ)|^2059 ≤ (219901633501/400000000000 : ℝ)^1547
        have hw : |(6379392407/10000000000 : ℝ)|=(6379392407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s1_9 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (959062871/10000000000 : ℝ)*x 0 + (-139813851/312500000 : ℝ)*x 1 + (1730845833/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (959062871/10000000000 : ℝ)^2059 ≤ (4414443628357/100000000000000 : ℝ)^1547 := by
    have hnat : (959062871 : ℕ)^2059*100000000000000^1547 ≤ 4414443628357^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959062871 10000000000 4414443628357 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (139813851/312500000 : ℝ)^2059 ≤ (6856852391641/20000000000000 : ℝ)^1547 := by
    have hnat : (139813851 : ℕ)^2059*20000000000000^1547 ≤ 6856852391641^1547*312500000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      139813851 312500000 6856852391641 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1730845833/2500000000 : ℝ)^2059 ≤ (61301294399253/100000000000000 : ℝ)^1547 := by
    have hnat : (1730845833 : ℕ)^2059*100000000000000^1547 ≤ 61301294399253^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1730845833 2500000000 61301294399253 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(959062871/10000000000 : ℝ), (-139813851/312500000 : ℝ), (1730845833/2500000000 : ℝ)] ![(4414443628357/100000000000000 : ℝ), (6856852391641/20000000000000 : ℝ), (61301294399253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(959062871/10000000000 : ℝ)|^2059 ≤ (4414443628357/100000000000000 : ℝ)^1547
        have hw : |(959062871/10000000000 : ℝ)|=(959062871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-139813851/312500000 : ℝ)|^2059 ≤ (6856852391641/20000000000000 : ℝ)^1547
        have hw : |(-139813851/312500000 : ℝ)|=(139813851/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1730845833/2500000000 : ℝ)|^2059 ≤ (61301294399253/100000000000000 : ℝ)^1547
        have hw : |(1730845833/2500000000 : ℝ)|=(1730845833/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s1_10 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (959057587/10000000000 : ℝ)*x 0 + (692337207/1000000000 : ℝ)*x 1 + (-4474059419/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (959057587/10000000000 : ℝ)^2059 ≤ (882882251453/20000000000000 : ℝ)^1547 := by
    have hnat : (959057587 : ℕ)^2059*20000000000000^1547 ≤ 882882251453^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      959057587 10000000000 882882251453 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (692337207/1000000000 : ℝ)^2059 ≤ (61301161680373/100000000000000 : ℝ)^1547 := by
    have hnat : (692337207 : ℕ)^2059*100000000000000^1547 ≤ 61301161680373^1547*1000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      692337207 1000000000 61301161680373 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4474059419/10000000000 : ℝ)^2059 ≤ (8571106762671/25000000000000 : ℝ)^1547 := by
    have hnat : (4474059419 : ℕ)^2059*25000000000000^1547 ≤ 8571106762671^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4474059419 10000000000 8571106762671 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(959057587/10000000000 : ℝ), (692337207/1000000000 : ℝ), (-4474059419/10000000000 : ℝ)] ![(882882251453/20000000000000 : ℝ), (61301161680373/100000000000000 : ℝ), (8571106762671/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(959057587/10000000000 : ℝ)|^2059 ≤ (882882251453/20000000000000 : ℝ)^1547
        have hw : |(959057587/10000000000 : ℝ)|=(959057587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(692337207/1000000000 : ℝ)|^2059 ≤ (61301161680373/100000000000000 : ℝ)^1547
        have hw : |(692337207/1000000000 : ℝ)|=(692337207/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4474059419/10000000000 : ℝ)|^2059 ≤ (8571106762671/25000000000000 : ℝ)^1547
        have hw : |(-4474059419/10000000000 : ℝ)|=(4474059419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s1_11 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (120496381/625000000 : ℝ)*x 0 + (1459018507/2500000000 : ℝ)*x 1 + (5022225869/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (120496381/625000000 : ℝ)^2059 ≤ (11181149043253/100000000000000 : ℝ)^1547 := by
    have hnat : (120496381 : ℕ)^2059*100000000000000^1547 ≤ 11181149043253^1547*625000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      120496381 625000000 11181149043253 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1459018507/2500000000 : ℝ)^2059 ≤ (9766644666053/20000000000000 : ℝ)^1547 := by
    have hnat : (1459018507 : ℕ)^2059*20000000000000^1547 ≤ 9766644666053^1547*2500000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459018507 2500000000 9766644666053 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5022225869/10000000000 : ℝ)^2059 ≤ (39985627609109/100000000000000 : ℝ)^1547 := by
    have hnat : (5022225869 : ℕ)^2059*100000000000000^1547 ≤ 39985627609109^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5022225869 10000000000 39985627609109 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(120496381/625000000 : ℝ), (1459018507/2500000000 : ℝ), (5022225869/10000000000 : ℝ)] ![(11181149043253/100000000000000 : ℝ), (9766644666053/20000000000000 : ℝ), (39985627609109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(120496381/625000000 : ℝ)|^2059 ≤ (11181149043253/100000000000000 : ℝ)^1547
        have hw : |(120496381/625000000 : ℝ)|=(120496381/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1459018507/2500000000 : ℝ)|^2059 ≤ (9766644666053/20000000000000 : ℝ)^1547
        have hw : |(1459018507/2500000000 : ℝ)|=(1459018507/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5022225869/10000000000 : ℝ)|^2059 ≤ (39985627609109/100000000000000 : ℝ)^1547
        have hw : |(5022225869/10000000000 : ℝ)|=(5022225869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1043_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28199/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (5077/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20901/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (28199/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (28199/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (0 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (28199/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (28199/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (0 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (28199/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (0 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (28199/100000 : ℝ)*(X 0 2+X 1 2) := by
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
  have base59 : ((-1 : ℝ)*X 0 0+(-1 : ℝ)*X 1 0) ≤ (0 : ℝ) := by
    linarith only [sign4]
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
  have hpowlo : (0 : ℝ) ^ (8235/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8235 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8235*1^2048 ≤ 0^2048*1^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (28199/100000 : ℝ) ^ (8235/2048 : ℝ) ≤ (615732227926996183/100000000000000000000 : ℝ) := by
    have hpowers : (28199/100000 : ℝ)^8235 ≤ (615732227926996183/100000000000000000000 : ℝ)^2048 := by
      have hnat : (28199 : ℕ)^8235*100000000000000000000^2048 ≤ 615732227926996183^2048*100000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        28199 100000 615732227926996183 100000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (28199/100000 : ℝ)) (X := (615732227926996183/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8235 := by
      have hnat : (1 : ℕ)^2048*1^8235 ≤ 1^8235*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100615732227926996183/100000000000000000000 : ℝ) ≤ (10015277635528759/10000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (100615732227926996183/100000000000000000000 : ℝ)^2048 ≤ (10015277635528759/10000000000000000 : ℝ)^8235 := by
      have hnat : (100615732227926996183 : ℕ)^2048*10000000000000000^8235 ≤ 10015277635528759^8235*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100615732227926996183 100000000000000000000 10015277635528759 10000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10015277635528759/10000000000000000 : ℝ)) (X := (100615732227926996183/100000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50615732227926996183/50000000000000000000 : ℝ) ≤ (5015277635528759/5000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (50615732227926996183/50000000000000000000 : ℝ)^2048 ≤ (5015277635528759/5000000000000000 : ℝ)^8235 := by
      have hnat : (50615732227926996183 : ℕ)^2048*5000000000000000^8235 ≤ 5015277635528759^8235*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50615732227926996183 50000000000000000000 5015277635528759 5000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5015277635528759/5000000000000000 : ℝ)) (X := (50615732227926996183/50000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(15277635528759/2819900000000000 : ℝ)*(0 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(15277635528759/2819900000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(615732227926996183/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(15277635528759/2819900000000000 : ℝ)*((28199/100000 : ℝ)+(0 : ℝ)))^(8235/2048 : ℝ) := by
    rw [show (1 : ℝ)+(15277635528759/2819900000000000 : ℝ)*((28199/100000 : ℝ)+(0 : ℝ))=(10015277635528759/10000000000000000 : ℝ) by norm_num, show 1+(615732227926996183/100000000000000000000 : ℝ)+(0 : ℝ)=(100615732227926996183/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(615732227926996183/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(15277635528759/2819900000000000 : ℝ)*(28199/100000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(15277635528759/2819900000000000 : ℝ)*(28199/100000 : ℝ)=(5015277635528759/5000000000000000 : ℝ) by norm_num, show 1+2*(615732227926996183/100000000000000000000 : ℝ)=(50615732227926996183/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(15277635528759/2819900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (28199/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (15277635528759/2819900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(15277635528759/2819900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (28199/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (15277635528759/2819900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(15277635528759/2819900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (28199/100000 : ℝ)) (c := (1 : ℝ)) (alpha := (15277635528759/2819900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-533829681/2500000000 : ℝ)*X 0 0+(2864402131/5000000000 : ℝ)*X 0 1+(1245219047/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5424583041/10000000000 : ℝ)*X 1 0+(-2541047691/10000000000 : ℝ)*X 1 1+(4980876509/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2712291717/5000000000 : ℝ)*X 2 0+(249043801/500000000 : ℝ)*X 2 1+(-2541047797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325702901/10000000000 : ℝ)*X 0 0+(1829050877/5000000000 : ℝ)*X 0 1+(5117245487/10000000000 : ℝ)*X 0 2+(4325702901/10000000000 : ℝ)*X 1 0+(1829050877/5000000000 : ℝ)*X 1 1+(5117245487/10000000000 : ℝ)*X 1 2+(4325702901/10000000000 : ℝ)*X 2 0+(1829050877/5000000000 : ℝ)*X 2 1+(5117245487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2136277431/10000000000 : ℝ)*X 0 0+(4991477871/10000000000 : ℝ)*X 0 1+(2858991851/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2616902807/5000000000 : ℝ)*X 1 0+(-1803938911/10000000000 : ℝ)*X 1 1+(5717984879/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5233803729/10000000000 : ℝ)*X 2 0+(5717986947/10000000000 : ℝ)*X 2 1+(-1803938563/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163785087/5000000000 : ℝ)*X 0 0+(5096559161/10000000000 : ℝ)*X 0 1+(3679209203/10000000000 : ℝ)*X 0 2+(2163785087/5000000000 : ℝ)*X 1 0+(5096559161/10000000000 : ℝ)*X 1 1+(3679209203/10000000000 : ℝ)*X 1 2+(2163785087/5000000000 : ℝ)*X 2 0+(5096559161/10000000000 : ℝ)*X 2 1+(3679209203/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((1933417/2000000000 : ℝ)*X 0 0+(2744884401/5000000000 : ℝ)*X 0 1+(6379392407/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s1_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((959062871/10000000000 : ℝ)*X 1 0+(-139813851/312500000 : ℝ)*X 1 1+(1730845833/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s1_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((959057587/10000000000 : ℝ)*X 2 0+(692337207/1000000000 : ℝ)*X 2 1+(-4474059419/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s1_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((120496381/625000000 : ℝ)*X 0 0+(1459018507/2500000000 : ℝ)*X 0 1+(5022225869/10000000000 : ℝ)*X 0 2+(120496381/625000000 : ℝ)*X 1 0+(1459018507/2500000000 : ℝ)*X 1 1+(5022225869/10000000000 : ℝ)*X 1 2+(120496381/625000000 : ℝ)*X 2 0+(1459018507/2500000000 : ℝ)*X 2 1+(5022225869/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s1_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (687711525854614576794003/70497500000000000000000000000 : ℝ) := by norm_num
    linear_combination (505591759337879/50000000000000 : ℝ)*(major0) + (505591759337879/50000000000000 : ℝ)*(major1) + (505591759337879/50000000000000 : ℝ)*(major2) + (668514607380797/50000000000000 : ℝ)*(sp0) + (8356437314701/625000000000 : ℝ)*(sp1) + (1337029336682607/100000000000000 : ℝ)*(sp2) + (342667035721159/50000000000000 : ℝ)*(sp3) + (32139387/2500000000000 : ℝ)*(sp4) + (105259277/12500000000000 : ℝ)*(sp5) + (1381105013/100000000000000 : ℝ)*(sp6) + (926405527/100000000000000 : ℝ)*(sp8) + (9598691/1562500000000 : ℝ)*(sp9) + (35447749/5000000000000 : ℝ)*(sp10) + (606997973/50000000000000 : ℝ)*(sp11) + (85666910679783/12500000000000 : ℝ)*(f.failure) + (6685157133713/500000000000 : ℝ)*(f.sum) + (176348610952287/140995000000000000000000000000 : ℝ)*base65 + (163318127131729/140995000000000000000000000000 : ℝ)*base68 + (261979573944267/70497500000000000000000000000 : ℝ)*base70 + (256255921828271/140995000000000000000000000000 : ℝ)*base71 + (159431009761551/70497500000000000000000000000 : ℝ)*base73 + (692125046338221/140995000000000000000000000000 : ℝ)*base75 + (303802592562853/70497500000000000000000000000 : ℝ)*base77 + (146666581895679/35248750000000000000000000000 : ℝ)*base79 + (8444643356679/17624375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (9601421/1250000000000000000000 : ℝ)*base90 + (9601421/1250000000000000000000 : ℝ)*base92 + (9601421/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (697761087668022928673307/140995000000000000000000000000 : ℝ) := by norm_num
    linear_combination (52968079/50000000000000 : ℝ)*(base59) + (1040997883971809/100000000000000 : ℝ)*(major0) + (1040997883971809/100000000000000 : ℝ)*(major1) + (1040997883971809/100000000000000 : ℝ)*(major2) + (1778606069/100000000000000 : ℝ)*(sp0) + (381089701/20000000000000 : ℝ)*(sp1) + (2203559927/50000000000000 : ℝ)*(sp2) + (1344188405239/97656250000 : ℝ)*(sp4) + (688225655882803/50000000000000 : ℝ)*(sp5) + (1376449057590027/100000000000000 : ℝ)*(sp6) + (352770386281301/50000000000000 : ℝ)*(sp7) + (110365563/4000000000000 : ℝ)*(sp8) + (24749577/10000000000000 : ℝ)*(sp9) + (682854971/50000000000000 : ℝ)*(sp11) + (22048191821017/3125000000000 : ℝ)*(f.failure) + (34411336617747/2500000000000 : ℝ)*(f.sum) + (149345776346973/70497500000000000000000000000 : ℝ)*base65 + (1143688577076851/281990000000000000000000000000 : ℝ)*base67 + (1335556718738761/281990000000000000000000000000 : ℝ)*base69 + (1779469418783421/281990000000000000000000000000 : ℝ)*base71 + (589282872027/17624375000000000000000000000 : ℝ)*base73 + (277235791589339/281990000000000000000000000000 : ℝ)*base76 + (570476723357979/281990000000000000000000000000 : ℝ)*base78 + (535876958679499/281990000000000000000000000000 : ℝ)*base80 + (3794521824393/17624375000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (626821/312500000000000000000 : ℝ)*base89 + (626821/312500000000000000000 : ℝ)*base91 + (626821/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1043_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (28199/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5077/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20901/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1043_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1043_s2_0 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2194051269/10000000000 : ℝ)*x 0 + (2765358277/5000000000 : ℝ)*x 1 + (128543149/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2194051269/10000000000 : ℝ)^2059 ≤ (13280784360767/100000000000000 : ℝ)^1547 := by
    have hnat : (2194051269 : ℕ)^2059*100000000000000^1547 ≤ 13280784360767^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194051269 10000000000 13280784360767 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2765358277/5000000000 : ℝ)^2059 ≤ (9092462502203/20000000000000 : ℝ)^1547 := by
    have hnat : (2765358277 : ℕ)^2059*20000000000000^1547 ≤ 9092462502203^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2765358277 5000000000 9092462502203 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (128543149/250000000 : ℝ)^2059 ≤ (20628451552741/50000000000000 : ℝ)^1547 := by
    have hnat : (128543149 : ℕ)^2059*50000000000000^1547 ≤ 20628451552741^1547*250000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128543149 250000000 20628451552741 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2194051269/10000000000 : ℝ), (2765358277/5000000000 : ℝ), (128543149/250000000 : ℝ)] ![(13280784360767/100000000000000 : ℝ), (9092462502203/20000000000000 : ℝ), (20628451552741/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2194051269/10000000000 : ℝ)|^2059 ≤ (13280784360767/100000000000000 : ℝ)^1547
        have hw : |(-2194051269/10000000000 : ℝ)|=(2194051269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2765358277/5000000000 : ℝ)|^2059 ≤ (9092462502203/20000000000000 : ℝ)^1547
        have hw : |(2765358277/5000000000 : ℝ)|=(2765358277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(128543149/250000000 : ℝ)|^2059 ≤ (20628451552741/50000000000000 : ℝ)^1547
        have hw : |(128543149/250000000 : ℝ)|=(128543149/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s2_1 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5378237377/10000000000 : ℝ)*x 0 + (-2397115019/10000000000 : ℝ)*x 1 + (160678961/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5378237377/10000000000 : ℝ)^2059 ≤ (8760355206723/20000000000000 : ℝ)^1547 := by
    have hnat : (5378237377 : ℕ)^2059*20000000000000^1547 ≤ 8760355206723^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5378237377 10000000000 8760355206723 20000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2397115019/10000000000 : ℝ)^2059 ≤ (3735328094127/25000000000000 : ℝ)^1547 := by
    have hnat : (2397115019 : ℕ)^2059*25000000000000^1547 ≤ 3735328094127^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397115019 10000000000 3735328094127 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (160678961/312500000 : ℝ)^2059 ≤ (41256911563701/100000000000000 : ℝ)^1547 := by
    have hnat : (160678961 : ℕ)^2059*100000000000000^1547 ≤ 41256911563701^1547*312500000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      160678961 312500000 41256911563701 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5378237377/10000000000 : ℝ), (-2397115019/10000000000 : ℝ), (160678961/312500000 : ℝ)] ![(8760355206723/20000000000000 : ℝ), (3735328094127/25000000000000 : ℝ), (41256911563701/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5378237377/10000000000 : ℝ)|^2059 ≤ (8760355206723/20000000000000 : ℝ)^1547
        have hw : |(5378237377/10000000000 : ℝ)|=(5378237377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2397115019/10000000000 : ℝ)|^2059 ≤ (3735328094127/25000000000000 : ℝ)^1547
        have hw : |(-2397115019/10000000000 : ℝ)|=(2397115019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(160678961/312500000 : ℝ)|^2059 ≤ (41256911563701/100000000000000 : ℝ)^1547
        have hw : |(160678961/312500000 : ℝ)|=(160678961/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s2_2 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2689118779/5000000000 : ℝ)*x 0 + (1028345301/2000000000 : ℝ)*x 1 + (-2397115103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689118779/5000000000 : ℝ)^2059 ≤ (43801777995603/100000000000000 : ℝ)^1547 := by
    have hnat : (2689118779 : ℕ)^2059*100000000000000^1547 ≤ 43801777995603^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689118779 5000000000 43801777995603 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028345301/2000000000 : ℝ)^2059 ≤ (41256908925847/100000000000000 : ℝ)^1547 := by
    have hnat : (1028345301 : ℕ)^2059*100000000000000^1547 ≤ 41256908925847^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028345301 2000000000 41256908925847 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2397115103/10000000000 : ℝ)^2059 ≤ (1867664134171/12500000000000 : ℝ)^1547 := by
    have hnat : (2397115103 : ℕ)^2059*12500000000000^1547 ≤ 1867664134171^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2397115103 10000000000 1867664134171 12500000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689118779/5000000000 : ℝ), (1028345301/2000000000 : ℝ), (-2397115103/10000000000 : ℝ)] ![(43801777995603/100000000000000 : ℝ), (41256908925847/100000000000000 : ℝ), (1867664134171/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689118779/5000000000 : ℝ)|^2059 ≤ (43801777995603/100000000000000 : ℝ)^1547
        have hw : |(2689118779/5000000000 : ℝ)|=(2689118779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028345301/2000000000 : ℝ)|^2059 ≤ (41256908925847/100000000000000 : ℝ)^1547
        have hw : |(1028345301/2000000000 : ℝ)|=(1028345301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2397115103/10000000000 : ℝ)|^2059 ≤ (1867664134171/12500000000000 : ℝ)^1547
        have hw : |(-2397115103/10000000000 : ℝ)|=(2397115103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s2_3 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (272856603/625000000 : ℝ)*x 0 + (4002980433/10000000000 : ℝ)*x 1 + (2380933203/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (272856603/625000000 : ℝ)^2059 ≤ (8295942721073/25000000000000 : ℝ)^1547 := by
    have hnat : (272856603 : ℕ)^2059*25000000000000^1547 ≤ 8295942721073^1547*625000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272856603 625000000 8295942721073 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4002980433/10000000000 : ℝ)^2059 ≤ (7391405928429/25000000000000 : ℝ)^1547 := by
    have hnat : (4002980433 : ℕ)^2059*25000000000000^1547 ≤ 7391405928429^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4002980433 10000000000 7391405928429 25000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2380933203/5000000000 : ℝ)^2059 ≤ (37250605383737/100000000000000 : ℝ)^1547 := by
    have hnat : (2380933203 : ℕ)^2059*100000000000000^1547 ≤ 37250605383737^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2380933203 5000000000 37250605383737 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(272856603/625000000 : ℝ), (4002980433/10000000000 : ℝ), (2380933203/5000000000 : ℝ)] ![(8295942721073/25000000000000 : ℝ), (7391405928429/25000000000000 : ℝ), (37250605383737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(272856603/625000000 : ℝ)|^2059 ≤ (8295942721073/25000000000000 : ℝ)^1547
        have hw : |(272856603/625000000 : ℝ)|=(272856603/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4002980433/10000000000 : ℝ)|^2059 ≤ (7391405928429/25000000000000 : ℝ)^1547
        have hw : |(4002980433/10000000000 : ℝ)|=(4002980433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2380933203/5000000000 : ℝ)|^2059 ≤ (37250605383737/100000000000000 : ℝ)^1547
        have hw : |(2380933203/5000000000 : ℝ)|=(2380933203/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s2_4 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2194185259/10000000000 : ℝ)*x 0 + (1028920419/2000000000 : ℝ)*x 1 + (5527809827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2194185259/10000000000 : ℝ)^2059 ≤ (6640931926799/50000000000000 : ℝ)^1547 := by
    have hnat : (2194185259 : ℕ)^2059*50000000000000^1547 ≤ 6640931926799^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2194185259 10000000000 6640931926799 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028920419/2000000000 : ℝ)^2059 ≤ (516095272887/1250000000000 : ℝ)^1547 := by
    have hnat : (1028920419 : ℕ)^2059*1250000000000^1547 ≤ 516095272887^1547*2000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028920419 2000000000 516095272887 1250000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5527809827/10000000000 : ℝ)^2059 ≤ (45430514304759/100000000000000 : ℝ)^1547 := by
    have hnat : (5527809827 : ℕ)^2059*100000000000000^1547 ≤ 45430514304759^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527809827 10000000000 45430514304759 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2194185259/10000000000 : ℝ), (1028920419/2000000000 : ℝ), (5527809827/10000000000 : ℝ)] ![(6640931926799/50000000000000 : ℝ), (516095272887/1250000000000 : ℝ), (45430514304759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2194185259/10000000000 : ℝ)|^2059 ≤ (6640931926799/50000000000000 : ℝ)^1547
        have hw : |(-2194185259/10000000000 : ℝ)|=(2194185259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028920419/2000000000 : ℝ)|^2059 ≤ (516095272887/1250000000000 : ℝ)^1547
        have hw : |(1028920419/2000000000 : ℝ)|=(1028920419/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5527809827/10000000000 : ℝ)|^2059 ≤ (45430514304759/100000000000000 : ℝ)^1547
        have hw : |(5527809827/10000000000 : ℝ)|=(5527809827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s2_5 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5280213007/10000000000 : ℝ)*x 0 + (-1005515997/5000000000 : ℝ)*x 1 + (5527809887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5280213007/10000000000 : ℝ)^2059 ≤ (42742437875559/100000000000000 : ℝ)^1547 := by
    have hnat : (5280213007 : ℕ)^2059*100000000000000^1547 ≤ 42742437875559^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5280213007 10000000000 42742437875559 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1005515997/5000000000 : ℝ)^2059 ≤ (11827047150259/100000000000000 : ℝ)^1547 := by
    have hnat : (1005515997 : ℕ)^2059*100000000000000^1547 ≤ 11827047150259^1547*5000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1005515997 5000000000 11827047150259 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5527809887/10000000000 : ℝ)^2059 ≤ (45430514961073/100000000000000 : ℝ)^1547 := by
    have hnat : (5527809887 : ℕ)^2059*100000000000000^1547 ≤ 45430514961073^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527809887 10000000000 45430514961073 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5280213007/10000000000 : ℝ), (-1005515997/5000000000 : ℝ), (5527809887/10000000000 : ℝ)] ![(42742437875559/100000000000000 : ℝ), (11827047150259/100000000000000 : ℝ), (45430514961073/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5280213007/10000000000 : ℝ)|^2059 ≤ (42742437875559/100000000000000 : ℝ)^1547
        have hw : |(5280213007/10000000000 : ℝ)|=(5280213007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1005515997/5000000000 : ℝ)|^2059 ≤ (11827047150259/100000000000000 : ℝ)^1547
        have hw : |(-1005515997/5000000000 : ℝ)|=(1005515997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5527809887/10000000000 : ℝ)|^2059 ≤ (45430514961073/100000000000000 : ℝ)^1547
        have hw : |(5527809887/10000000000 : ℝ)|=(5527809887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s2_6 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (211208529/400000000 : ℝ)*x 0 + (5527809731/10000000000 : ℝ)*x 1 + (-2011031913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211208529/400000000 : ℝ)^2059 ≤ (21371220112137/50000000000000 : ℝ)^1547 := by
    have hnat : (211208529 : ℕ)^2059*50000000000000^1547 ≤ 21371220112137^1547*400000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211208529 400000000 21371220112137 50000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5527809731/10000000000 : ℝ)^2059 ≤ (177462942401/390625000000 : ℝ)^1547 := by
    have hnat : (5527809731 : ℕ)^2059*390625000000^1547 ≤ 177462942401^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5527809731 10000000000 177462942401 390625000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2011031913/10000000000 : ℝ)^2059 ≤ (11827046516231/100000000000000 : ℝ)^1547 := by
    have hnat : (2011031913 : ℕ)^2059*100000000000000^1547 ≤ 11827046516231^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2011031913 10000000000 11827046516231 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211208529/400000000 : ℝ), (5527809731/10000000000 : ℝ), (-2011031913/10000000000 : ℝ)] ![(21371220112137/50000000000000 : ℝ), (177462942401/390625000000 : ℝ), (11827046516231/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211208529/400000000 : ℝ)|^2059 ≤ (21371220112137/50000000000000 : ℝ)^1547
        have hw : |(211208529/400000000 : ℝ)|=(211208529/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5527809731/10000000000 : ℝ)|^2059 ≤ (177462942401/390625000000 : ℝ)^1547
        have hw : |(5527809731/10000000000 : ℝ)|=(5527809731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2011031913/10000000000 : ℝ)|^2059 ≤ (11827046516231/100000000000000 : ℝ)^1547
        have hw : |(-2011031913/10000000000 : ℝ)|=(2011031913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1043_s2_7 (p : ℝ) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4365967253/10000000000 : ℝ)*x 0 + (297266037/625000000 : ℝ)*x 1 + (4008650287/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4365967253/10000000000 : ℝ)^2059 ≤ (33186417480373/100000000000000 : ℝ)^1547 := by
    have hnat : (4365967253 : ℕ)^2059*100000000000000^1547 ≤ 33186417480373^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4365967253 10000000000 33186417480373 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (297266037/625000000 : ℝ)^2059 ≤ (37192209003583/100000000000000 : ℝ)^1547 := by
    have hnat : (297266037 : ℕ)^2059*100000000000000^1547 ≤ 37192209003583^1547*625000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      297266037 625000000 37192209003583 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4008650287/10000000000 : ℝ)^2059 ≤ (29621373503843/100000000000000 : ℝ)^1547 := by
    have hnat : (4008650287 : ℕ)^2059*100000000000000^1547 ≤ 29621373503843^1547*10000000000^2059 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4008650287 10000000000 29621373503843 100000000000000 2059 1547 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2059/512 : ℝ)) 2059 1547 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4365967253/10000000000 : ℝ), (297266037/625000000 : ℝ), (4008650287/10000000000 : ℝ)] ![(33186417480373/100000000000000 : ℝ), (37192209003583/100000000000000 : ℝ), (29621373503843/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4365967253/10000000000 : ℝ)|^2059 ≤ (33186417480373/100000000000000 : ℝ)^1547
        have hw : |(4365967253/10000000000 : ℝ)|=(4365967253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(297266037/625000000 : ℝ)|^2059 ≤ (37192209003583/100000000000000 : ℝ)^1547
        have hw : |(297266037/625000000 : ℝ)|=(297266037/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4008650287/10000000000 : ℝ)|^2059 ≤ (29621373503843/100000000000000 : ℝ)^1547
        have hw : |(4008650287/10000000000 : ℝ)|=(4008650287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1043_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20901/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5077/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (4299/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (8409/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20901/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5077/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20901/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5077/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20901/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5077/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20901/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5077/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20901/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5077/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20901/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5077/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5077/100000 : ℝ) ^ (8235/2048 : ℝ) ≤ (624096087936273/100000000000000000000 : ℝ) := by
    have hpowers : (5077/100000 : ℝ)^8235 ≤ (624096087936273/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5077 : ℕ)^8235*100000000000000000000^2048 ≤ 624096087936273^2048*100000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5077 100000 624096087936273 100000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5077/100000 : ℝ)) (X := (624096087936273/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20901/100000 : ℝ) ^ (8235/2048 : ℝ) ≤ (46167295448729757/25000000000000000000 : ℝ) := by
    have hpowers : (20901/100000 : ℝ)^8235 ≤ (46167295448729757/25000000000000000000 : ℝ)^2048 := by
      have hnat : (20901 : ℕ)^8235*25000000000000000000^2048 ≤ 46167295448729757^2048*100000^8235 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20901 100000 46167295448729757 25000000000000000000 8235 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20901/100000 : ℝ)) (X := (46167295448729757/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000624096087936273/50000000000000000000 : ℝ) ≤ (10000031041719371/10000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (50000624096087936273/50000000000000000000 : ℝ)^2048 ≤ (10000031041719371/10000000000000000 : ℝ)^8235 := by
      have hnat : (50000624096087936273 : ℕ)^2048*10000000000000000^8235 ≤ 10000031041719371^8235*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000624096087936273 50000000000000000000 10000031041719371 10000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000031041719371/10000000000000000 : ℝ)) (X := (50000624096087936273/50000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100185293277882855301/100000000000000000000 : ℝ) ≤ (62528780872607/62500000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (100185293277882855301/100000000000000000000 : ℝ)^2048 ≤ (62528780872607/62500000000000 : ℝ)^8235 := by
      have hnat : (100185293277882855301 : ℕ)^2048*62500000000000^8235 ≤ 62528780872607^8235*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100185293277882855301 100000000000000000000 62528780872607 62500000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (62528780872607/62500000000000 : ℝ)) (X := (100185293277882855301/100000000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (12546167295448729757/12500000000000000000 : ℝ) ≤ (10009178837514869/10000000000000000 : ℝ) ^ (8235/2048 : ℝ) := by
    have hpowers : (12546167295448729757/12500000000000000000 : ℝ)^2048 ≤ (10009178837514869/10000000000000000 : ℝ)^8235 := by
      have hnat : (12546167295448729757 : ℕ)^2048*10000000000000000^8235 ≤ 10009178837514869^8235*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12546167295448729757 12500000000000000000 10009178837514869 10000000000000000 2048 8235 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009178837514869/10000000000000000 : ℝ)) (X := (12546167295448729757/12500000000000000000 : ℝ)) (by norm_num) 8235 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(624096087936273/100000000000000000000 : ℝ) ≤ ((79097023922456791679/79120000000000000000 : ℝ)+2*(4573897897749/1582400000000000 : ℝ)*(5077/100000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (79097023922456791679/79120000000000000000 : ℝ)+2*(4573897897749/1582400000000000 : ℝ)*(5077/100000 : ℝ)=(10000031041719371/10000000000000000 : ℝ) by norm_num, show 1+2*(624096087936273/100000000000000000000 : ℝ)=(50000624096087936273/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(46167295448729757/25000000000000000000 : ℝ)+(624096087936273/100000000000000000000 : ℝ) ≤ ((79097023922456791679/79120000000000000000 : ℝ)+(4573897897749/1582400000000000 : ℝ)*((20901/100000 : ℝ)+(5077/100000 : ℝ)))^(8235/2048 : ℝ) := by
    rw [show (79097023922456791679/79120000000000000000 : ℝ)+(4573897897749/1582400000000000 : ℝ)*((20901/100000 : ℝ)+(5077/100000 : ℝ))=(62528780872607/62500000000000 : ℝ) by norm_num, show 1+(46167295448729757/25000000000000000000 : ℝ)+(624096087936273/100000000000000000000 : ℝ)=(100185293277882855301/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(46167295448729757/25000000000000000000 : ℝ) ≤ ((79097023922456791679/79120000000000000000 : ℝ)+2*(4573897897749/1582400000000000 : ℝ)*(20901/100000 : ℝ))^(8235/2048 : ℝ) := by
    rw [show (79097023922456791679/79120000000000000000 : ℝ)+2*(4573897897749/1582400000000000 : ℝ)*(20901/100000 : ℝ)=(10009178837514869/10000000000000000 : ℝ) by norm_num, show 1+2*(46167295448729757/25000000000000000000 : ℝ)=(12546167295448729757/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (79097023922456791679/79120000000000000000 : ℝ)*(X 1 0+X 2 0)+(4573897897749/1582400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (5077/100000 : ℝ)) (hi := (20901/100000 : ℝ)) (c := (79097023922456791679/79120000000000000000 : ℝ)) (alpha := (4573897897749/1582400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (79097023922456791679/79120000000000000000 : ℝ)*(X 0 1+X 2 1)+(4573897897749/1582400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (5077/100000 : ℝ)) (hi := (20901/100000 : ℝ)) (c := (79097023922456791679/79120000000000000000 : ℝ)) (alpha := (4573897897749/1582400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (79097023922456791679/79120000000000000000 : ℝ)*(X 0 2+X 1 2)+(4573897897749/1582400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8235/2048 : ℝ)) (lo := (5077/100000 : ℝ)) (hi := (20901/100000 : ℝ)) (c := (79097023922456791679/79120000000000000000 : ℝ)) (alpha := (4573897897749/1582400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2194051269/10000000000 : ℝ)*X 0 0+(2765358277/5000000000 : ℝ)*X 0 1+(128543149/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5378237377/10000000000 : ℝ)*X 1 0+(-2397115019/10000000000 : ℝ)*X 1 1+(160678961/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2689118779/5000000000 : ℝ)*X 2 0+(1028345301/2000000000 : ℝ)*X 2 1+(-2397115103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((272856603/625000000 : ℝ)*X 0 0+(4002980433/10000000000 : ℝ)*X 0 1+(2380933203/5000000000 : ℝ)*X 0 2+(272856603/625000000 : ℝ)*X 1 0+(4002980433/10000000000 : ℝ)*X 1 1+(2380933203/5000000000 : ℝ)*X 1 2+(272856603/625000000 : ℝ)*X 2 0+(4002980433/10000000000 : ℝ)*X 2 1+(2380933203/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2194185259/10000000000 : ℝ)*X 0 0+(1028920419/2000000000 : ℝ)*X 0 1+(5527809827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5280213007/10000000000 : ℝ)*X 1 0+(-1005515997/5000000000 : ℝ)*X 1 1+(5527809887/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((211208529/400000000 : ℝ)*X 2 0+(5527809731/10000000000 : ℝ)*X 2 1+(-2011031913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4365967253/10000000000 : ℝ)*X 0 0+(297266037/625000000 : ℝ)*X 0 1+(4008650287/10000000000 : ℝ)*X 0 2+(4365967253/10000000000 : ℝ)*X 1 0+(297266037/625000000 : ℝ)*X 1 1+(4008650287/10000000000 : ℝ)*X 1 2+(4365967253/10000000000 : ℝ)*X 2 0+(297266037/625000000 : ℝ)*X 2 1+(4008650287/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1043_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5382187389903816954875725641/1978000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (76450959/10000000000000 : ℝ)*(base19) + (40281707/5000000000000 : ℝ)*(base23) + (3427443/2500000000000 : ℝ)*(upper3) + (24413331/100000000000000 : ℝ)*(upper4) + (2947711/4000000000000 : ℝ)*(upper5) + (972127147475231/50000000000000 : ℝ)*(major0) + (972127147475231/50000000000000 : ℝ)*(major1) + (972127147475231/50000000000000 : ℝ)*(major2) + (2570767933567303/100000000000000 : ℝ)*(sp0) + (1285389255934531/50000000000000 : ℝ)*(sp1) + (40168413605383/1562500000000 : ℝ)*(sp2) + (131772474878873/10000000000000 : ℝ)*(sp3) + (11342811349/100000000000000 : ℝ)*(sp4) + (2237016351/50000000000000 : ℝ)*(sp7) + (1317729222821431/100000000000000 : ℝ)*(f.failure) + (642694819094663/25000000000000 : ℝ)*(f.sum) + (323451120955861/39560000000000000000000000000 : ℝ)*base66 + (47469579008465647151/3956000000000000000000000000000000 : ℝ)*base68 + (29227278843161647151/3956000000000000000000000000000000 : ℝ)*base70 + (27178397857989647151/3956000000000000000000000000000000 : ℝ)*base72 + (363219077906741/39560000000000000000000000000 : ℝ)*base74 + (59114598225837647151/3956000000000000000000000000000000 : ℝ)*base76 + (32251775287821647151/3956000000000000000000000000000000 : ℝ)*base78 + (8713756836573647151/3956000000000000000000000000000000 : ℝ)*base80 + (128160505513061/39560000000000000000000000000 : ℝ)*base82 + (9281597/10000000000000000000000 : ℝ)*base90 + (9281597/10000000000000000000000 : ℝ)*base92 + (9281597/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1295099239097700754002632277/123625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1020042671/50000000000000 : ℝ)*(base19) + (459514243/20000000000000 : ℝ)*(base23) + (51085413/20000000000000 : ℝ)*(upper3) + (29329131/50000000000000 : ℝ)*(lower4) + (58671767/25000000000000 : ℝ)*(upper5) + (123348538849521/6250000000000 : ℝ)*(major0) + (123348538849521/6250000000000 : ℝ)*(major1) + (123348538849521/6250000000000 : ℝ)*(major2) + (17420993687/100000000000000 : ℝ)*(sp1) + (19503301359/100000000000000 : ℝ)*(sp2) + (1304775150138921/50000000000000 : ℝ)*(sp4) + (2609530839198813/100000000000000 : ℝ)*(sp5) + (652382124851317/25000000000000 : ℝ)*(sp6) + (668801296852909/50000000000000 : ℝ)*(sp7) + (668801296852909/50000000000000 : ℝ)*(f.failure) + (1304775150138921/50000000000000 : ℝ)*(f.sum) + (20985777826409/4945000000000000000000000000 : ℝ)*base65 + (1575011961690385759/494500000000000000000000000000000 : ℝ)*base67 + (1044746110112614241/494500000000000000000000000000000 : ℝ)*base70 + (412653732120614241/494500000000000000000000000000000 : ℝ)*base72 + (7092540036921/1236250000000000000000000000 : ℝ)*base73 + (4354496630797114241/494500000000000000000000000000000 : ℝ)*base76 + (2849802387994614241/494500000000000000000000000000000 : ℝ)*base78 + (1243936821638114241/494500000000000000000000000000000 : ℝ)*base80 + (5927889898501/1236250000000000000000000000 : ℝ)*base81 + (179983/5000000000000000000000 : ℝ)*base90 + (179983/5000000000000000000000 : ℝ)*base92 + (179983/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1043_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20901/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5077/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4299/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8409/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1043_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1043_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4299/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8409/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1043_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1043_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1043_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8235/2048 : ℝ) ≤ p) (hpb : p ≤ (2059/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (147545813/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4299/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (8409/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1043_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
