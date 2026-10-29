-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1348_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:06:42.072529+00:00
-- url     : https://prove2.me/submissions/883a905f-c2b6-46b7-b931-46269a2bdada

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
theorem support_rectangle_w1348_s6_0 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2038792811/10000000000 : ℝ)*x 0 + (2706205473/5000000000 : ℝ)*x 1 + (1048956263/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2038792811/10000000000 : ℝ)^1077 ≤ (12417248183647/100000000000000 : ℝ)^821 := by
    have hnat : (2038792811 : ℕ)^1077*100000000000000^821 ≤ 12417248183647^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038792811 10000000000 12417248183647 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706205473/5000000000 : ℝ)^1077 ≤ (44694907417929/100000000000000 : ℝ)^821 := by
    have hnat : (2706205473 : ℕ)^1077*100000000000000^821 ≤ 44694907417929^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706205473 5000000000 44694907417929 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048956263/2000000000 : ℝ)^1077 ≤ (42887844382507/100000000000000 : ℝ)^821 := by
    have hnat : (1048956263 : ℕ)^1077*100000000000000^821 ≤ 42887844382507^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048956263 2000000000 42887844382507 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2038792811/10000000000 : ℝ), (2706205473/5000000000 : ℝ), (1048956263/2000000000 : ℝ)] ![(12417248183647/100000000000000 : ℝ), (44694907417929/100000000000000 : ℝ), (42887844382507/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2038792811/10000000000 : ℝ)|^1077 ≤ (12417248183647/100000000000000 : ℝ)^821
        have hw : |(-2038792811/10000000000 : ℝ)|=(2038792811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706205473/5000000000 : ℝ)|^1077 ≤ (44694907417929/100000000000000 : ℝ)^821
        have hw : |(2706205473/5000000000 : ℝ)|=(2706205473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048956263/2000000000 : ℝ)|^1077 ≤ (42887844382507/100000000000000 : ℝ)^821
        have hw : |(1048956263/2000000000 : ℝ)|=(1048956263/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s6_1 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (534889823/1000000000 : ℝ)*x 0 + (-2124196737/10000000000 : ℝ)*x 1 + (1048956261/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534889823/1000000000 : ℝ)^1077 ≤ (11002037610883/25000000000000 : ℝ)^821 := by
    have hnat : (534889823 : ℕ)^1077*25000000000000^821 ≤ 11002037610883^821*1000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534889823 1000000000 11002037610883 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124196737/10000000000 : ℝ)^1077 ≤ (2620801051479/20000000000000 : ℝ)^821 := by
    have hnat : (2124196737 : ℕ)^1077*20000000000000^821 ≤ 2620801051479^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124196737 10000000000 2620801051479 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1048956261/2000000000 : ℝ)^1077 ≤ (42887844275237/100000000000000 : ℝ)^821 := by
    have hnat : (1048956261 : ℕ)^1077*100000000000000^821 ≤ 42887844275237^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048956261 2000000000 42887844275237 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534889823/1000000000 : ℝ), (-2124196737/10000000000 : ℝ), (1048956261/2000000000 : ℝ)] ![(11002037610883/25000000000000 : ℝ), (2620801051479/20000000000000 : ℝ), (42887844275237/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534889823/1000000000 : ℝ)|^1077 ≤ (11002037610883/25000000000000 : ℝ)^821
        have hw : |(534889823/1000000000 : ℝ)|=(534889823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2124196737/10000000000 : ℝ)|^1077 ≤ (2620801051479/20000000000000 : ℝ)^821
        have hw : |(-2124196737/10000000000 : ℝ)|=(2124196737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1048956261/2000000000 : ℝ)|^1077 ≤ (42887844275237/100000000000000 : ℝ)^821
        have hw : |(1048956261/2000000000 : ℝ)|=(1048956261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s6_2 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2674449091/5000000000 : ℝ)*x 0 + (1311195331/2500000000 : ℝ)*x 1 + (-2124196777/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2674449091/5000000000 : ℝ)^1077 ≤ (44008149925469/100000000000000 : ℝ)^821 := by
    have hnat : (2674449091 : ℕ)^1077*100000000000000^821 ≤ 44008149925469^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2674449091 5000000000 44008149925469 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311195331/2500000000 : ℝ)^1077 ≤ (857756889581/2000000000000 : ℝ)^821 := by
    have hnat : (1311195331 : ℕ)^1077*2000000000000^821 ≤ 857756889581^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311195331 2500000000 857756889581 2000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124196777/10000000000 : ℝ)^1077 ≤ (6552002790547/50000000000000 : ℝ)^821 := by
    have hnat : (2124196777 : ℕ)^1077*50000000000000^821 ≤ 6552002790547^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124196777 10000000000 6552002790547 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2674449091/5000000000 : ℝ), (1311195331/2500000000 : ℝ), (-2124196777/10000000000 : ℝ)] ![(44008149925469/100000000000000 : ℝ), (857756889581/2000000000000 : ℝ), (6552002790547/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2674449091/5000000000 : ℝ)|^1077 ≤ (44008149925469/100000000000000 : ℝ)^821
        have hw : |(2674449091/5000000000 : ℝ)|=(2674449091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311195331/2500000000 : ℝ)|^1077 ≤ (857756889581/2000000000000 : ℝ)^821
        have hw : |(1311195331/2500000000 : ℝ)|=(1311195331/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2124196777/10000000000 : ℝ)|^1077 ≤ (6552002790547/50000000000000 : ℝ)^821
        have hw : |(-2124196777/10000000000 : ℝ)|=(2124196777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s6_3 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1081262869/2500000000 : ℝ)*x 0 + (1038108749/2500000000 : ℝ)*x 1 + (4504340211/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081262869/2500000000 : ℝ)^1077 ≤ (8325838100461/25000000000000 : ℝ)^821 := by
    have hnat : (1081262869 : ℕ)^1077*25000000000000^821 ≤ 8325838100461^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081262869 2500000000 8325838100461 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1038108749/2500000000 : ℝ)^1077 ≤ (15785342202929/50000000000000 : ℝ)^821 := by
    have hnat : (1038108749 : ℕ)^1077*50000000000000^821 ≤ 15785342202929^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038108749 2500000000 15785342202929 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504340211/10000000000 : ℝ)^1077 ≤ (8781490793707/25000000000000 : ℝ)^821 := by
    have hnat : (4504340211 : ℕ)^1077*25000000000000^821 ≤ 8781490793707^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504340211 10000000000 8781490793707 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081262869/2500000000 : ℝ), (1038108749/2500000000 : ℝ), (4504340211/10000000000 : ℝ)] ![(8325838100461/25000000000000 : ℝ), (15785342202929/50000000000000 : ℝ), (8781490793707/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081262869/2500000000 : ℝ)|^1077 ≤ (8325838100461/25000000000000 : ℝ)^821
        have hw : |(1081262869/2500000000 : ℝ)|=(1081262869/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1038108749/2500000000 : ℝ)|^1077 ≤ (15785342202929/50000000000000 : ℝ)^821
        have hw : |(1038108749/2500000000 : ℝ)|=(1038108749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504340211/10000000000 : ℝ)|^1077 ≤ (8781490793707/25000000000000 : ℝ)^821
        have hw : |(4504340211/10000000000 : ℝ)|=(4504340211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s6_4 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2038804953/10000000000 : ℝ)*x 0 + (5245381847/10000000000 : ℝ)*x 1 + (5411807301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2038804953/10000000000 : ℝ)^1077 ≤ (1241734519341/10000000000000 : ℝ)^821 := by
    have hnat : (2038804953 : ℕ)^1077*10000000000000^821 ≤ 1241734519341^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038804953 10000000000 1241734519341 10000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245381847/10000000000 : ℝ)^1077 ≤ (10723571605143/25000000000000 : ℝ)^821 := by
    have hnat : (5245381847 : ℕ)^1077*25000000000000^821 ≤ 10723571605143^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245381847 10000000000 10723571605143 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411807301/10000000000 : ℝ)^1077 ≤ (44688368379641/100000000000000 : ℝ)^821 := by
    have hnat : (5411807301 : ℕ)^1077*100000000000000^821 ≤ 44688368379641^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411807301 10000000000 44688368379641 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2038804953/10000000000 : ℝ), (5245381847/10000000000 : ℝ), (5411807301/10000000000 : ℝ)] ![(1241734519341/10000000000000 : ℝ), (10723571605143/25000000000000 : ℝ), (44688368379641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2038804953/10000000000 : ℝ)|^1077 ≤ (1241734519341/10000000000000 : ℝ)^821
        have hw : |(-2038804953/10000000000 : ℝ)|=(2038804953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245381847/10000000000 : ℝ)|^1077 ≤ (10723571605143/25000000000000 : ℝ)^821
        have hw : |(5245381847/10000000000 : ℝ)|=(5245381847/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411807301/10000000000 : ℝ)|^1077 ≤ (44688368379641/100000000000000 : ℝ)^821
        have hw : |(5411807301/10000000000 : ℝ)|=(5411807301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s6_5 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (212227633/400000000 : ℝ)*x 0 + (-1957170761/10000000000 : ℝ)*x 1 + (2705903651/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212227633/400000000 : ℝ)^1077 ≤ (43542402225477/100000000000000 : ℝ)^821 := by
    have hnat : (212227633 : ℕ)^1077*100000000000000^821 ≤ 43542402225477^821*400000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212227633 400000000 43542402225477 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1957170761/10000000000 : ℝ)^1077 ≤ (5884614690383/50000000000000 : ℝ)^821 := by
    have hnat : (1957170761 : ℕ)^1077*50000000000000^821 ≤ 5884614690383^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957170761 10000000000 5884614690383 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2705903651/5000000000 : ℝ)^1077 ≤ (44688368390473/100000000000000 : ℝ)^821 := by
    have hnat : (2705903651 : ℕ)^1077*100000000000000^821 ≤ 44688368390473^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705903651 5000000000 44688368390473 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212227633/400000000 : ℝ), (-1957170761/10000000000 : ℝ), (2705903651/5000000000 : ℝ)] ![(43542402225477/100000000000000 : ℝ), (5884614690383/50000000000000 : ℝ), (44688368390473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212227633/400000000 : ℝ)|^1077 ≤ (43542402225477/100000000000000 : ℝ)^821
        have hw : |(212227633/400000000 : ℝ)|=(212227633/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1957170761/10000000000 : ℝ)|^1077 ≤ (5884614690383/50000000000000 : ℝ)^821
        have hw : |(-1957170761/10000000000 : ℝ)|=(1957170761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2705903651/5000000000 : ℝ)|^1077 ≤ (44688368390473/100000000000000 : ℝ)^821
        have hw : |(2705903651/5000000000 : ℝ)|=(2705903651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s6_6 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (82901419/156250000 : ℝ)*x 0 + (1082361463/2000000000 : ℝ)*x 1 + (-391434151/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82901419/156250000 : ℝ)^1077 ≤ (8708480425717/20000000000000 : ℝ)^821 := by
    have hnat : (82901419 : ℕ)^1077*20000000000000^821 ≤ 8708480425717^821*156250000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82901419 156250000 8708480425717 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082361463/2000000000 : ℝ)^1077 ≤ (22344184265647/50000000000000 : ℝ)^821 := by
    have hnat : (1082361463 : ℕ)^1077*50000000000000^821 ≤ 22344184265647^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082361463 2000000000 22344184265647 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (391434151/2000000000 : ℝ)^1077 ≤ (2353845866687/20000000000000 : ℝ)^821 := by
    have hnat : (391434151 : ℕ)^1077*20000000000000^821 ≤ 2353845866687^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391434151 2000000000 2353845866687 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(82901419/156250000 : ℝ), (1082361463/2000000000 : ℝ), (-391434151/2000000000 : ℝ)] ![(8708480425717/20000000000000 : ℝ), (22344184265647/50000000000000 : ℝ), (2353845866687/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(82901419/156250000 : ℝ)|^1077 ≤ (8708480425717/20000000000000 : ℝ)^821
        have hw : |(82901419/156250000 : ℝ)|=(82901419/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082361463/2000000000 : ℝ)|^1077 ≤ (22344184265647/50000000000000 : ℝ)^821
        have hw : |(1082361463/2000000000 : ℝ)|=(1082361463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-391434151/2000000000 : ℝ)|^1077 ≤ (2353845866687/20000000000000 : ℝ)^821
        have hw : |(-391434151/2000000000 : ℝ)|=(391434151/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s6_7 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (865015397/2000000000 : ℝ)*x 0 + (70360617/156250000 : ℝ)*x 1 + (830740431/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865015397/2000000000 : ℝ)^1077 ≤ (6660722014273/20000000000000 : ℝ)^821 := by
    have hnat : (865015397 : ℕ)^1077*20000000000000^821 ≤ 6660722014273^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865015397 2000000000 6660722014273 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (70360617/156250000 : ℝ)^1077 ≤ (35113066720463/100000000000000 : ℝ)^821 := by
    have hnat : (70360617 : ℕ)^1077*100000000000000^821 ≤ 35113066720463^821*156250000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70360617 156250000 35113066720463 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830740431/2000000000 : ℝ)^1077 ≤ (15791661597573/50000000000000 : ℝ)^821 := by
    have hnat : (830740431 : ℕ)^1077*50000000000000^821 ≤ 15791661597573^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830740431 2000000000 15791661597573 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865015397/2000000000 : ℝ), (70360617/156250000 : ℝ), (830740431/2000000000 : ℝ)] ![(6660722014273/20000000000000 : ℝ), (35113066720463/100000000000000 : ℝ), (15791661597573/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865015397/2000000000 : ℝ)|^1077 ≤ (6660722014273/20000000000000 : ℝ)^821
        have hw : |(865015397/2000000000 : ℝ)|=(865015397/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(70360617/156250000 : ℝ)|^1077 ≤ (35113066720463/100000000000000 : ℝ)^821
        have hw : |(70360617/156250000 : ℝ)|=(70360617/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830740431/2000000000 : ℝ)|^1077 ≤ (15791661597573/50000000000000 : ℝ)^821
        have hw : |(830740431/2000000000 : ℝ)|=(830740431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1348_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11163/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14711/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2789/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14719/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2789/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2789/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14719/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2789/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2789/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14719/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2789/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2789/25000 : ℝ) ^ (4307/1024 : ℝ) ≤ (1971508622454173/20000000000000000000 : ℝ) := by
    have hpowers : (2789/25000 : ℝ)^4307 ≤ (1971508622454173/20000000000000000000 : ℝ)^1024 := by
      have hnat : (2789 : ℕ)^4307*20000000000000000000^1024 ≤ 1971508622454173^1024*25000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2789 25000 1971508622454173 20000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2789/25000 : ℝ)) (X := (1971508622454173/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14719/100000 : ℝ) ^ (4307/1024 : ℝ) ≤ (31626464519726587/100000000000000000000 : ℝ) := by
    have hpowers : (14719/100000 : ℝ)^4307 ≤ (31626464519726587/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14719 : ℕ)^4307*100000000000000000000^1024 ≤ 31626464519726587^1024*100000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14719 100000 31626464519726587 100000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14719/100000 : ℝ)) (X := (31626464519726587/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001971508622454173/10000000000000000000 : ℝ) ≤ (100004686958799/100000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (10001971508622454173/10000000000000000000 : ℝ)^1024 ≤ (100004686958799/100000000000000 : ℝ)^4307 := by
      have hnat : (10001971508622454173 : ℕ)^1024*100000000000000^4307 ≤ 100004686958799^4307*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001971508622454173 10000000000000000000 100004686958799 100000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (100004686958799/100000000000000 : ℝ)) (X := (10001971508622454173/10000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010371001907999363/25000000000000000000 : ℝ) ≤ (2500246534183847/2500000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (25010371001907999363/25000000000000000000 : ℝ)^1024 ≤ (2500246534183847/2500000000000000 : ℝ)^4307 := by
      have hnat : (25010371001907999363 : ℕ)^1024*2500000000000000^4307 ≤ 2500246534183847^4307*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010371001907999363 25000000000000000000 2500246534183847 2500000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500246534183847/2500000000000000 : ℝ)) (X := (25010371001907999363/25000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031626464519726587/50000000000000000000 : ℝ) ≤ (2500375894397719/2500000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50031626464519726587/50000000000000000000 : ℝ)^1024 ≤ (2500375894397719/2500000000000000 : ℝ)^4307 := by
      have hnat : (50031626464519726587 : ℕ)^1024*2500000000000000^4307 ≤ 2500375894397719^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031626464519726587 50000000000000000000 2500375894397719 2500000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500375894397719/2500000000000000 : ℝ)) (X := (50031626464519726587/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1971508622454173/20000000000000000000 : ℝ) ≤ ((8905031205763108861/8907500000000000000 : ℝ)+2*(8085013367/5567187500000 : ℝ)*(2789/25000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (8905031205763108861/8907500000000000000 : ℝ)+2*(8085013367/5567187500000 : ℝ)*(2789/25000 : ℝ)=(100004686958799/100000000000000 : ℝ) by norm_num, show 1+2*(1971508622454173/20000000000000000000 : ℝ)=(10001971508622454173/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31626464519726587/100000000000000000000 : ℝ)+(1971508622454173/20000000000000000000 : ℝ) ≤ ((8905031205763108861/8907500000000000000 : ℝ)+(8085013367/5567187500000 : ℝ)*((14719/100000 : ℝ)+(2789/25000 : ℝ)))^(4307/1024 : ℝ) := by
    rw [show (8905031205763108861/8907500000000000000 : ℝ)+(8085013367/5567187500000 : ℝ)*((14719/100000 : ℝ)+(2789/25000 : ℝ))=(2500246534183847/2500000000000000 : ℝ) by norm_num, show 1+(31626464519726587/100000000000000000000 : ℝ)+(1971508622454173/20000000000000000000 : ℝ)=(25010371001907999363/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31626464519726587/100000000000000000000 : ℝ) ≤ ((8905031205763108861/8907500000000000000 : ℝ)+2*(8085013367/5567187500000 : ℝ)*(14719/100000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (8905031205763108861/8907500000000000000 : ℝ)+2*(8085013367/5567187500000 : ℝ)*(14719/100000 : ℝ)=(2500375894397719/2500000000000000 : ℝ) by norm_num, show 1+2*(31626464519726587/100000000000000000000 : ℝ)=(50031626464519726587/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8905031205763108861/8907500000000000000 : ℝ)*(X 1 0+X 2 0)+(8085013367/5567187500000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (8905031205763108861/8907500000000000000 : ℝ)) (alpha := (8085013367/5567187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8905031205763108861/8907500000000000000 : ℝ)*(X 0 1+X 2 1)+(8085013367/5567187500000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (8905031205763108861/8907500000000000000 : ℝ)) (alpha := (8085013367/5567187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8905031205763108861/8907500000000000000 : ℝ)*(X 0 2+X 1 2)+(8085013367/5567187500000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (2789/25000 : ℝ)) (hi := (14719/100000 : ℝ)) (c := (8905031205763108861/8907500000000000000 : ℝ)) (alpha := (8085013367/5567187500000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2038792811/10000000000 : ℝ)*X 0 0+(2706205473/5000000000 : ℝ)*X 0 1+(1048956263/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534889823/1000000000 : ℝ)*X 1 0+(-2124196737/10000000000 : ℝ)*X 1 1+(1048956261/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2674449091/5000000000 : ℝ)*X 2 0+(1311195331/2500000000 : ℝ)*X 2 1+(-2124196777/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1081262869/2500000000 : ℝ)*X 0 0+(1038108749/2500000000 : ℝ)*X 0 1+(4504340211/10000000000 : ℝ)*X 0 2+(1081262869/2500000000 : ℝ)*X 1 0+(1038108749/2500000000 : ℝ)*X 1 1+(4504340211/10000000000 : ℝ)*X 1 2+(1081262869/2500000000 : ℝ)*X 2 0+(1038108749/2500000000 : ℝ)*X 2 1+(4504340211/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2038804953/10000000000 : ℝ)*X 0 0+(5245381847/10000000000 : ℝ)*X 0 1+(5411807301/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212227633/400000000 : ℝ)*X 1 0+(-1957170761/10000000000 : ℝ)*X 1 1+(2705903651/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((82901419/156250000 : ℝ)*X 2 0+(1082361463/2000000000 : ℝ)*X 2 1+(-391434151/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((865015397/2000000000 : ℝ)*X 0 0+(70360617/156250000 : ℝ)*X 0 1+(830740431/2000000000 : ℝ)*X 0 2+(865015397/2000000000 : ℝ)*X 1 0+(70360617/156250000 : ℝ)*X 1 1+(830740431/2000000000 : ℝ)*X 1 2+(865015397/2000000000 : ℝ)*X 2 0+(70360617/156250000 : ℝ)*X 2 1+(830740431/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (91450801833994846569102603/31812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (48947193/10000000000000 : ℝ)*(base19) + (104975457/25000000000000 : ℝ)*(base23) + (20159817/100000000000000 : ℝ)*(lower2) + (34844161/50000000000000 : ℝ)*(upper3) + (2316427/20000000000000 : ℝ)*(lower4) + (2201809739328913/50000000000000 : ℝ)*(major0) + (2201809739328913/50000000000000 : ℝ)*(major1) + (2201809739328913/50000000000000 : ℝ)*(major2) + (5965544628363153/100000000000000 : ℝ)*(sp0) + (1193110708931399/20000000000000 : ℝ)*(sp1) + (5965553614227097/100000000000000 : ℝ)*(sp2) + (2841679094130979/100000000000000 : ℝ)*(sp3) + (9405765771/100000000000000 : ℝ)*(sp4) + (1433308257/25000000000000 : ℝ)*(sp7) + (2841684827364007/100000000000000 : ℝ)*(f.failure) + (238622161365157/4000000000000 : ℝ)*(f.sum) + (3636855073687/1272500000000000000000000000 : ℝ)*base65 + (558022982233753299/63625000000000000000000000000000 : ℝ)*base67 + (1009089260625253299/63625000000000000000000000000000 : ℝ)*base69 + (148803170603621701/63625000000000000000000000000000 : ℝ)*base72 + (1788047408599/2545000000000000000000000000 : ℝ)*base73 + (46385862077628299/63625000000000000000000000000000 : ℝ)*base75 + (273878392008121701/63625000000000000000000000000000 : ℝ)*base78 + (854343398686628299/63625000000000000000000000000000 : ℝ)*base79 + (4020980734071/636250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (34879637/10000000000000000000000 : ℝ)*base89 + (34879637/10000000000000000000000 : ℝ)*base91 + (34879637/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51378543007889893023732723/15906250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (279067607/50000000000000 : ℝ)*(base19) + (8015351/1250000000000 : ℝ)*(base23) + (33167763/50000000000000 : ℝ)*(upper3) + (19880027/50000000000000 : ℝ)*(lower4) + (25023239/50000000000000 : ℝ)*(upper5) + (2217732435399817/50000000000000 : ℝ)*(major0) + (2217732435399817/50000000000000 : ℝ)*(major1) + (2217732435399817/50000000000000 : ℝ)*(major2) + (1424542719/12500000000000 : ℝ)*(sp1) + (13649272501/100000000000000 : ℝ)*(sp2) + (751086845501673/12500000000000 : ℝ)*(sp4) + (6008682809536417/100000000000000 : ℝ)*(sp5) + (6008680473512803/100000000000000 : ℝ)*(sp6) + (286223486991637/10000000000000 : ℝ)*(sp7) + (286223486991637/10000000000000 : ℝ)*(f.failure) + (751086845501673/12500000000000 : ℝ)*(f.sum) + (1251262769677/1272500000000000000000000000 : ℝ)*base66 + (233778767137125491/63625000000000000000000000000000 : ℝ)*base67 + (593615692754624509/63625000000000000000000000000000 : ℝ)*base70 + (408086688005749509/63625000000000000000000000000000 : ℝ)*base72 + (7510017275601/2545000000000000000000000000 : ℝ)*base73 + (558185902178374509/63625000000000000000000000000000 : ℝ)*base76 + (435371470443874509/63625000000000000000000000000000 : ℝ)*base78 + (857675342323999509/63625000000000000000000000000000 : ℝ)*base80 + (59709761303/79531250000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (3943967/1000000000000000000000 : ℝ)*base89 + (3943967/1000000000000000000000 : ℝ)*base91 + (3943967/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1348_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1348_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1348_s7_0 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-2038801397/10000000000 : ℝ)*x 0 + (5412348221/10000000000 : ℝ)*x 1 + (655604783/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2038801397/10000000000 : ℝ)^1077 ≤ (6208658391181/50000000000000 : ℝ)^821 := by
    have hnat : (2038801397 : ℕ)^1077*50000000000000^821 ≤ 6208658391181^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2038801397 10000000000 6208658391181 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5412348221/10000000000 : ℝ)^1077 ≤ (22347113966593/50000000000000 : ℝ)^821 := by
    have hnat : (5412348221 : ℕ)^1077*50000000000000^821 ≤ 22347113966593^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412348221 10000000000 22347113966593 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655604783/1250000000 : ℝ)^1077 ≤ (42888455277011/100000000000000 : ℝ)^821 := by
    have hnat : (655604783 : ℕ)^1077*100000000000000^821 ≤ 42888455277011^821*1250000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655604783 1250000000 42888455277011 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2038801397/10000000000 : ℝ), (5412348221/10000000000 : ℝ), (655604783/1250000000 : ℝ)] ![(6208658391181/50000000000000 : ℝ), (22347113966593/50000000000000 : ℝ), (42888455277011/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2038801397/10000000000 : ℝ)|^1077 ≤ (6208658391181/50000000000000 : ℝ)^821
        have hw : |(-2038801397/10000000000 : ℝ)|=(2038801397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5412348221/10000000000 : ℝ)|^1077 ≤ (22347113966593/50000000000000 : ℝ)^821
        have hw : |(5412348221/10000000000 : ℝ)|=(5412348221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655604783/1250000000 : ℝ)|^1077 ≤ (42888455277011/100000000000000 : ℝ)^821
        have hw : |(655604783/1250000000 : ℝ)|=(655604783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s7_1 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348881737/10000000000 : ℝ)*x 0 + (-424828647/2000000000 : ℝ)*x 1 + (5244838261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348881737/10000000000 : ℝ)^1077 ≤ (44007972435017/100000000000000 : ℝ)^821 := by
    have hnat : (5348881737 : ℕ)^1077*100000000000000^821 ≤ 44007972435017^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348881737 10000000000 44007972435017 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (424828647/2000000000 : ℝ)^1077 ≤ (6551786147499/50000000000000 : ℝ)^821 := by
    have hnat : (424828647 : ℕ)^1077*50000000000000^821 ≤ 6551786147499^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424828647 2000000000 6551786147499 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244838261/10000000000 : ℝ)^1077 ≤ (42888455244829/100000000000000 : ℝ)^821 := by
    have hnat : (5244838261 : ℕ)^1077*100000000000000^821 ≤ 42888455244829^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244838261 10000000000 42888455244829 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348881737/10000000000 : ℝ), (-424828647/2000000000 : ℝ), (5244838261/10000000000 : ℝ)] ![(44007972435017/100000000000000 : ℝ), (6551786147499/50000000000000 : ℝ), (42888455244829/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348881737/10000000000 : ℝ)|^1077 ≤ (44007972435017/100000000000000 : ℝ)^821
        have hw : |(5348881737/10000000000 : ℝ)|=(5348881737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-424828647/2000000000 : ℝ)|^1077 ≤ (6551786147499/50000000000000 : ℝ)^821
        have hw : |(-424828647/2000000000 : ℝ)|=(424828647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244838261/10000000000 : ℝ)|^1077 ≤ (42888455244829/100000000000000 : ℝ)^821
        have hw : |(5244838261/10000000000 : ℝ)|=(5244838261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s7_2 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5348881779/10000000000 : ℝ)*x 0 + (5244838211/10000000000 : ℝ)*x 1 + (-2124143247/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348881779/10000000000 : ℝ)^1077 ≤ (44007972888321/100000000000000 : ℝ)^821 := by
    have hnat : (5348881779 : ℕ)^1077*100000000000000^821 ≤ 44007972888321^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348881779 10000000000 44007972888321 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244838211/10000000000 : ℝ)^1077 ≤ (10722113677119/25000000000000 : ℝ)^821 := by
    have hnat : (5244838211 : ℕ)^1077*25000000000000^821 ≤ 10722113677119^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244838211 10000000000 10722113677119 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124143247/10000000000 : ℝ)^1077 ≤ (13103572392107/100000000000000 : ℝ)^821 := by
    have hnat : (2124143247 : ℕ)^1077*100000000000000^821 ≤ 13103572392107^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124143247 10000000000 13103572392107 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348881779/10000000000 : ℝ), (5244838211/10000000000 : ℝ), (-2124143247/10000000000 : ℝ)] ![(44007972888321/100000000000000 : ℝ), (10722113677119/25000000000000 : ℝ), (13103572392107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348881779/10000000000 : ℝ)|^1077 ≤ (44007972888321/100000000000000 : ℝ)^821
        have hw : |(5348881779/10000000000 : ℝ)|=(5348881779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244838211/10000000000 : ℝ)|^1077 ≤ (10722113677119/25000000000000 : ℝ)^821
        have hw : |(5244838211/10000000000 : ℝ)|=(5244838211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2124143247/10000000000 : ℝ)|^1077 ≤ (13103572392107/100000000000000 : ℝ)^821
        have hw : |(-2124143247/10000000000 : ℝ)|=(2124143247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s7_3 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4325055737/10000000000 : ℝ)*x 0 + (4152560139/10000000000 : ℝ)*x 1 + (2252106997/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325055737/10000000000 : ℝ)^1077 ≤ (8325848860673/25000000000000 : ℝ)^821 := by
    have hnat : (4325055737 : ℕ)^1077*25000000000000^821 ≤ 8325848860673^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325055737 10000000000 8325848860673 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4152560139/10000000000 : ℝ)^1077 ≤ (7892983135747/25000000000000 : ℝ)^821 := by
    have hnat : (4152560139 : ℕ)^1077*25000000000000^821 ≤ 7892983135747^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152560139 10000000000 7892983135747 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252106997/5000000000 : ℝ)^1077 ≤ (35124671998489/100000000000000 : ℝ)^821 := by
    have hnat : (2252106997 : ℕ)^1077*100000000000000^821 ≤ 35124671998489^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252106997 5000000000 35124671998489 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325055737/10000000000 : ℝ), (4152560139/10000000000 : ℝ), (2252106997/5000000000 : ℝ)] ![(8325848860673/25000000000000 : ℝ), (7892983135747/25000000000000 : ℝ), (35124671998489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325055737/10000000000 : ℝ)|^1077 ≤ (8325848860673/25000000000000 : ℝ)^821
        have hw : |(4325055737/10000000000 : ℝ)|=(4325055737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4152560139/10000000000 : ℝ)|^1077 ≤ (7892983135747/25000000000000 : ℝ)^821
        have hw : |(4152560139/10000000000 : ℝ)|=(4152560139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252106997/5000000000 : ℝ)|^1077 ≤ (35124671998489/100000000000000 : ℝ)^821
        have hw : |(2252106997/5000000000 : ℝ)|=(2252106997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s7_4 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1019406717/5000000000 : ℝ)*x 0 + (5245437969/10000000000 : ℝ)*x 1 + (5411745467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1019406717/5000000000 : ℝ)^1077 ≤ (12417412953343/100000000000000 : ℝ)^821 := by
    have hnat : (1019406717 : ℕ)^1077*100000000000000^821 ≤ 12417412953343^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1019406717 5000000000 12417412953343 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245437969/10000000000 : ℝ)^1077 ≤ (42894888465287/100000000000000 : ℝ)^821 := by
    have hnat : (5245437969 : ℕ)^1077*100000000000000^821 ≤ 42894888465287^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245437969 10000000000 42894888465287 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5411745467/10000000000 : ℝ)^1077 ≤ (44687698570163/100000000000000 : ℝ)^821 := by
    have hnat : (5411745467 : ℕ)^1077*100000000000000^821 ≤ 44687698570163^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5411745467 10000000000 44687698570163 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1019406717/5000000000 : ℝ), (5245437969/10000000000 : ℝ), (5411745467/10000000000 : ℝ)] ![(12417412953343/100000000000000 : ℝ), (42894888465287/100000000000000 : ℝ), (44687698570163/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1019406717/5000000000 : ℝ)|^1077 ≤ (12417412953343/100000000000000 : ℝ)^821
        have hw : |(-1019406717/5000000000 : ℝ)|=(1019406717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245437969/10000000000 : ℝ)|^1077 ≤ (42894888465287/100000000000000 : ℝ)^821
        have hw : |(5245437969/10000000000 : ℝ)|=(5245437969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5411745467/10000000000 : ℝ)|^1077 ≤ (44687698570163/100000000000000 : ℝ)^821
        have hw : |(5411745467/10000000000 : ℝ)|=(5411745467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s7_5 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (530570511/1000000000 : ℝ)*x 0 + (-489309031/2500000000 : ℝ)*x 1 + (169117047/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530570511/1000000000 : ℝ)^1077 ≤ (43542556013821/100000000000000 : ℝ)^821 := by
    have hnat : (530570511 : ℕ)^1077*100000000000000^821 ≤ 43542556013821^821*1000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530570511 1000000000 43542556013821 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489309031/2500000000 : ℝ)^1077 ≤ (5884872498209/50000000000000 : ℝ)^821 := by
    have hnat : (489309031 : ℕ)^1077*50000000000000^821 ≤ 5884872498209^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489309031 2500000000 5884872498209 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169117047/312500000 : ℝ)^1077 ≤ (558596237137/1250000000000 : ℝ)^821 := by
    have hnat : (169117047 : ℕ)^1077*1250000000000^821 ≤ 558596237137^821*312500000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169117047 312500000 558596237137 1250000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530570511/1000000000 : ℝ), (-489309031/2500000000 : ℝ), (169117047/312500000 : ℝ)] ![(43542556013821/100000000000000 : ℝ), (5884872498209/50000000000000 : ℝ), (558596237137/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530570511/1000000000 : ℝ)|^1077 ≤ (43542556013821/100000000000000 : ℝ)^821
        have hw : |(530570511/1000000000 : ℝ)|=(530570511/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-489309031/2500000000 : ℝ)|^1077 ≤ (5884872498209/50000000000000 : ℝ)^821
        have hw : |(-489309031/2500000000 : ℝ)|=(489309031/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169117047/312500000 : ℝ)|^1077 ≤ (558596237137/1250000000000 : ℝ)^821
        have hw : |(169117047/312500000 : ℝ)|=(169117047/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s7_6 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5305705101/10000000000 : ℝ)*x 0 + (1352936387/2500000000 : ℝ)*x 1 + (-1957236077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305705101/10000000000 : ℝ)^1077 ≤ (43542555916929/100000000000000 : ℝ)^821 := by
    have hnat : (5305705101 : ℕ)^1077*100000000000000^821 ≤ 43542555916929^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305705101 10000000000 43542555916929 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1352936387/2500000000 : ℝ)^1077 ≤ (1396490607737/3125000000000 : ℝ)^821 := by
    have hnat : (1352936387 : ℕ)^1077*3125000000000^821 ≤ 1396490607737^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1352936387 2500000000 1396490607737 3125000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1957236077/10000000000 : ℝ)^1077 ≤ (11769744625657/100000000000000 : ℝ)^821 := by
    have hnat : (1957236077 : ℕ)^1077*100000000000000^821 ≤ 11769744625657^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1957236077 10000000000 11769744625657 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305705101/10000000000 : ℝ), (1352936387/2500000000 : ℝ), (-1957236077/10000000000 : ℝ)] ![(43542555916929/100000000000000 : ℝ), (1396490607737/3125000000000 : ℝ), (11769744625657/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305705101/10000000000 : ℝ)|^1077 ≤ (43542555916929/100000000000000 : ℝ)^821
        have hw : |(5305705101/10000000000 : ℝ)|=(5305705101/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1352936387/2500000000 : ℝ)|^1077 ≤ (1396490607737/3125000000000 : ℝ)^821
        have hw : |(1352936387/2500000000 : ℝ)|=(1352936387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1957236077/10000000000 : ℝ)|^1077 ≤ (11769744625657/100000000000000 : ℝ)^821
        have hw : |(-1957236077/10000000000 : ℝ)|=(1957236077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_s7_7 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4325081157/10000000000 : ℝ)*x 0 + (4502955113/10000000000 : ℝ)*x 1 + (166153019/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4325081157/10000000000 : ℝ)^1077 ≤ (8325913053323/25000000000000 : ℝ)^821 := by
    have hnat : (4325081157 : ℕ)^1077*25000000000000^821 ≤ 8325913053323^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4325081157 10000000000 8325913053323 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502955113/10000000000 : ℝ)^1077 ≤ (35111794498413/100000000000000 : ℝ)^821 := by
    have hnat : (4502955113 : ℕ)^1077*100000000000000^821 ≤ 35111794498413^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502955113 10000000000 35111794498413 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166153019/400000000 : ℝ)^1077 ≤ (31584553267181/100000000000000 : ℝ)^821 := by
    have hnat : (166153019 : ℕ)^1077*100000000000000^821 ≤ 31584553267181^821*400000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166153019 400000000 31584553267181 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4325081157/10000000000 : ℝ), (4502955113/10000000000 : ℝ), (166153019/400000000 : ℝ)] ![(8325913053323/25000000000000 : ℝ), (35111794498413/100000000000000 : ℝ), (31584553267181/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4325081157/10000000000 : ℝ)|^1077 ≤ (8325913053323/25000000000000 : ℝ)^821
        have hw : |(4325081157/10000000000 : ℝ)|=(4325081157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502955113/10000000000 : ℝ)|^1077 ≤ (35111794498413/100000000000000 : ℝ)^821
        have hw : |(4502955113/10000000000 : ℝ)|=(4502955113/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(166153019/400000000 : ℝ)|^1077 ≤ (31584553267181/100000000000000 : ℝ)^821
        have hw : |(166153019/400000000 : ℝ)|=(166153019/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1348_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2791/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1471/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11163/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11163/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11163/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14711/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11163/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11163/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14711/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11163/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11163/100000 : ℝ) ^ (4307/1024 : ℝ) ≤ (9883584849288879/100000000000000000000 : ℝ) := by
    have hpowers : (11163/100000 : ℝ)^4307 ≤ (9883584849288879/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11163 : ℕ)^4307*100000000000000000000^1024 ≤ 9883584849288879^1024*100000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11163 100000 9883584849288879 100000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11163/100000 : ℝ)) (X := (9883584849288879/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14711/100000 : ℝ) ^ (4307/1024 : ℝ) ≤ (31554227662841743/100000000000000000000 : ℝ) := by
    have hpowers : (14711/100000 : ℝ)^4307 ≤ (31554227662841743/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14711 : ℕ)^4307*100000000000000000000^1024 ≤ 31554227662841743^1024*100000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14711 100000 31554227662841743 100000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14711/100000 : ℝ)) (X := (31554227662841743/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009883584849288879/50000000000000000000 : ℝ) ≤ (10000469933991193/10000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50009883584849288879/50000000000000000000 : ℝ)^1024 ≤ (10000469933991193/10000000000000000 : ℝ)^4307 := by
      have hnat : (50009883584849288879 : ℕ)^1024*10000000000000000^4307 ≤ 10000469933991193^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009883584849288879 50000000000000000000 10000469933991193 10000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000469933991193/10000000000000000 : ℝ)) (X := (50009883584849288879/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020718906256065311/50000000000000000000 : ℝ) ≤ (5000492519390929/5000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50020718906256065311/50000000000000000000 : ℝ)^1024 ≤ (5000492519390929/5000000000000000 : ℝ)^4307 := by
      have hnat : (50020718906256065311 : ℕ)^1024*5000000000000000^4307 ≤ 5000492519390929^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020718906256065311 50000000000000000000 5000492519390929 5000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000492519390929/5000000000000000 : ℝ)) (X := (50020718906256065311/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50031554227662841743/50000000000000000000 : ℝ) ≤ (10001500143572523/10000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50031554227662841743/50000000000000000000 : ℝ)^1024 ≤ (10001500143572523/10000000000000000 : ℝ)^4307 := by
      have hnat : (50031554227662841743 : ℕ)^1024*10000000000000000^4307 ≤ 10001500143572523^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031554227662841743 50000000000000000000 10001500143572523 10000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001500143572523/10000000000000000 : ℝ)) (X := (50031554227662841743/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9883584849288879/100000000000000000000 : ℝ) ≤ ((17735083548122182987/17740000000000000000 : ℝ)+2*(103020958133/70960000000000 : ℝ)*(11163/100000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (17735083548122182987/17740000000000000000 : ℝ)+2*(103020958133/70960000000000 : ℝ)*(11163/100000 : ℝ)=(10000469933991193/10000000000000000 : ℝ) by norm_num, show 1+2*(9883584849288879/100000000000000000000 : ℝ)=(50009883584849288879/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(31554227662841743/100000000000000000000 : ℝ)+(9883584849288879/100000000000000000000 : ℝ) ≤ ((17735083548122182987/17740000000000000000 : ℝ)+(103020958133/70960000000000 : ℝ)*((14711/100000 : ℝ)+(11163/100000 : ℝ)))^(4307/1024 : ℝ) := by
    rw [show (17735083548122182987/17740000000000000000 : ℝ)+(103020958133/70960000000000 : ℝ)*((14711/100000 : ℝ)+(11163/100000 : ℝ))=(5000492519390929/5000000000000000 : ℝ) by norm_num, show 1+(31554227662841743/100000000000000000000 : ℝ)+(9883584849288879/100000000000000000000 : ℝ)=(50020718906256065311/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(31554227662841743/100000000000000000000 : ℝ) ≤ ((17735083548122182987/17740000000000000000 : ℝ)+2*(103020958133/70960000000000 : ℝ)*(14711/100000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (17735083548122182987/17740000000000000000 : ℝ)+2*(103020958133/70960000000000 : ℝ)*(14711/100000 : ℝ)=(10001500143572523/10000000000000000 : ℝ) by norm_num, show 1+2*(31554227662841743/100000000000000000000 : ℝ)=(50031554227662841743/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (17735083548122182987/17740000000000000000 : ℝ)*(X 1 0+X 2 0)+(103020958133/70960000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (11163/100000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (17735083548122182987/17740000000000000000 : ℝ)) (alpha := (103020958133/70960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (17735083548122182987/17740000000000000000 : ℝ)*(X 0 1+X 2 1)+(103020958133/70960000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (11163/100000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (17735083548122182987/17740000000000000000 : ℝ)) (alpha := (103020958133/70960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (17735083548122182987/17740000000000000000 : ℝ)*(X 0 2+X 1 2)+(103020958133/70960000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (11163/100000 : ℝ)) (hi := (14711/100000 : ℝ)) (c := (17735083548122182987/17740000000000000000 : ℝ)) (alpha := (103020958133/70960000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2038801397/10000000000 : ℝ)*X 0 0+(5412348221/10000000000 : ℝ)*X 0 1+(655604783/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348881737/10000000000 : ℝ)*X 1 0+(-424828647/2000000000 : ℝ)*X 1 1+(5244838261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348881779/10000000000 : ℝ)*X 2 0+(5244838211/10000000000 : ℝ)*X 2 1+(-2124143247/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4325055737/10000000000 : ℝ)*X 0 0+(4152560139/10000000000 : ℝ)*X 0 1+(2252106997/5000000000 : ℝ)*X 0 2+(4325055737/10000000000 : ℝ)*X 1 0+(4152560139/10000000000 : ℝ)*X 1 1+(2252106997/5000000000 : ℝ)*X 1 2+(4325055737/10000000000 : ℝ)*X 2 0+(4152560139/10000000000 : ℝ)*X 2 1+(2252106997/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1019406717/5000000000 : ℝ)*X 0 0+(5245437969/10000000000 : ℝ)*X 0 1+(5411745467/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530570511/1000000000 : ℝ)*X 1 0+(-489309031/2500000000 : ℝ)*X 1 1+(169117047/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305705101/10000000000 : ℝ)*X 2 0+(1352936387/2500000000 : ℝ)*X 2 1+(-1957236077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4325081157/10000000000 : ℝ)*X 0 0+(4502955113/10000000000 : ℝ)*X 0 1+(166153019/400000000 : ℝ)*X 0 2+(4325081157/10000000000 : ℝ)*X 1 0+(4502955113/10000000000 : ℝ)*X 1 1+(166153019/400000000 : ℝ)*X 1 2+(4325081157/10000000000 : ℝ)*X 2 0+(4502955113/10000000000 : ℝ)*X 2 1+(166153019/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2143796116917966430649095749/443500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (902077299/100000000000000 : ℝ)*(base19) + (214898257/25000000000000 : ℝ)*(base23) + (47797627/100000000000000 : ℝ)*(lower2) + (116485459/100000000000000 : ℝ)*(upper3) + (22538517/50000000000000 : ℝ)*(upper5) + (2203388982519109/50000000000000 : ℝ)*(major0) + (2203388982519109/50000000000000 : ℝ)*(major1) + (2203388982519109/50000000000000 : ℝ)*(major2) + (373113383481491/6250000000000 : ℝ)*(sp0) + (1492457961829761/25000000000000 : ℝ)*(sp1) + (1193966377960663/20000000000000 : ℝ)*(sp2) + (2843713438017867/100000000000000 : ℝ)*(sp3) + (2326711561/12500000000000 : ℝ)*(sp4) + (958153511/10000000000000 : ℝ)*(sp7) + (177732688722061/6250000000000 : ℝ)*(f.failure) + (5969832749396343/100000000000000 : ℝ)*(f.sum) + (3486069658747/1774000000000000000000000000 : ℝ)*base65 + (21367136324620551417/887000000000000000000000000000000 : ℝ)*base68 + (243779434739551417/887000000000000000000000000000000 : ℝ)*base70 + (4831972734897448583/887000000000000000000000000000000 : ℝ)*base71 + (324412017129/70960000000000000000000000 : ℝ)*base74 + (12358464998487551417/887000000000000000000000000000000 : ℝ)*base76 + (4599851252961551417/887000000000000000000000000000000 : ℝ)*base78 + (4944164281500448583/887000000000000000000000000000000 : ℝ)*base79 + (1026649415283/354800000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (5927449/625000000000000000000 : ℝ)*base90 + (5927449/625000000000000000000 : ℝ)*base92 + (5927449/625000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (159311248400170511678236179/22175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (24484581/3125000000000 : ℝ)*(base19) + (1022408529/100000000000000 : ℝ)*(base23) + (133995173/50000000000000 : ℝ)*(lower1) + (56875147/50000000000000 : ℝ)*(upper3) + (53521557/50000000000000 : ℝ)*(lower4) + (29876103/25000000000000 : ℝ)*(upper5) + (221929930435261/5000000000000 : ℝ)*(major0) + (221929930435261/5000000000000 : ℝ)*(major1) + (221929930435261/5000000000000 : ℝ)*(major2) + (2909309341/50000000000000 : ℝ)*(sp2) + (1202587977236819/20000000000000 : ℝ)*(sp4) + (6012939102677503/100000000000000 : ℝ)*(sp5) + (1202586609031377/20000000000000 : ℝ)*(sp6) + (2864257091750567/100000000000000 : ℝ)*(sp7) + (2864257091750567/100000000000000 : ℝ)*(f.failure) + (1202587977236819/20000000000000 : ℝ)*(f.sum) + (356536733861/443500000000000000000000000 : ℝ)*base65 + (3465410943751154607/88700000000000000000000000000000 : ℝ)*base67 + (47601294424354607/88700000000000000000000000000000 : ℝ)*base69 + (8402638839171054607/88700000000000000000000000000000 : ℝ)*base71 + (287938944819/110875000000000000000000000 : ℝ)*base73 + (1653527144914545393/88700000000000000000000000000000 : ℝ)*base76 + (167781812133954607/88700000000000000000000000000000 : ℝ)*base77 + (492590277996254607/88700000000000000000000000000000 : ℝ)*base79 + (2245472463603/887000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (35543403/10000000000000000000000 : ℝ)*base90 + (35543403/10000000000000000000000 : ℝ)*base92 + (35543403/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1348_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11163/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1348_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1348_box_0 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1872023541/10000000000 : ℝ)*x 0 + (5389688833/10000000000 : ℝ)*x 1 + (5389688659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1872023541/10000000000 : ℝ)^1077 ≤ (11102151706423/100000000000000 : ℝ)^821 := by
    have hnat : (1872023541 : ℕ)^1077*100000000000000^821 ≤ 11102151706423^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1872023541 10000000000 11102151706423 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389688833/10000000000 : ℝ)^1077 ≤ (22224462542329/50000000000000 : ℝ)^821 := by
    have hnat : (5389688833 : ℕ)^1077*50000000000000^821 ≤ 22224462542329^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389688833 10000000000 22224462542329 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5389688659/10000000000 : ℝ)^1077 ≤ (22224461601113/50000000000000 : ℝ)^821 := by
    have hnat : (5389688659 : ℕ)^1077*50000000000000^821 ≤ 22224461601113^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389688659 10000000000 22224461601113 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1872023541/10000000000 : ℝ), (5389688833/10000000000 : ℝ), (5389688659/10000000000 : ℝ)] ![(11102151706423/100000000000000 : ℝ), (22224462542329/50000000000000 : ℝ), (22224461601113/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1872023541/10000000000 : ℝ)|^1077 ≤ (11102151706423/100000000000000 : ℝ)^821
        have hw : |(-1872023541/10000000000 : ℝ)|=(1872023541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389688833/10000000000 : ℝ)|^1077 ≤ (22224462542329/50000000000000 : ℝ)^821
        have hw : |(5389688833/10000000000 : ℝ)|=(5389688833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5389688659/10000000000 : ℝ)|^1077 ≤ (22224461601113/50000000000000 : ℝ)^821
        have hw : |(5389688659/10000000000 : ℝ)|=(5389688659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_1 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2642623187/5000000000 : ℝ)*x 0 + (-4030287/20000000 : ℝ)*x 1 + (538968857/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642623187/5000000000 : ℝ)^1077 ≤ (43322435378623/100000000000000 : ℝ)^821 := by
    have hnat : (2642623187 : ℕ)^1077*100000000000000^821 ≤ 43322435378623^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642623187 5000000000 43322435378623 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4030287/20000000 : ℝ)^1077 ≤ (6114321183717/50000000000000 : ℝ)^821 := by
    have hnat : (4030287 : ℕ)^1077*50000000000000^821 ≤ 6114321183717^821*20000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4030287 20000000 6114321183717 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (538968857/1000000000 : ℝ)^1077 ≤ (11112230559843/25000000000000 : ℝ)^821 := by
    have hnat : (538968857 : ℕ)^1077*25000000000000^821 ≤ 11112230559843^821*1000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      538968857 1000000000 11112230559843 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642623187/5000000000 : ℝ), (-4030287/20000000 : ℝ), (538968857/1000000000 : ℝ)] ![(43322435378623/100000000000000 : ℝ), (6114321183717/50000000000000 : ℝ), (11112230559843/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642623187/5000000000 : ℝ)|^1077 ≤ (43322435378623/100000000000000 : ℝ)^821
        have hw : |(2642623187/5000000000 : ℝ)|=(2642623187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4030287/20000000 : ℝ)|^1077 ≤ (6114321183717/50000000000000 : ℝ)^821
        have hw : |(-4030287/20000000 : ℝ)|=(4030287/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(538968857/1000000000 : ℝ)|^1077 ≤ (11112230559843/25000000000000 : ℝ)^821
        have hw : |(538968857/1000000000 : ℝ)|=(538968857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_2 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2642623107/5000000000 : ℝ)*x 0 + (5389688787/10000000000 : ℝ)*x 1 + (-2015143421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642623107/5000000000 : ℝ)^1077 ≤ (2166121682909/5000000000000 : ℝ)^821 := by
    have hnat : (2642623107 : ℕ)^1077*5000000000000^821 ≤ 2166121682909^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642623107 5000000000 2166121682909 5000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389688787/10000000000 : ℝ)^1077 ≤ (44448924587003/100000000000000 : ℝ)^821 := by
    have hnat : (5389688787 : ℕ)^1077*100000000000000^821 ≤ 44448924587003^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389688787 10000000000 44448924587003 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015143421/10000000000 : ℝ)^1077 ≤ (3057160434637/25000000000000 : ℝ)^821 := by
    have hnat : (2015143421 : ℕ)^1077*25000000000000^821 ≤ 3057160434637^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015143421 10000000000 3057160434637 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642623107/5000000000 : ℝ), (5389688787/10000000000 : ℝ), (-2015143421/10000000000 : ℝ)] ![(2166121682909/5000000000000 : ℝ), (44448924587003/100000000000000 : ℝ), (3057160434637/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642623107/5000000000 : ℝ)|^1077 ≤ (2166121682909/5000000000000 : ℝ)^821
        have hw : |(2642623107/5000000000 : ℝ)|=(2642623107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389688787/10000000000 : ℝ)|^1077 ≤ (44448924587003/100000000000000 : ℝ)^821
        have hw : |(5389688787/10000000000 : ℝ)|=(5389688787/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2015143421/10000000000 : ℝ)|^1077 ≤ (3057160434637/25000000000000 : ℝ)^821
        have hw : |(-2015143421/10000000000 : ℝ)|=(2015143421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_3 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4473103021/10000000000 : ℝ)*x 0 + (4254907693/10000000000 : ℝ)*x 1 + (2127453947/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4473103021/10000000000 : ℝ)^1077 ≤ (17403378605437/50000000000000 : ℝ)^821 := by
    have hnat : (4473103021 : ℕ)^1077*50000000000000^821 ≤ 17403378605437^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4473103021 10000000000 17403378605437 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4254907693/10000000000 : ℝ)^1077 ≤ (32596620378853/100000000000000 : ℝ)^821 := by
    have hnat : (4254907693 : ℕ)^1077*100000000000000^821 ≤ 32596620378853^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254907693 10000000000 32596620378853 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2127453947/5000000000 : ℝ)^1077 ≤ (32596622398851/100000000000000 : ℝ)^821 := by
    have hnat : (2127453947 : ℕ)^1077*100000000000000^821 ≤ 32596622398851^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127453947 5000000000 32596622398851 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4473103021/10000000000 : ℝ), (4254907693/10000000000 : ℝ), (2127453947/5000000000 : ℝ)] ![(17403378605437/50000000000000 : ℝ), (32596620378853/100000000000000 : ℝ), (32596622398851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4473103021/10000000000 : ℝ)|^1077 ≤ (17403378605437/50000000000000 : ℝ)^821
        have hw : |(4473103021/10000000000 : ℝ)|=(4473103021/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4254907693/10000000000 : ℝ)|^1077 ≤ (32596620378853/100000000000000 : ℝ)^821
        have hw : |(4254907693/10000000000 : ℝ)|=(4254907693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2127453947/5000000000 : ℝ)|^1077 ≤ (32596622398851/100000000000000 : ℝ)^821
        have hw : |(2127453947/5000000000 : ℝ)|=(2127453947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_4 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-441665827/2000000000 : ℝ)*x 0 + (5265058827/10000000000 : ℝ)*x 1 + (1316264763/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (441665827/2000000000 : ℝ)^1077 ≤ (2757802394059/20000000000000 : ℝ)^821 := by
    have hnat : (441665827 : ℕ)^1077*20000000000000^821 ≤ 2757802394059^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441665827 2000000000 2757802394059 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265058827/10000000000 : ℝ)^1077 ≤ (5388186600241/12500000000000 : ℝ)^821 := by
    have hnat : (5265058827 : ℕ)^1077*12500000000000^821 ≤ 5388186600241^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265058827 10000000000 5388186600241 12500000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316264763/2500000000 : ℝ)^1077 ≤ (8621099043683/20000000000000 : ℝ)^821 := by
    have hnat : (1316264763 : ℕ)^1077*20000000000000^821 ≤ 8621099043683^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316264763 2500000000 8621099043683 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-441665827/2000000000 : ℝ), (5265058827/10000000000 : ℝ), (1316264763/2500000000 : ℝ)] ![(2757802394059/20000000000000 : ℝ), (5388186600241/12500000000000 : ℝ), (8621099043683/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-441665827/2000000000 : ℝ)|^1077 ≤ (2757802394059/20000000000000 : ℝ)^821
        have hw : |(-441665827/2000000000 : ℝ)|=(441665827/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265058827/10000000000 : ℝ)|^1077 ≤ (5388186600241/12500000000000 : ℝ)^821
        have hw : |(5265058827/10000000000 : ℝ)|=(5265058827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316264763/2500000000 : ℝ)|^1077 ≤ (8621099043683/20000000000000 : ℝ)^821
        have hw : |(1316264763/2500000000 : ℝ)|=(1316264763/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_5 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (671595127/1250000000 : ℝ)*x 0 + (-2065195107/10000000000 : ℝ)*x 1 + (5265059827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671595127/1250000000 : ℝ)^1077 ≤ (22132939971781/50000000000000 : ℝ)^821 := by
    have hnat : (671595127 : ℕ)^1077*50000000000000^821 ≤ 22132939971781^821*1250000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671595127 1250000000 22132939971781 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065195107/10000000000 : ℝ)^1077 ≤ (12628616495633/100000000000000 : ℝ)^821 := by
    have hnat : (2065195107 : ℕ)^1077*100000000000000^821 ≤ 12628616495633^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065195107 10000000000 12628616495633 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265059827/10000000000 : ℝ)^1077 ≤ (4310550354187/10000000000000 : ℝ)^821 := by
    have hnat : (5265059827 : ℕ)^1077*10000000000000^821 ≤ 4310550354187^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265059827 10000000000 4310550354187 10000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671595127/1250000000 : ℝ), (-2065195107/10000000000 : ℝ), (5265059827/10000000000 : ℝ)] ![(22132939971781/50000000000000 : ℝ), (12628616495633/100000000000000 : ℝ), (4310550354187/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671595127/1250000000 : ℝ)|^1077 ≤ (22132939971781/50000000000000 : ℝ)^821
        have hw : |(671595127/1250000000 : ℝ)|=(671595127/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2065195107/10000000000 : ℝ)|^1077 ≤ (12628616495633/100000000000000 : ℝ)^821
        have hw : |(-2065195107/10000000000 : ℝ)|=(2065195107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265059827/10000000000 : ℝ)|^1077 ≤ (4310550354187/10000000000000 : ℝ)^821
        have hw : |(5265059827/10000000000 : ℝ)|=(5265059827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_6 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (10745523/20000000 : ℝ)*x 0 + (131626483/250000000 : ℝ)*x 1 + (-1032597567/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10745523/20000000 : ℝ)^1077 ≤ (44265885174619/100000000000000 : ℝ)^821 := by
    have hnat : (10745523 : ℕ)^1077*100000000000000^821 ≤ 44265885174619^821*20000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10745523 20000000 44265885174619 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131626483/250000000 : ℝ)^1077 ≤ (538818726209/1250000000000 : ℝ)^821 := by
    have hnat : (131626483 : ℕ)^1077*1250000000000^821 ≤ 538818726209^821*250000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131626483 250000000 538818726209 1250000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1032597567/5000000000 : ℝ)^1077 ≤ (12628616712219/100000000000000 : ℝ)^821 := by
    have hnat : (1032597567 : ℕ)^1077*100000000000000^821 ≤ 12628616712219^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1032597567 5000000000 12628616712219 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10745523/20000000 : ℝ), (131626483/250000000 : ℝ), (-1032597567/5000000000 : ℝ)] ![(44265885174619/100000000000000 : ℝ), (538818726209/1250000000000 : ℝ), (12628616712219/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10745523/20000000 : ℝ)|^1077 ≤ (44265885174619/100000000000000 : ℝ)^821
        have hw : |(10745523/20000000 : ℝ)|=(10745523/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131626483/250000000 : ℝ)|^1077 ≤ (538818726209/1250000000000 : ℝ)^821
        have hw : |(131626483/250000000 : ℝ)|=(131626483/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1032597567/5000000000 : ℝ)|^1077 ≤ (12628616712219/100000000000000 : ℝ)^821
        have hw : |(-1032597567/5000000000 : ℝ)|=(1032597567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_7 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (417607313/1000000000 : ℝ)*x 0 + (4403369693/10000000000 : ℝ)*x 1 + (440336899/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (417607313/1000000000 : ℝ)^1077 ≤ (7951662904599/25000000000000 : ℝ)^821 := by
    have hnat : (417607313 : ℕ)^1077*25000000000000^821 ≤ 7951662904599^821*1000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417607313 1000000000 7951662904599 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4403369693/10000000000 : ℝ)^1077 ≤ (8524169438463/25000000000000 : ℝ)^821 := by
    have hnat : (4403369693 : ℕ)^1077*25000000000000^821 ≤ 8524169438463^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4403369693 10000000000 8524169438463 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (440336899/1000000000 : ℝ)^1077 ≤ (17048335306461/50000000000000 : ℝ)^821 := by
    have hnat : (440336899 : ℕ)^1077*50000000000000^821 ≤ 17048335306461^821*1000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      440336899 1000000000 17048335306461 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(417607313/1000000000 : ℝ), (4403369693/10000000000 : ℝ), (440336899/1000000000 : ℝ)] ![(7951662904599/25000000000000 : ℝ), (8524169438463/25000000000000 : ℝ), (17048335306461/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(417607313/1000000000 : ℝ)|^1077 ≤ (7951662904599/25000000000000 : ℝ)^821
        have hw : |(417607313/1000000000 : ℝ)|=(417607313/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4403369693/10000000000 : ℝ)|^1077 ≤ (8524169438463/25000000000000 : ℝ)^821
        have hw : |(4403369693/10000000000 : ℝ)|=(4403369693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(440336899/1000000000 : ℝ)|^1077 ≤ (17048335306461/50000000000000 : ℝ)^821
        have hw : |(440336899/1000000000 : ℝ)|=(440336899/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_8 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-133605597/625000000 : ℝ)*x 0 + (2589615833/5000000000 : ℝ)*x 1 + (10554113/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133605597/625000000 : ℝ)^1077 ≤ (13213303627497/100000000000000 : ℝ)^821 := by
    have hnat : (133605597 : ℕ)^1077*100000000000000^821 ≤ 13213303627497^821*625000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133605597 625000000 13213303627497 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2589615833/5000000000 : ℝ)^1077 ≤ (8437213117973/20000000000000 : ℝ)^821 := by
    have hnat : (2589615833 : ℕ)^1077*20000000000000^821 ≤ 8437213117973^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2589615833 5000000000 8437213117973 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10554113/19531250 : ℝ)^1077 ≤ (44600630769511/100000000000000 : ℝ)^821 := by
    have hnat : (10554113 : ℕ)^1077*100000000000000^821 ≤ 44600630769511^821*19531250^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10554113 19531250 44600630769511 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-133605597/625000000 : ℝ), (2589615833/5000000000 : ℝ), (10554113/19531250 : ℝ)] ![(13213303627497/100000000000000 : ℝ), (8437213117973/20000000000000 : ℝ), (44600630769511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-133605597/625000000 : ℝ)|^1077 ≤ (13213303627497/100000000000000 : ℝ)^821
        have hw : |(-133605597/625000000 : ℝ)|=(133605597/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2589615833/5000000000 : ℝ)|^1077 ≤ (8437213117973/20000000000000 : ℝ)^821
        have hw : |(2589615833/5000000000 : ℝ)|=(2589615833/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10554113/19531250 : ℝ)|^1077 ≤ (44600630769511/100000000000000 : ℝ)^821
        have hw : |(10554113/19531250 : ℝ)|=(10554113/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_9 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2637699177/5000000000 : ℝ)*x 0 + (-200938201/1000000000 : ℝ)*x 1 + (5403705717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637699177/5000000000 : ℝ)^1077 ≤ (43216572705131/100000000000000 : ℝ)^821 := by
    have hnat : (2637699177 : ℕ)^1077*100000000000000^821 ≤ 43216572705131^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637699177 5000000000 43216572705131 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200938201/1000000000 : ℝ)^1077 ≤ (12182798012569/100000000000000 : ℝ)^821 := by
    have hnat : (200938201 : ℕ)^1077*100000000000000^821 ≤ 12182798012569^821*1000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200938201 1000000000 12182798012569 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5403705717/10000000000 : ℝ)^1077 ≤ (44600629264511/100000000000000 : ℝ)^821 := by
    have hnat : (5403705717 : ℕ)^1077*100000000000000^821 ≤ 44600629264511^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403705717 10000000000 44600629264511 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637699177/5000000000 : ℝ), (-200938201/1000000000 : ℝ), (5403705717/10000000000 : ℝ)] ![(43216572705131/100000000000000 : ℝ), (12182798012569/100000000000000 : ℝ), (44600629264511/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637699177/5000000000 : ℝ)|^1077 ≤ (43216572705131/100000000000000 : ℝ)^821
        have hw : |(2637699177/5000000000 : ℝ)|=(2637699177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-200938201/1000000000 : ℝ)|^1077 ≤ (12182798012569/100000000000000 : ℝ)^821
        have hw : |(-200938201/1000000000 : ℝ)|=(200938201/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5403705717/10000000000 : ℝ)|^1077 ≤ (44600629264511/100000000000000 : ℝ)^821
        have hw : |(5403705717/10000000000 : ℝ)|=(5403705717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_10 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (1055079649/2000000000 : ℝ)*x 0 + (33773161/62500000 : ℝ)*x 1 + (-1004691049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055079649/2000000000 : ℝ)^1077 ≤ (43216571533761/100000000000000 : ℝ)^821 := by
    have hnat : (1055079649 : ℕ)^1077*100000000000000^821 ≤ 43216571533761^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055079649 2000000000 43216571533761 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (33773161/62500000 : ℝ)^1077 ≤ (22300314865043/50000000000000 : ℝ)^821 := by
    have hnat : (33773161 : ℕ)^1077*50000000000000^821 ≤ 22300314865043^821*62500000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      33773161 62500000 22300314865043 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1004691049/5000000000 : ℝ)^1077 ≤ (487311948499/4000000000000 : ℝ)^821 := by
    have hnat : (1004691049 : ℕ)^1077*4000000000000^821 ≤ 487311948499^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1004691049 5000000000 487311948499 4000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055079649/2000000000 : ℝ), (33773161/62500000 : ℝ), (-1004691049/5000000000 : ℝ)] ![(43216571533761/100000000000000 : ℝ), (22300314865043/50000000000000 : ℝ), (487311948499/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055079649/2000000000 : ℝ)|^1077 ≤ (43216571533761/100000000000000 : ℝ)^821
        have hw : |(1055079649/2000000000 : ℝ)|=(1055079649/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(33773161/62500000 : ℝ)|^1077 ≤ (22300314865043/50000000000000 : ℝ)^821
        have hw : |(33773161/62500000 : ℝ)|=(33773161/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1004691049/5000000000 : ℝ)|^1077 ≤ (487311948499/4000000000000 : ℝ)^821
        have hw : |(-1004691049/5000000000 : ℝ)|=(1004691049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_11 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4505950489/10000000000 : ℝ)*x 0 + (4238196517/10000000000 : ℝ)*x 1 + (4238196759/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4505950489/10000000000 : ℝ)^1077 ≤ (35142437008069/100000000000000 : ℝ)^821 := by
    have hnat : (4505950489 : ℕ)^1077*100000000000000^821 ≤ 35142437008069^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4505950489 10000000000 35142437008069 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4238196517/10000000000 : ℝ)^1077 ≤ (16214390137567/50000000000000 : ℝ)^821 := by
    have hnat : (4238196517 : ℕ)^1077*50000000000000^821 ≤ 16214390137567^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238196517 10000000000 16214390137567 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4238196759/10000000000 : ℝ)^1077 ≤ (3242878270419/10000000000000 : ℝ)^821 := by
    have hnat : (4238196759 : ℕ)^1077*10000000000000^821 ≤ 3242878270419^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4238196759 10000000000 3242878270419 10000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4505950489/10000000000 : ℝ), (4238196517/10000000000 : ℝ), (4238196759/10000000000 : ℝ)] ![(35142437008069/100000000000000 : ℝ), (16214390137567/50000000000000 : ℝ), (3242878270419/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4505950489/10000000000 : ℝ)|^1077 ≤ (35142437008069/100000000000000 : ℝ)^821
        have hw : |(4505950489/10000000000 : ℝ)|=(4505950489/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4238196517/10000000000 : ℝ)|^1077 ≤ (16214390137567/50000000000000 : ℝ)^821
        have hw : |(4238196517/10000000000 : ℝ)|=(4238196517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4238196759/10000000000 : ℝ)|^1077 ≤ (3242878270419/10000000000000 : ℝ)^821
        have hw : |(4238196759/10000000000 : ℝ)|=(4238196759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_12 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-38859773/200000000 : ℝ)*x 0 + (1368331053/2500000000 : ℝ)*x 1 + (5253984743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (38859773/200000000 : ℝ)^1077 ≤ (5828740531013/50000000000000 : ℝ)^821 := by
    have hnat : (38859773 : ℕ)^1077*50000000000000^821 ≤ 5828740531013^821*200000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      38859773 200000000 5828740531013 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368331053/2500000000 : ℝ)^1077 ≤ (4535592211877/10000000000000 : ℝ)^821 := by
    have hnat : (1368331053 : ℕ)^1077*10000000000000^821 ≤ 4535592211877^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368331053 2500000000 4535592211877 10000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253984743/10000000000 : ℝ)^1077 ≤ (21493298401641/50000000000000 : ℝ)^821 := by
    have hnat : (5253984743 : ℕ)^1077*50000000000000^821 ≤ 21493298401641^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253984743 10000000000 21493298401641 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-38859773/200000000 : ℝ), (1368331053/2500000000 : ℝ), (5253984743/10000000000 : ℝ)] ![(5828740531013/50000000000000 : ℝ), (4535592211877/10000000000000 : ℝ), (21493298401641/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-38859773/200000000 : ℝ)|^1077 ≤ (5828740531013/50000000000000 : ℝ)^821
        have hw : |(-38859773/200000000 : ℝ)|=(38859773/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368331053/2500000000 : ℝ)|^1077 ≤ (4535592211877/10000000000000 : ℝ)^821
        have hw : |(1368331053/2500000000 : ℝ)|=(1368331053/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253984743/10000000000 : ℝ)|^1077 ≤ (21493298401641/50000000000000 : ℝ)^821
        have hw : |(5253984743/10000000000 : ℝ)|=(5253984743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_13 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5380535831/10000000000 : ℝ)*x 0 + (-258692419/1250000000 : ℝ)*x 1 + (5253984567/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380535831/10000000000 : ℝ)^1077 ≤ (44349928861463/100000000000000 : ℝ)^821 := by
    have hnat : (5380535831 : ℕ)^1077*100000000000000^821 ≤ 44349928861463^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380535831 10000000000 44349928861463 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258692419/1250000000 : ℝ)^1077 ≤ (12663476214673/100000000000000 : ℝ)^821 := by
    have hnat : (258692419 : ℕ)^1077*100000000000000^821 ≤ 12663476214673^821*1250000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258692419 1250000000 12663476214673 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253984567/10000000000 : ℝ)^1077 ≤ (42986594914293/100000000000000 : ℝ)^821 := by
    have hnat : (5253984567 : ℕ)^1077*100000000000000^821 ≤ 42986594914293^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253984567 10000000000 42986594914293 100000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380535831/10000000000 : ℝ), (-258692419/1250000000 : ℝ), (5253984567/10000000000 : ℝ)] ![(44349928861463/100000000000000 : ℝ), (12663476214673/100000000000000 : ℝ), (42986594914293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380535831/10000000000 : ℝ)|^1077 ≤ (44349928861463/100000000000000 : ℝ)^821
        have hw : |(5380535831/10000000000 : ℝ)|=(5380535831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-258692419/1250000000 : ℝ)|^1077 ≤ (12663476214673/100000000000000 : ℝ)^821
        have hw : |(-258692419/1250000000 : ℝ)|=(258692419/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253984567/10000000000 : ℝ)|^1077 ≤ (42986594914293/100000000000000 : ℝ)^821
        have hw : |(5253984567/10000000000 : ℝ)|=(5253984567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_14 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2690268303/5000000000 : ℝ)*x 0 + (5253983991/10000000000 : ℝ)*x 1 + (-2069539077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2690268303/5000000000 : ℝ)^1077 ≤ (22174968620709/50000000000000 : ℝ)^821 := by
    have hnat : (2690268303 : ℕ)^1077*50000000000000^821 ≤ 22174968620709^821*5000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2690268303 5000000000 22174968620709 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5253983991/10000000000 : ℝ)^1077 ≤ (21493294366073/50000000000000 : ℝ)^821 := by
    have hnat : (5253983991 : ℕ)^1077*50000000000000^821 ≤ 21493294366073^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253983991 10000000000 21493294366073 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2069539077/10000000000 : ℝ)^1077 ≤ (1582934250907/12500000000000 : ℝ)^821 := by
    have hnat : (2069539077 : ℕ)^1077*12500000000000^821 ≤ 1582934250907^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2069539077 10000000000 1582934250907 12500000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2690268303/5000000000 : ℝ), (5253983991/10000000000 : ℝ), (-2069539077/10000000000 : ℝ)] ![(22174968620709/50000000000000 : ℝ), (21493294366073/50000000000000 : ℝ), (1582934250907/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2690268303/5000000000 : ℝ)|^1077 ≤ (22174968620709/50000000000000 : ℝ)^821
        have hw : |(2690268303/5000000000 : ℝ)|=(2690268303/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5253983991/10000000000 : ℝ)|^1077 ≤ (21493294366073/50000000000000 : ℝ)^821
        have hw : |(5253983991/10000000000 : ℝ)|=(5253983991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2069539077/10000000000 : ℝ)|^1077 ≤ (1582934250907/12500000000000 : ℝ)^821
        have hw : |(-2069539077/10000000000 : ℝ)|=(2069539077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1348_box_15 (p : ℝ) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ)) (x : Fin 3 → ℝ) :
    (829846737/2000000000 : ℝ)*x 0 + (1104137319/2500000000 : ℝ)*x 1 + (4416550169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (829846737/2000000000 : ℝ)^1077 ≤ (7884689879979/25000000000000 : ℝ)^821 := by
    have hnat : (829846737 : ℕ)^1077*25000000000000^821 ≤ 7884689879979^821*2000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      829846737 2000000000 7884689879979 25000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104137319/2500000000 : ℝ)^1077 ≤ (17115307845433/50000000000000 : ℝ)^821 := by
    have hnat : (1104137319 : ℕ)^1077*50000000000000^821 ≤ 17115307845433^821*2500000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104137319 2500000000 17115307845433 50000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4416550169/10000000000 : ℝ)^1077 ≤ (6846124954047/20000000000000 : ℝ)^821 := by
    have hnat : (4416550169 : ℕ)^1077*20000000000000^821 ≤ 6846124954047^821*10000000000^1077 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4416550169 10000000000 6846124954047 20000000000000 1077 821 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1077/256 : ℝ)) 1077 821 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(829846737/2000000000 : ℝ), (1104137319/2500000000 : ℝ), (4416550169/10000000000 : ℝ)] ![(7884689879979/25000000000000 : ℝ), (17115307845433/50000000000000 : ℝ), (6846124954047/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(829846737/2000000000 : ℝ)|^1077 ≤ (7884689879979/25000000000000 : ℝ)^821
        have hw : |(829846737/2000000000 : ℝ)|=(829846737/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1104137319/2500000000 : ℝ)|^1077 ≤ (17115307845433/50000000000000 : ℝ)^821
        have hw : |(1104137319/2500000000 : ℝ)|=(1104137319/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4416550169/10000000000 : ℝ)|^1077 ≤ (6846124954047/20000000000000 : ℝ)^821
        have hw : |(4416550169/10000000000 : ℝ)|=(4416550169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1348_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31429/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58953/100000 : ℝ) ∧ (79989/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (27/32 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1471/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2791/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1471/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2791/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1471/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2791/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1471/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2791/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1471/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2791/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1471/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2791/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2791/25000 : ℝ) ^ (4307/1024 : ℝ) ≤ (9887309373918049/100000000000000000000 : ℝ) := by
    have hpowers : (2791/25000 : ℝ)^4307 ≤ (9887309373918049/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2791 : ℕ)^4307*100000000000000000000^1024 ≤ 9887309373918049^1024*25000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2791 25000 9887309373918049 100000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2791/25000 : ℝ)) (X := (9887309373918049/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1471/10000 : ℝ) ^ (4307/1024 : ℝ) ≤ (6309041381310109/20000000000000000000 : ℝ) := by
    have hpowers : (1471/10000 : ℝ)^4307 ≤ (6309041381310109/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1471 : ℕ)^4307*20000000000000000000^1024 ≤ 6309041381310109^1024*10000^4307 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1471 10000 6309041381310109 20000000000000000000 4307 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1471/10000 : ℝ)) (X := (6309041381310109/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009887309373918049/50000000000000000000 : ℝ) ≤ (10000470111067513/10000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50009887309373918049/50000000000000000000 : ℝ)^1024 ≤ (10000470111067513/10000000000000000 : ℝ)^4307 := by
      have hnat : (50009887309373918049 : ℕ)^1024*10000000000000000^4307 ≤ 10000470111067513^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009887309373918049 50000000000000000000 10000470111067513 10000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000470111067513/10000000000000000 : ℝ)) (X := (50009887309373918049/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020716258140234297/50000000000000000000 : ℝ) ≤ (625061557056399/625000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (50020716258140234297/50000000000000000000 : ℝ)^1024 ≤ (625061557056399/625000000000000 : ℝ)^4307 := by
      have hnat : (50020716258140234297 : ℕ)^1024*625000000000000^4307 ≤ 625061557056399^4307*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020716258140234297 50000000000000000000 625061557056399 625000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625061557056399/625000000000000 : ℝ)) (X := (50020716258140234297/50000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006309041381310109/10000000000000000000 : ℝ) ≤ (2000299942947451/2000000000000000 : ℝ) ^ (4307/1024 : ℝ) := by
    have hpowers : (10006309041381310109/10000000000000000000 : ℝ)^1024 ≤ (2000299942947451/2000000000000000 : ℝ)^4307 := by
      have hnat : (10006309041381310109 : ℕ)^1024*2000000000000000^4307 ≤ 2000299942947451^4307*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006309041381310109 10000000000000000000 2000299942947451 2000000000000000 1024 4307 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000299942947451/2000000000000000 : ℝ)) (X := (10006309041381310109/10000000000000000000 : ℝ)) (by norm_num) 4307 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9887309373918049/100000000000000000000 : ℝ) ≤ ((3545017251847640141/3546000000000000000 : ℝ)+2*(514801834871/354600000000000 : ℝ)*(2791/25000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (3545017251847640141/3546000000000000000 : ℝ)+2*(514801834871/354600000000000 : ℝ)*(2791/25000 : ℝ)=(10000470111067513/10000000000000000 : ℝ) by norm_num, show 1+2*(9887309373918049/100000000000000000000 : ℝ)=(50009887309373918049/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6309041381310109/20000000000000000000 : ℝ)+(9887309373918049/100000000000000000000 : ℝ) ≤ ((3545017251847640141/3546000000000000000 : ℝ)+(514801834871/354600000000000 : ℝ)*((1471/10000 : ℝ)+(2791/25000 : ℝ)))^(4307/1024 : ℝ) := by
    rw [show (3545017251847640141/3546000000000000000 : ℝ)+(514801834871/354600000000000 : ℝ)*((1471/10000 : ℝ)+(2791/25000 : ℝ))=(625061557056399/625000000000000 : ℝ) by norm_num, show 1+(6309041381310109/20000000000000000000 : ℝ)+(9887309373918049/100000000000000000000 : ℝ)=(50020716258140234297/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6309041381310109/20000000000000000000 : ℝ) ≤ ((3545017251847640141/3546000000000000000 : ℝ)+2*(514801834871/354600000000000 : ℝ)*(1471/10000 : ℝ))^(4307/1024 : ℝ) := by
    rw [show (3545017251847640141/3546000000000000000 : ℝ)+2*(514801834871/354600000000000 : ℝ)*(1471/10000 : ℝ)=(2000299942947451/2000000000000000 : ℝ) by norm_num, show 1+2*(6309041381310109/20000000000000000000 : ℝ)=(10006309041381310109/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3545017251847640141/3546000000000000000 : ℝ)*(X 1 0+X 2 0)+(514801834871/354600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (2791/25000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (3545017251847640141/3546000000000000000 : ℝ)) (alpha := (514801834871/354600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3545017251847640141/3546000000000000000 : ℝ)*(X 0 1+X 2 1)+(514801834871/354600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (2791/25000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (3545017251847640141/3546000000000000000 : ℝ)) (alpha := (514801834871/354600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3545017251847640141/3546000000000000000 : ℝ)*(X 0 2+X 1 2)+(514801834871/354600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4307/1024 : ℝ)) (lo := (2791/25000 : ℝ)) (hi := (1471/10000 : ℝ)) (c := (3545017251847640141/3546000000000000000 : ℝ)) (alpha := (514801834871/354600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1872023541/10000000000 : ℝ)*X 0 0+(5389688833/10000000000 : ℝ)*X 0 1+(5389688659/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642623187/5000000000 : ℝ)*X 1 0+(-4030287/20000000 : ℝ)*X 1 1+(538968857/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642623107/5000000000 : ℝ)*X 2 0+(5389688787/10000000000 : ℝ)*X 2 1+(-2015143421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4473103021/10000000000 : ℝ)*X 0 0+(4254907693/10000000000 : ℝ)*X 0 1+(2127453947/5000000000 : ℝ)*X 0 2+(4473103021/10000000000 : ℝ)*X 1 0+(4254907693/10000000000 : ℝ)*X 1 1+(2127453947/5000000000 : ℝ)*X 1 2+(4473103021/10000000000 : ℝ)*X 2 0+(4254907693/10000000000 : ℝ)*X 2 1+(2127453947/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-441665827/2000000000 : ℝ)*X 0 0+(5265058827/10000000000 : ℝ)*X 0 1+(1316264763/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((671595127/1250000000 : ℝ)*X 1 0+(-2065195107/10000000000 : ℝ)*X 1 1+(5265059827/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((10745523/20000000 : ℝ)*X 2 0+(131626483/250000000 : ℝ)*X 2 1+(-1032597567/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((417607313/1000000000 : ℝ)*X 0 0+(4403369693/10000000000 : ℝ)*X 0 1+(440336899/1000000000 : ℝ)*X 0 2+(417607313/1000000000 : ℝ)*X 1 0+(4403369693/10000000000 : ℝ)*X 1 1+(440336899/1000000000 : ℝ)*X 1 2+(417607313/1000000000 : ℝ)*X 2 0+(4403369693/10000000000 : ℝ)*X 2 1+(440336899/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-133605597/625000000 : ℝ)*X 0 0+(2589615833/5000000000 : ℝ)*X 0 1+(10554113/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637699177/5000000000 : ℝ)*X 1 0+(-200938201/1000000000 : ℝ)*X 1 1+(5403705717/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1055079649/2000000000 : ℝ)*X 2 0+(33773161/62500000 : ℝ)*X 2 1+(-1004691049/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4505950489/10000000000 : ℝ)*X 0 0+(4238196517/10000000000 : ℝ)*X 0 1+(4238196759/10000000000 : ℝ)*X 0 2+(4505950489/10000000000 : ℝ)*X 1 0+(4238196517/10000000000 : ℝ)*X 1 1+(4238196759/10000000000 : ℝ)*X 1 2+(4505950489/10000000000 : ℝ)*X 2 0+(4238196517/10000000000 : ℝ)*X 2 1+(4238196759/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-38859773/200000000 : ℝ)*X 0 0+(1368331053/2500000000 : ℝ)*X 0 1+(5253984743/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5380535831/10000000000 : ℝ)*X 1 0+(-258692419/1250000000 : ℝ)*X 1 1+(5253984567/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2690268303/5000000000 : ℝ)*X 2 0+(5253983991/10000000000 : ℝ)*X 2 1+(-2069539077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((829846737/2000000000 : ℝ)*X 0 0+(1104137319/2500000000 : ℝ)*X 0 1+(4416550169/10000000000 : ℝ)*X 0 2+(829846737/2000000000 : ℝ)*X 1 0+(1104137319/2500000000 : ℝ)*X 1 1+(4416550169/10000000000 : ℝ)*X 1 2+(829846737/2000000000 : ℝ)*X 2 0+(1104137319/2500000000 : ℝ)*X 2 1+(4416550169/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1348_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31429/50000 : ℝ) ≤ (-6191234930671699880889966188569/9850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (80021993/100000000000000 : ℝ)*(lower0) + (6414719/100000000000000 : ℝ)*(upper1) + (22681071/25000000000000 : ℝ)*(lower2) + (2927385272479073/100000000000000 : ℝ)*(major0) + (2927385272479073/100000000000000 : ℝ)*(major1) + (2927385272479073/100000000000000 : ℝ)*(major2) + (6283898633/100000000000000 : ℝ)*(sp3) + (797331757309027/20000000000000 : ℝ)*(sp4) + (1993203040618193/50000000000000 : ℝ)*(sp5) + (1993268787335467/50000000000000 : ℝ)*(sp6) + (1889054828890359/100000000000000 : ℝ)*(sp7) + (1185638861/50000000000000 : ℝ)*(sp8) + (255076586471/100000000000000 : ℝ)*(sp13) + (61791575961/50000000000000 : ℝ)*(sp14) + (1889061112788991/100000000000000 : ℝ)*(f.failure) + (498332644727857/12500000000000 : ℝ)*(f.sum) + (2367565435037/17730000000000000000000000000 : ℝ)*base66 + (2899311658930700707/354600000000000000000000000000000 : ℝ)*base68 + (3104892218471300707/354600000000000000000000000000000 : ℝ)*base70 + (4303073624480900707/354600000000000000000000000000000 : ℝ)*base72 + (126383294546323/17730000000000000000000000000 : ℝ)*base73 + (1219202546565500707/354600000000000000000000000000000 : ℝ)*base76 + (890980213643900707/354600000000000000000000000000000 : ℝ)*base78 + (2784825604528299293/354600000000000000000000000000000 : ℝ)*base79 + (5076730232323/17730000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (45886819/10000000000000000000000 : ℝ)*base90 + (45886819/10000000000000000000000 : ℝ)*base92 + (45886819/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (58953/100000 : ℝ) ≤ (3484261759060396416263440933/5910000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12929773/50000000000000 : ℝ)*(upper0) + (1319343/12500000000000 : ℝ)*(lower1) + (2665797/50000000000000 : ℝ)*(upper2) + (2996279457449573/100000000000000 : ℝ)*(major0) + (2996279457449573/100000000000000 : ℝ)*(major1) + (2996279457449573/100000000000000 : ℝ)*(major2) + (403938677663573/10000000000000 : ℝ)*(sp0) + (2019676799597677/50000000000000 : ℝ)*(sp1) + (1009846313177041/25000000000000 : ℝ)*(sp2) + (241689562509351/12500000000000 : ℝ)*(sp3) + (2888785853/100000000000000 : ℝ)*(sp6) + (155422449/6250000000000 : ℝ)*(sp7) + (682429143/50000000000000 : ℝ)*(sp8) + (34542298663/100000000000000 : ℝ)*(sp9) + (241689873354249/12500000000000 : ℝ)*(f.failure) + (4039388141494017/100000000000000 : ℝ)*(f.sum) + (137787229354697/17730000000000000000000000000 : ℝ)*base66 + (1191748427757739793/354600000000000000000000000000000 : ℝ)*base67 + (419659629828139793/354600000000000000000000000000000 : ℝ)*base69 + (1823440890676660207/354600000000000000000000000000000 : ℝ)*base72 + (682441864935103/17730000000000000000000000000 : ℝ)*base73 + (3623472288740860207/354600000000000000000000000000000 : ℝ)*base76 + (3794379851067460207/354600000000000000000000000000000 : ℝ)*base78 + (9002710756532539793/354600000000000000000000000000000 : ℝ)*base79 + (75420838783097/17730000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (9021659/1250000000000000000000 : ℝ)*base89 + (9021659/1250000000000000000000 : ℝ)*base91 + (9021659/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (79989/100000 : ℝ) ≤ (3939604209903386387707059921717/4925000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32688009/50000000000000 : ℝ)*(upper2) + (60150471/100000000000000 : ℝ)*(lower3) + (11397717/100000000000000 : ℝ)*(lower4) + (3898073/12500000000000 : ℝ)*(lower5) + (827036008613463/25000000000000 : ℝ)*(major0) + (827036008613463/25000000000000 : ℝ)*(major1) + (827036008613463/25000000000000 : ℝ)*(major2) + (1790702397/6250000000000 : ℝ)*(sp1) + (7513476303/25000000000000 : ℝ)*(sp3) + (302444047/10000000000000 : ℝ)*(sp4) + (8700886312179/195312500000 : ℝ)*(sp8) + (2227414082518883/50000000000000 : ℝ)*(sp9) + (2227428408138059/50000000000000 : ℝ)*(sp10) + (13342107567763/625000000000 : ℝ)*(sp11) + (533691816186823/25000000000000 : ℝ)*(f.failure) + (2227428408138059/50000000000000 : ℝ)*(f.sum) + (131072251693/46171875000000000000000000 : ℝ)*base65 + (450083832828482761/29550000000000000000000000000000 : ℝ)*base67 + (168006570397382761/29550000000000000000000000000000 : ℝ)*base69 + (202608319960982761/29550000000000000000000000000000 : ℝ)*base71 + (2934964648451/1477500000000000000000000000 : ℝ)*base73 + (230671608457682761/29550000000000000000000000000000 : ℝ)*base75 + (536208905065082761/29550000000000000000000000000000 : ℝ)*base77 + (246535116808382761/29550000000000000000000000000000 : ℝ)*base79 + (4000098730481/1477500000000000000000000000 : ℝ)*base81 + (804107/2500000000000000000000 : ℝ)*base90 + (804107/2500000000000000000000 : ℝ)*base92 + (804107/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-27/32 : ℝ) ≤ (-4986439310918502720696811874069/5910000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (59258227/100000000000000 : ℝ)*(lower0) + (101638057/25000000000000 : ℝ)*(lower1) + (301064189/100000000000000 : ℝ)*(lower2) + (334469119859191/10000000000000 : ℝ)*(major0) + (334469119859191/10000000000000 : ℝ)*(major1) + (334469119859191/10000000000000 : ℝ)*(major2) + (5077158981/100000000000000 : ℝ)*(sp0) + (4013936629/800000000000 : ℝ)*(sp5) + (113790225339/20000000000000 : ℝ)*(sp6) + (5686676487/25000000000000 : ℝ)*(sp7) + (911830046659361/20000000000000 : ℝ)*(sp12) + (4558653568377161/100000000000000 : ℝ)*(sp13) + (4558586359329091/100000000000000 : ℝ)*(sp14) + (33723885081503/1562500000000 : ℝ)*(sp15) + (107917569596107/5000000000000 : ℝ)*(f.failure) + (2279577655227893/50000000000000 : ℝ)*(f.sum) + (74591598317/221625000000000000000000000 : ℝ)*base66 + (449159913444944069/35460000000000000000000000000000 : ℝ)*base68 + (374354163135524069/35460000000000000000000000000000 : ℝ)*base70 + (48612291734535931/35460000000000000000000000000000 : ℝ)*base71 + (29155602208699/443250000000000000000000000 : ℝ)*base74 + (487678279616804069/35460000000000000000000000000000 : ℝ)*base76 + (199139677736235931/35460000000000000000000000000000 : ℝ)*base77 + (2682254397389024069/35460000000000000000000000000000 : ℝ)*base80 + (2826689252501/886500000000000000000000000 : ℝ)*base82 + (4500737/500000000000000000000 : ℝ)*base89 + (4500737/500000000000000000000 : ℝ)*base91 + (4500737/500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1348_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1471/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2791/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31429/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58953/100000 : ℝ) else (79989/100000 : ℝ) ≤ X j i ∧ X j i ≤ (27/32 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1348_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1348_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31429/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58953/100000 : ℝ) else (79989/100000 : ℝ) ≤ X j i ∧ X j i ≤ (27/32 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1348_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1348_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1348_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4307/1024 : ℝ) ≤ p) (hpb : p ≤ (1077/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (154965091/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14719/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2789/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31429/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(58953/100000 : ℝ) else (79989/100000 : ℝ) ≤ X j i ∧ X j i ≤ (27/32 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1348_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
