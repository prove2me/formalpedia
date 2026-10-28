-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1076_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:14:23.642761+00:00
-- url     : https://prove2.me/submissions/41e89084-b1c2-42b0-9c0e-0f60be16ee74

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
theorem support_rectangle_w1076_s6_0 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-549702423/2500000000 : ℝ)*x 0 + (539471353/1000000000 : ℝ)*x 1 + (1316033127/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549702423/2500000000 : ℝ)^8269 ≤ (13354599428517/100000000000000 : ℝ)^6221 := by
    have hnat : (549702423 : ℕ)^8269*100000000000000^6221 ≤ 13354599428517^6221*2500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549702423 2500000000 13354599428517 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539471353/1000000000 : ℝ)^8269 ≤ (11007035654599/25000000000000 : ℝ)^6221 := by
    have hnat : (539471353 : ℕ)^8269*25000000000000^6221 ≤ 11007035654599^6221*1000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539471353 1000000000 11007035654599 25000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316033127/2500000000 : ℝ)^8269 ≤ (21308628968241/50000000000000 : ℝ)^6221 := by
    have hnat : (1316033127 : ℕ)^8269*50000000000000^6221 ≤ 21308628968241^6221*2500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316033127 2500000000 21308628968241 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549702423/2500000000 : ℝ), (539471353/1000000000 : ℝ), (1316033127/2500000000 : ℝ)] ![(13354599428517/100000000000000 : ℝ), (11007035654599/25000000000000 : ℝ), (21308628968241/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549702423/2500000000 : ℝ)|^8269 ≤ (13354599428517/100000000000000 : ℝ)^6221
        have hw : |(-549702423/2500000000 : ℝ)|=(549702423/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539471353/1000000000 : ℝ)|^8269 ≤ (11007035654599/25000000000000 : ℝ)^6221
        have hw : |(539471353/1000000000 : ℝ)|=(539471353/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316033127/2500000000 : ℝ)|^8269 ≤ (21308628968241/50000000000000 : ℝ)^6221
        have hw : |(1316033127/2500000000 : ℝ)|=(1316033127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s6_1 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345087463/10000000000 : ℝ)*x 0 + (-90602679/400000000 : ℝ)*x 1 + (2632066311/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345087463/10000000000 : ℝ)^8269 ≤ (43490609581701/100000000000000 : ℝ)^6221 := by
    have hnat : (5345087463 : ℕ)^8269*100000000000000^6221 ≤ 43490609581701^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345087463 10000000000 43490609581701 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (90602679/400000000 : ℝ)^8269 ≤ (6946065618829/50000000000000 : ℝ)^6221 := by
    have hnat : (90602679 : ℕ)^8269*50000000000000^6221 ≤ 6946065618829^6221*400000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90602679 400000000 6946065618829 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632066311/5000000000 : ℝ)^8269 ≤ (1331789348851/3125000000000 : ℝ)^6221 := by
    have hnat : (2632066311 : ℕ)^8269*3125000000000^6221 ≤ 1331789348851^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632066311 5000000000 1331789348851 3125000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345087463/10000000000 : ℝ), (-90602679/400000000 : ℝ), (2632066311/5000000000 : ℝ)] ![(43490609581701/100000000000000 : ℝ), (6946065618829/50000000000000 : ℝ), (1331789348851/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345087463/10000000000 : ℝ)|^8269 ≤ (43490609581701/100000000000000 : ℝ)^6221
        have hw : |(5345087463/10000000000 : ℝ)|=(5345087463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-90602679/400000000 : ℝ)|^8269 ≤ (6946065618829/50000000000000 : ℝ)^6221
        have hw : |(-90602679/400000000 : ℝ)|=(90602679/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632066311/5000000000 : ℝ)|^8269 ≤ (1331789348851/3125000000000 : ℝ)^6221
        have hw : |(2632066311/5000000000 : ℝ)|=(2632066311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s6_2 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2672543537/5000000000 : ℝ)*x 0 + (5264132831/10000000000 : ℝ)*x 1 + (-453013443/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2672543537/5000000000 : ℝ)^8269 ≤ (43490605374599/100000000000000 : ℝ)^6221 := by
    have hnat : (2672543537 : ℕ)^8269*100000000000000^6221 ≤ 43490605374599^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2672543537 5000000000 43490605374599 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264132831/10000000000 : ℝ)^8269 ≤ (1704690456491/4000000000000 : ℝ)^6221 := by
    have hnat : (5264132831 : ℕ)^8269*4000000000000^6221 ≤ 1704690456491^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264132831 10000000000 1704690456491 4000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453013443/2000000000 : ℝ)^8269 ≤ (3473033298553/25000000000000 : ℝ)^6221 := by
    have hnat : (453013443 : ℕ)^8269*25000000000000^6221 ≤ 3473033298553^6221*2000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453013443 2000000000 3473033298553 25000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2672543537/5000000000 : ℝ), (5264132831/10000000000 : ℝ), (-453013443/2000000000 : ℝ)] ![(43490605374599/100000000000000 : ℝ), (1704690456491/4000000000000 : ℝ), (3473033298553/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2672543537/5000000000 : ℝ)|^8269 ≤ (43490605374599/100000000000000 : ℝ)^6221
        have hw : |(2672543537/5000000000 : ℝ)|=(2672543537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264132831/10000000000 : ℝ)|^8269 ≤ (1704690456491/4000000000000 : ℝ)^6221
        have hw : |(5264132831/10000000000 : ℝ)|=(5264132831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-453013443/2000000000 : ℝ)|^8269 ≤ (3473033298553/25000000000000 : ℝ)^6221
        have hw : |(-453013443/2000000000 : ℝ)|=(453013443/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s6_3 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187014787/5000000000 : ℝ)*x 0 + (1061928581/2500000000 : ℝ)*x 1 + (4504143181/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187014787/5000000000 : ℝ)^8269 ≤ (16658169562409/50000000000000 : ℝ)^6221 := by
    have hnat : (2187014787 : ℕ)^8269*50000000000000^6221 ≤ 16658169562409^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187014787 5000000000 16658169562409 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1061928581/2500000000 : ℝ)^8269 ≤ (32043594608063/100000000000000 : ℝ)^6221 := by
    have hnat : (1061928581 : ℕ)^8269*100000000000000^6221 ≤ 32043594608063^6221*2500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061928581 2500000000 32043594608063 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504143181/10000000000 : ℝ)^8269 ≤ (34640066261739/100000000000000 : ℝ)^6221 := by
    have hnat : (4504143181 : ℕ)^8269*100000000000000^6221 ≤ 34640066261739^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504143181 10000000000 34640066261739 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187014787/5000000000 : ℝ), (1061928581/2500000000 : ℝ), (4504143181/10000000000 : ℝ)] ![(16658169562409/50000000000000 : ℝ), (32043594608063/100000000000000 : ℝ), (34640066261739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187014787/5000000000 : ℝ)|^8269 ≤ (16658169562409/50000000000000 : ℝ)^6221
        have hw : |(2187014787/5000000000 : ℝ)|=(2187014787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1061928581/2500000000 : ℝ)|^8269 ≤ (32043594608063/100000000000000 : ℝ)^6221
        have hw : |(1061928581/2500000000 : ℝ)|=(1061928581/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504143181/10000000000 : ℝ)|^8269 ≤ (34640066261739/100000000000000 : ℝ)^6221
        have hw : |(4504143181/10000000000 : ℝ)|=(4504143181/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s6_4 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-219881479/1000000000 : ℝ)*x 0 + (2632231187/5000000000 : ℝ)*x 1 + (2697191257/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219881479/1000000000 : ℝ)^8269 ≤ (13354640584787/100000000000000 : ℝ)^6221 := by
    have hnat : (219881479 : ℕ)^8269*100000000000000^6221 ≤ 13354640584787^6221*1000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219881479 1000000000 13354640584787 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632231187/5000000000 : ℝ)^8269 ≤ (42620807651717/100000000000000 : ℝ)^6221 := by
    have hnat : (2632231187 : ℕ)^8269*100000000000000^6221 ≤ 42620807651717^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632231187 5000000000 42620807651717 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697191257/5000000000 : ℝ)^8269 ≤ (44024551751003/100000000000000 : ℝ)^6221 := by
    have hnat : (2697191257 : ℕ)^8269*100000000000000^6221 ≤ 44024551751003^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697191257 5000000000 44024551751003 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219881479/1000000000 : ℝ), (2632231187/5000000000 : ℝ), (2697191257/5000000000 : ℝ)] ![(13354640584787/100000000000000 : ℝ), (42620807651717/100000000000000 : ℝ), (44024551751003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219881479/1000000000 : ℝ)|^8269 ≤ (13354640584787/100000000000000 : ℝ)^6221
        have hw : |(-219881479/1000000000 : ℝ)|=(219881479/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632231187/5000000000 : ℝ)|^8269 ≤ (42620807651717/100000000000000 : ℝ)^6221
        have hw : |(2632231187/5000000000 : ℝ)|=(2632231187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697191257/5000000000 : ℝ)|^8269 ≤ (44024551751003/100000000000000 : ℝ)^6221
        have hw : |(2697191257/5000000000 : ℝ)|=(2697191257/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s6_5 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656085339/5000000000 : ℝ)*x 0 + (-1067408627/5000000000 : ℝ)*x 1 + (5394382483/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656085339/5000000000 : ℝ)^8269 ≤ (4313497022867/10000000000000 : ℝ)^6221 := by
    have hnat : (2656085339 : ℕ)^8269*10000000000000^6221 ≤ 4313497022867^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656085339 5000000000 4313497022867 10000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1067408627/5000000000 : ℝ)^8269 ≤ (3210119586991/25000000000000 : ℝ)^6221 := by
    have hnat : (1067408627 : ℕ)^8269*25000000000000^6221 ≤ 3210119586991^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067408627 5000000000 3210119586991 25000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5394382483/10000000000 : ℝ)^8269 ≤ (22012275707359/50000000000000 : ℝ)^6221 := by
    have hnat : (5394382483 : ℕ)^8269*50000000000000^6221 ≤ 22012275707359^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394382483 10000000000 22012275707359 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656085339/5000000000 : ℝ), (-1067408627/5000000000 : ℝ), (5394382483/10000000000 : ℝ)] ![(4313497022867/10000000000000 : ℝ), (3210119586991/25000000000000 : ℝ), (22012275707359/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656085339/5000000000 : ℝ)|^8269 ≤ (4313497022867/10000000000000 : ℝ)^6221
        have hw : |(2656085339/5000000000 : ℝ)|=(2656085339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1067408627/5000000000 : ℝ)|^8269 ≤ (3210119586991/25000000000000 : ℝ)^6221
        have hw : |(-1067408627/5000000000 : ℝ)|=(1067408627/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5394382483/10000000000 : ℝ)|^8269 ≤ (22012275707359/50000000000000 : ℝ)^6221
        have hw : |(5394382483/10000000000 : ℝ)|=(5394382483/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s6_6 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312170541/10000000000 : ℝ)*x 0 + (1348595671/2500000000 : ℝ)*x 1 + (-1067408583/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312170541/10000000000 : ℝ)^8269 ≤ (43134968750001/100000000000000 : ℝ)^6221 := by
    have hnat : (5312170541 : ℕ)^8269*100000000000000^6221 ≤ 43134968750001^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312170541 10000000000 43134968750001 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348595671/2500000000 : ℝ)^8269 ≤ (44024553595147/100000000000000 : ℝ)^6221 := by
    have hnat : (1348595671 : ℕ)^8269*100000000000000^6221 ≤ 44024553595147^6221*2500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348595671 2500000000 44024553595147 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1067408583/5000000000 : ℝ)^8269 ≤ (3210119411103/25000000000000 : ℝ)^6221 := by
    have hnat : (1067408583 : ℕ)^8269*25000000000000^6221 ≤ 3210119411103^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067408583 5000000000 3210119411103 25000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312170541/10000000000 : ℝ), (1348595671/2500000000 : ℝ), (-1067408583/5000000000 : ℝ)] ![(43134968750001/100000000000000 : ℝ), (44024553595147/100000000000000 : ℝ), (3210119411103/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312170541/10000000000 : ℝ)|^8269 ≤ (43134968750001/100000000000000 : ℝ)^6221
        have hw : |(5312170541/10000000000 : ℝ)|=(5312170541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348595671/2500000000 : ℝ)|^8269 ≤ (44024553595147/100000000000000 : ℝ)^6221
        have hw : |(1348595671/2500000000 : ℝ)|=(1348595671/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1067408583/5000000000 : ℝ)|^8269 ≤ (3210119411103/25000000000000 : ℝ)^6221
        have hw : |(-1067408583/5000000000 : ℝ)|=(1067408583/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s6_7 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (6834437/15625000 : ℝ)*x 0 + (4503495427/10000000000 : ℝ)*x 1 + (2124182231/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6834437/15625000 : ℝ)^8269 ≤ (1665822072091/5000000000000 : ℝ)^6221 := by
    have hnat : (6834437 : ℕ)^8269*5000000000000^6221 ≤ 1665822072091^6221*15625000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6834437 15625000 1665822072091 5000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4503495427/10000000000 : ℝ)^8269 ≤ (865836117993/2500000000000 : ℝ)^6221 := by
    have hnat : (4503495427 : ℕ)^8269*2500000000000^6221 ≤ 865836117993^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503495427 10000000000 865836117993 2500000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124182231/5000000000 : ℝ)^8269 ≤ (16025056910827/50000000000000 : ℝ)^6221 := by
    have hnat : (2124182231 : ℕ)^8269*50000000000000^6221 ≤ 16025056910827^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124182231 5000000000 16025056910827 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6834437/15625000 : ℝ), (4503495427/10000000000 : ℝ), (2124182231/5000000000 : ℝ)] ![(1665822072091/5000000000000 : ℝ), (865836117993/2500000000000 : ℝ), (16025056910827/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6834437/15625000 : ℝ)|^8269 ≤ (1665822072091/5000000000000 : ℝ)^6221
        have hw : |(6834437/15625000 : ℝ)|=(6834437/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4503495427/10000000000 : ℝ)|^8269 ≤ (865836117993/2500000000000 : ℝ)^6221
        have hw : |(4503495427/10000000000 : ℝ)|=(4503495427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124182231/5000000000 : ℝ)|^8269 ≤ (16025056910827/50000000000000 : ℝ)^6221
        have hw : |(2124182231/5000000000 : ℝ)|=(2124182231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1076_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5627/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (701/5000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5607/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5607/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5607/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5607/50000 : ℝ) ^ (2067/512 : ℝ) ≤ (14580734937863249/100000000000000000000 : ℝ) := by
    have hpowers : (5607/50000 : ℝ)^2067 ≤ (14580734937863249/100000000000000000000 : ℝ)^512 := by
      have hnat : (5607 : ℕ)^2067*100000000000000000000^512 ≤ 14580734937863249^512*50000^2067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5607 50000 14580734937863249 100000000000000000000 2067 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5607/50000 : ℝ)) (X := (14580734937863249/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7031/50000 : ℝ) ^ (2067/512 : ℝ) ≤ (36355735448506639/100000000000000000000 : ℝ) := by
    have hpowers : (7031/50000 : ℝ)^2067 ≤ (36355735448506639/100000000000000000000 : ℝ)^512 := by
      have hnat : (7031 : ℕ)^2067*100000000000000000000^512 ≤ 36355735448506639^512*50000^2067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7031 50000 36355735448506639 100000000000000000000 2067 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7031/50000 : ℝ)) (X := (36355735448506639/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014580734937863249/50000000000000000000 : ℝ) ≤ (5000361128086627/5000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (50014580734937863249/50000000000000000000 : ℝ)^512 ≤ (5000361128086627/5000000000000000 : ℝ)^2067 := by
      have hnat : (50014580734937863249 : ℕ)^512*5000000000000000^2067 ≤ 5000361128086627^2067*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014580734937863249 50000000000000000000 5000361128086627 5000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000361128086627/5000000000000000 : ℝ)) (X := (50014580734937863249/50000000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126591764699574059/3125000000000000000 : ℝ) ≤ (5000630732403833/5000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (3126591764699574059/3125000000000000000 : ℝ)^512 ≤ (5000630732403833/5000000000000000 : ℝ)^2067 := by
      have hnat : (3126591764699574059 : ℕ)^512*5000000000000000^2067 ≤ 5000630732403833^2067*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126591764699574059 3125000000000000000 5000630732403833 5000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000630732403833/5000000000000000 : ℝ)) (X := (3126591764699574059/3125000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036355735448506639/50000000000000000000 : ℝ) ≤ (5000900336721039/5000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (50036355735448506639/50000000000000000000 : ℝ)^512 ≤ (5000900336721039/5000000000000000 : ℝ)^2067 := by
      have hnat : (50036355735448506639 : ℕ)^512*5000000000000000^2067 ≤ 5000900336721039^2067*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036355735448506639 50000000000000000000 5000900336721039 5000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000900336721039/5000000000000000 : ℝ)) (X := (50036355735448506639/50000000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14580734937863249/100000000000000000000 : ℝ) ≤ ((19992951976354519/20000000000000000 : ℝ)+2*(134802158603/71200000000000 : ℝ)*(5607/50000 : ℝ))^(2067/512 : ℝ) := by
    rw [show (19992951976354519/20000000000000000 : ℝ)+2*(134802158603/71200000000000 : ℝ)*(5607/50000 : ℝ)=(5000361128086627/5000000000000000 : ℝ) by norm_num, show 1+2*(14580734937863249/100000000000000000000 : ℝ)=(50014580734937863249/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36355735448506639/100000000000000000000 : ℝ)+(14580734937863249/100000000000000000000 : ℝ) ≤ ((19992951976354519/20000000000000000 : ℝ)+(134802158603/71200000000000 : ℝ)*((7031/50000 : ℝ)+(5607/50000 : ℝ)))^(2067/512 : ℝ) := by
    rw [show (19992951976354519/20000000000000000 : ℝ)+(134802158603/71200000000000 : ℝ)*((7031/50000 : ℝ)+(5607/50000 : ℝ))=(5000630732403833/5000000000000000 : ℝ) by norm_num, show 1+(36355735448506639/100000000000000000000 : ℝ)+(14580734937863249/100000000000000000000 : ℝ)=(3126591764699574059/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36355735448506639/100000000000000000000 : ℝ) ≤ ((19992951976354519/20000000000000000 : ℝ)+2*(134802158603/71200000000000 : ℝ)*(7031/50000 : ℝ))^(2067/512 : ℝ) := by
    rw [show (19992951976354519/20000000000000000 : ℝ)+2*(134802158603/71200000000000 : ℝ)*(7031/50000 : ℝ)=(5000900336721039/5000000000000000 : ℝ) by norm_num, show 1+2*(36355735448506639/100000000000000000000 : ℝ)=(50036355735448506639/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19992951976354519/20000000000000000 : ℝ)*(X 1 0+X 2 0)+(134802158603/71200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (19992951976354519/20000000000000000 : ℝ)) (alpha := (134802158603/71200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19992951976354519/20000000000000000 : ℝ)*(X 0 1+X 2 1)+(134802158603/71200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (19992951976354519/20000000000000000 : ℝ)) (alpha := (134802158603/71200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19992951976354519/20000000000000000 : ℝ)*(X 0 2+X 1 2)+(134802158603/71200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (5607/50000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (19992951976354519/20000000000000000 : ℝ)) (alpha := (134802158603/71200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-549702423/2500000000 : ℝ)*X 0 0+(539471353/1000000000 : ℝ)*X 0 1+(1316033127/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345087463/10000000000 : ℝ)*X 1 0+(-90602679/400000000 : ℝ)*X 1 1+(2632066311/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2672543537/5000000000 : ℝ)*X 2 0+(5264132831/10000000000 : ℝ)*X 2 1+(-453013443/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187014787/5000000000 : ℝ)*X 0 0+(1061928581/2500000000 : ℝ)*X 0 1+(4504143181/10000000000 : ℝ)*X 0 2+(2187014787/5000000000 : ℝ)*X 1 0+(1061928581/2500000000 : ℝ)*X 1 1+(4504143181/10000000000 : ℝ)*X 1 2+(2187014787/5000000000 : ℝ)*X 2 0+(1061928581/2500000000 : ℝ)*X 2 1+(4504143181/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219881479/1000000000 : ℝ)*X 0 0+(2632231187/5000000000 : ℝ)*X 0 1+(2697191257/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656085339/5000000000 : ℝ)*X 1 0+(-1067408627/5000000000 : ℝ)*X 1 1+(5394382483/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312170541/10000000000 : ℝ)*X 2 0+(1348595671/2500000000 : ℝ)*X 2 1+(-1067408583/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((6834437/15625000 : ℝ)*X 0 0+(4503495427/10000000000 : ℝ)*X 0 1+(2124182231/5000000000 : ℝ)*X 0 2+(6834437/15625000 : ℝ)*X 1 0+(4503495427/10000000000 : ℝ)*X 1 1+(2124182231/5000000000 : ℝ)*X 1 2+(6834437/15625000 : ℝ)*X 2 0+(4503495427/10000000000 : ℝ)*X 2 1+(2124182231/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (477588097642310094631850451/44500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2464993659/100000000000000 : ℝ)*(base19) + (1889060701/100000000000000 : ℝ)*(base23) + (518941457/100000000000000 : ℝ)*(upper3) + (310513/3125000000000 : ℝ)*(upper4) + (23758757/100000000000000 : ℝ)*(upper5) + (5779006943944213/100000000000000 : ℝ)*(major0) + (5779006943944213/100000000000000 : ℝ)*(major1) + (5779006943944213/100000000000000 : ℝ)*(major2) + (7658166159287491/100000000000000 : ℝ)*(sp0) + (957277522732527/12500000000000 : ℝ)*(sp1) + (3829110378896587/50000000000000 : ℝ)*(sp2) + (3899750363946409/100000000000000 : ℝ)*(sp3) + (11297513277/20000000000000 : ℝ)*(sp4) + (40519344241/100000000000000 : ℝ)*(sp7) + (77995817665813/2000000000000 : ℝ)*(f.failure) + (61265781174831/800000000000 : ℝ)*(f.sum) + (28295524836999/3560000000000000000000000000 : ℝ)*base65 + (60854406959104317/178000000000000000000000000000000 : ℝ)*base68 + (564228184852895683/178000000000000000000000000000000 : ℝ)*base69 + (500387601082895683/178000000000000000000000000000000 : ℝ)*base71 + (9885354724559/3560000000000000000000000000 : ℝ)*base73 + (112016152800895683/178000000000000000000000000000000 : ℝ)*base75 + (757996166578895683/178000000000000000000000000000000 : ℝ)*base77 + (1568923494468895683/178000000000000000000000000000000 : ℝ)*base79 + (23740191446721/3560000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1157257/200000000000000000000 : ℝ)*base90 + (1157257/200000000000000000000 : ℝ)*base92 + (1157257/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1250416290506899927833/445000000000000000000000000 : ℝ) := by norm_num
    linear_combination (638137057/100000000000000 : ℝ)*(base19) + (266573737/50000000000000 : ℝ)*(base23) + (7827443/25000000000000 : ℝ)*(upper2) + (79804393/100000000000000 : ℝ)*(upper3) + (16405947/20000000000000 : ℝ)*(upper5) + (726036758990671/12500000000000 : ℝ)*(major0) + (726036758990671/12500000000000 : ℝ)*(major1) + (726036758990671/12500000000000 : ℝ)*(major2) + (14605491457/100000000000000 : ℝ)*(sp1) + (10092786141/50000000000000 : ℝ)*(sp2) + (1924258405002159/25000000000000 : ℝ)*(sp4) + (3848509188190061/50000000000000 : ℝ)*(sp5) + (96212661266111/1250000000000 : ℝ)*(sp6) + (78391088603559/2000000000000 : ℝ)*(sp7) + (78391088603559/2000000000000 : ℝ)*(f.failure) + (1924258405002159/25000000000000 : ℝ)*(f.sum) + (1389883738413/445000000000000000000000000 : ℝ)*base65 + (54017246741435161/22250000000000000000000000000000 : ℝ)*base67 + (140694890461064839/22250000000000000000000000000000 : ℝ)*base70 + (169260547847185161/22250000000000000000000000000000 : ℝ)*base71 + (423236544449/222500000000000000000000000 : ℝ)*base73 + (221569686102064839/22250000000000000000000000000000 : ℝ)*base76 + (48153783584935161/22250000000000000000000000000000 : ℝ)*base77 + (167959486614064839/22250000000000000000000000000000 : ℝ)*base80 + (233046328063/445000000000000000000000000 : ℝ)*base81 + (1692451/200000000000000000000 : ℝ)*base90 + (1692451/200000000000000000000 : ℝ)*base92 + (1692451/200000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1076_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (701/5000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1076_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1076_s7_0 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-137428023/625000000 : ℝ)*x 0 + (5394271381/10000000000 : ℝ)*x 1 + (1316137303/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (137428023/625000000 : ℝ)^8269 ≤ (3338727915383/25000000000000 : ℝ)^6221 := by
    have hnat : (137428023 : ℕ)^8269*25000000000000^6221 ≤ 3338727915383^6221*625000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      137428023 625000000 3338727915383 25000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5394271381/10000000000 : ℝ)^8269 ≤ (1375729568579/3125000000000 : ℝ)^6221 := by
    have hnat : (5394271381 : ℕ)^8269*3125000000000^6221 ≤ 1375729568579^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5394271381 10000000000 1375729568579 3125000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316137303/2500000000 : ℝ)^8269 ≤ (21310871067387/50000000000000 : ℝ)^6221 := by
    have hnat : (1316137303 : ℕ)^8269*50000000000000^6221 ≤ 21310871067387^6221*2500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316137303 2500000000 21310871067387 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-137428023/625000000 : ℝ), (5394271381/10000000000 : ℝ), (1316137303/2500000000 : ℝ)] ![(3338727915383/25000000000000 : ℝ), (1375729568579/3125000000000 : ℝ), (21310871067387/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-137428023/625000000 : ℝ)|^8269 ≤ (3338727915383/25000000000000 : ℝ)^6221
        have hw : |(-137428023/625000000 : ℝ)|=(137428023/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5394271381/10000000000 : ℝ)|^8269 ≤ (1375729568579/3125000000000 : ℝ)^6221
        have hw : |(5394271381/10000000000 : ℝ)|=(5394271381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316137303/2500000000 : ℝ)|^8269 ≤ (21310871067387/50000000000000 : ℝ)^6221
        have hw : |(1316137303/2500000000 : ℝ)|=(1316137303/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s7_1 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344976597/10000000000 : ℝ)*x 0 + (-1132332307/5000000000 : ℝ)*x 1 + (5264548853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344976597/10000000000 : ℝ)^8269 ≤ (43489410550829/100000000000000 : ℝ)^6221 := by
    have hnat : (5344976597 : ℕ)^8269*100000000000000^6221 ≤ 43489410550829^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344976597 10000000000 43489410550829 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1132332307/5000000000 : ℝ)^8269 ≤ (13888851162467/100000000000000 : ℝ)^6221 := by
    have hnat : (1132332307 : ℕ)^8269*100000000000000^6221 ≤ 13888851162467^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1132332307 5000000000 13888851162467 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264548853/10000000000 : ℝ)^8269 ≤ (10655434567871/25000000000000 : ℝ)^6221 := by
    have hnat : (5264548853 : ℕ)^8269*25000000000000^6221 ≤ 10655434567871^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264548853 10000000000 10655434567871 25000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344976597/10000000000 : ℝ), (-1132332307/5000000000 : ℝ), (5264548853/10000000000 : ℝ)] ![(43489410550829/100000000000000 : ℝ), (13888851162467/100000000000000 : ℝ), (10655434567871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344976597/10000000000 : ℝ)|^8269 ≤ (43489410550829/100000000000000 : ℝ)^6221
        have hw : |(5344976597/10000000000 : ℝ)|=(5344976597/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1132332307/5000000000 : ℝ)|^8269 ≤ (13888851162467/100000000000000 : ℝ)^6221
        have hw : |(-1132332307/5000000000 : ℝ)|=(1132332307/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264548853/10000000000 : ℝ)|^8269 ≤ (10655434567871/25000000000000 : ℝ)^6221
        have hw : |(5264548853/10000000000 : ℝ)|=(5264548853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s7_2 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (213799061/400000000 : ℝ)*x 0 + (526454917/1000000000 : ℝ)*x 1 + (-566166073/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (213799061/400000000 : ℝ)^8269 ≤ (43489409772141/100000000000000 : ℝ)^6221 := by
    have hnat : (213799061 : ℕ)^8269*100000000000000^6221 ≤ 43489409772141^6221*400000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213799061 400000000 43489409772141 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526454917/1000000000 : ℝ)^8269 ≤ (42621741682801/100000000000000 : ℝ)^6221 := by
    have hnat : (526454917 : ℕ)^8269*100000000000000^6221 ≤ 42621741682801^6221*1000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526454917 1000000000 42621741682801 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566166073/2500000000 : ℝ)^8269 ≤ (13888848537577/100000000000000 : ℝ)^6221 := by
    have hnat : (566166073 : ℕ)^8269*100000000000000^6221 ≤ 13888848537577^6221*2500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566166073 2500000000 13888848537577 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(213799061/400000000 : ℝ), (526454917/1000000000 : ℝ), (-566166073/2500000000 : ℝ)] ![(43489409772141/100000000000000 : ℝ), (42621741682801/100000000000000 : ℝ), (13888848537577/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(213799061/400000000 : ℝ)|^8269 ≤ (43489409772141/100000000000000 : ℝ)^6221
        have hw : |(213799061/400000000 : ℝ)|=(213799061/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526454917/1000000000 : ℝ)|^8269 ≤ (42621741682801/100000000000000 : ℝ)^6221
        have hw : |(526454917/1000000000 : ℝ)|=(526454917/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-566166073/2500000000 : ℝ)|^8269 ≤ (13888848537577/100000000000000 : ℝ)^6221
        have hw : |(-566166073/2500000000 : ℝ)|=(566166073/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s7_3 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187025917/5000000000 : ℝ)*x 0 + (53106923/125000000 : ℝ)*x 1 + (450329761/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187025917/5000000000 : ℝ)^8269 ≤ (1665828224683/5000000000000 : ℝ)^6221 := by
    have hnat : (2187025917 : ℕ)^8269*5000000000000^6221 ≤ 1665828224683^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187025917 5000000000 1665828224683 5000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53106923/125000000 : ℝ)^8269 ≤ (32052012858153/100000000000000 : ℝ)^6221 := by
    have hnat : (53106923 : ℕ)^8269*100000000000000^6221 ≤ 32052012858153^6221*125000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53106923 125000000 32052012858153 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (450329761/1000000000 : ℝ)^8269 ≤ (34631422635569/100000000000000 : ℝ)^6221 := by
    have hnat : (450329761 : ℕ)^8269*100000000000000^6221 ≤ 34631422635569^6221*1000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      450329761 1000000000 34631422635569 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187025917/5000000000 : ℝ), (53106923/125000000 : ℝ), (450329761/1000000000 : ℝ)] ![(1665828224683/5000000000000 : ℝ), (32052012858153/100000000000000 : ℝ), (34631422635569/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187025917/5000000000 : ℝ)|^8269 ≤ (1665828224683/5000000000000 : ℝ)^6221
        have hw : |(2187025917/5000000000 : ℝ)|=(2187025917/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(53106923/125000000 : ℝ)|^8269 ≤ (32052012858153/100000000000000 : ℝ)^6221
        have hw : |(53106923/125000000 : ℝ)|=(53106923/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(450329761/1000000000 : ℝ)|^8269 ≤ (34631422635569/100000000000000 : ℝ)^6221
        have hw : |(450329761/1000000000 : ℝ)|=(450329761/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s7_4 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1099426799/5000000000 : ℝ)*x 0 + (2632437167/5000000000 : ℝ)*x 1 + (2696972477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099426799/5000000000 : ℝ)^8269 ≤ (6677476941843/50000000000000 : ℝ)^6221 := by
    have hnat : (1099426799 : ℕ)^8269*50000000000000^6221 ≤ 6677476941843^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099426799 5000000000 6677476941843 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632437167/5000000000 : ℝ)^8269 ≤ (10656310222521/25000000000000 : ℝ)^6221 := by
    have hnat : (2632437167 : ℕ)^8269*25000000000000^6221 ≤ 10656310222521^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632437167 5000000000 10656310222521 25000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696972477/5000000000 : ℝ)^8269 ≤ (22009902601871/50000000000000 : ℝ)^6221 := by
    have hnat : (2696972477 : ℕ)^8269*50000000000000^6221 ≤ 22009902601871^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696972477 5000000000 22009902601871 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1099426799/5000000000 : ℝ), (2632437167/5000000000 : ℝ), (2696972477/5000000000 : ℝ)] ![(6677476941843/50000000000000 : ℝ), (10656310222521/25000000000000 : ℝ), (22009902601871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1099426799/5000000000 : ℝ)|^8269 ≤ (6677476941843/50000000000000 : ℝ)^6221
        have hw : |(-1099426799/5000000000 : ℝ)|=(1099426799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632437167/5000000000 : ℝ)|^8269 ≤ (10656310222521/25000000000000 : ℝ)^6221
        have hw : |(2632437167/5000000000 : ℝ)|=(2632437167/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696972477/5000000000 : ℝ)|^8269 ≤ (22009902601871/50000000000000 : ℝ)^6221
        have hw : |(2696972477/5000000000 : ℝ)|=(2696972477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s7_5 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062455261/2000000000 : ℝ)*x 0 + (-1067634147/5000000000 : ℝ)*x 1 + (2696972477/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062455261/2000000000 : ℝ)^8269 ≤ (5392013785733/12500000000000 : ℝ)^6221 := by
    have hnat : (1062455261 : ℕ)^8269*12500000000000^6221 ≤ 5392013785733^6221*2000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062455261 2000000000 5392013785733 12500000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1067634147/5000000000 : ℝ)^8269 ≤ (3211021123791/25000000000000 : ℝ)^6221 := by
    have hnat : (1067634147 : ℕ)^8269*25000000000000^6221 ≤ 3211021123791^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067634147 5000000000 3211021123791 25000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696972477/5000000000 : ℝ)^8269 ≤ (22009902601871/50000000000000 : ℝ)^6221 := by
    have hnat : (2696972477 : ℕ)^8269*50000000000000^6221 ≤ 22009902601871^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696972477 5000000000 22009902601871 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062455261/2000000000 : ℝ), (-1067634147/5000000000 : ℝ), (2696972477/5000000000 : ℝ)] ![(5392013785733/12500000000000 : ℝ), (3211021123791/25000000000000 : ℝ), (22009902601871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062455261/2000000000 : ℝ)|^8269 ≤ (5392013785733/12500000000000 : ℝ)^6221
        have hw : |(1062455261/2000000000 : ℝ)|=(1062455261/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1067634147/5000000000 : ℝ)|^8269 ≤ (3211021123791/25000000000000 : ℝ)^6221
        have hw : |(-1067634147/5000000000 : ℝ)|=(1067634147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696972477/5000000000 : ℝ)|^8269 ≤ (22009902601871/50000000000000 : ℝ)^6221
        have hw : |(2696972477/5000000000 : ℝ)|=(2696972477/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s7_6 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312276307/10000000000 : ℝ)*x 0 + (5393944953/10000000000 : ℝ)*x 1 + (-2135268293/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312276307/10000000000 : ℝ)^8269 ≤ (862722206149/2000000000000 : ℝ)^6221 := by
    have hnat : (5312276307 : ℕ)^8269*2000000000000^6221 ≤ 862722206149^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312276307 10000000000 862722206149 2000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393944953/10000000000 : ℝ)^8269 ≤ (8803961038579/20000000000000 : ℝ)^6221 := by
    have hnat : (5393944953 : ℕ)^8269*20000000000000^6221 ≤ 8803961038579^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393944953 10000000000 8803961038579 20000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2135268293/10000000000 : ℝ)^8269 ≤ (12844084487169/100000000000000 : ℝ)^6221 := by
    have hnat : (2135268293 : ℕ)^8269*100000000000000^6221 ≤ 12844084487169^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2135268293 10000000000 12844084487169 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312276307/10000000000 : ℝ), (5393944953/10000000000 : ℝ), (-2135268293/10000000000 : ℝ)] ![(862722206149/2000000000000 : ℝ), (8803961038579/20000000000000 : ℝ), (12844084487169/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312276307/10000000000 : ℝ)|^8269 ≤ (862722206149/2000000000000 : ℝ)^6221
        have hw : |(5312276307/10000000000 : ℝ)|=(5312276307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393944953/10000000000 : ℝ)|^8269 ≤ (8803961038579/20000000000000 : ℝ)^6221
        have hw : |(5393944953/10000000000 : ℝ)|=(5393944953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2135268293/10000000000 : ℝ)|^8269 ≤ (12844084487169/100000000000000 : ℝ)^6221
        have hw : |(-2135268293/10000000000 : ℝ)|=(2135268293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s7_7 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374061463/10000000000 : ℝ)*x 0 + (4502658393/10000000000 : ℝ)*x 1 + (169967827/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374061463/10000000000 : ℝ)^8269 ≤ (16658330990747/50000000000000 : ℝ)^6221 := by
    have hnat : (4374061463 : ℕ)^8269*50000000000000^6221 ≤ 16658330990747^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374061463 10000000000 16658330990747 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502658393/10000000000 : ℝ)^8269 ≤ (1731244438163/5000000000000 : ℝ)^6221 := by
    have hnat : (4502658393 : ℕ)^8269*5000000000000^6221 ≤ 1731244438163^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502658393 10000000000 1731244438163 5000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169967827/400000000 : ℝ)^8269 ≤ (32058449230609/100000000000000 : ℝ)^6221 := by
    have hnat : (169967827 : ℕ)^8269*100000000000000^6221 ≤ 32058449230609^6221*400000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169967827 400000000 32058449230609 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374061463/10000000000 : ℝ), (4502658393/10000000000 : ℝ), (169967827/400000000 : ℝ)] ![(16658330990747/50000000000000 : ℝ), (1731244438163/5000000000000 : ℝ), (32058449230609/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374061463/10000000000 : ℝ)|^8269 ≤ (16658330990747/50000000000000 : ℝ)^6221
        have hw : |(4374061463/10000000000 : ℝ)|=(4374061463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502658393/10000000000 : ℝ)|^8269 ≤ (1731244438163/5000000000000 : ℝ)^6221
        have hw : |(4502658393/10000000000 : ℝ)|=(4502658393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169967827/400000000 : ℝ)|^8269 ≤ (32058449230609/100000000000000 : ℝ)^6221
        have hw : |(169967827/400000000 : ℝ)|=(169967827/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1076_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11263/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14011/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (701/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5627/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (701/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5627/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (701/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5627/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (701/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5627/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (701/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5627/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (701/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5627/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5627/50000 : ℝ) ^ (2067/512 : ℝ) ≤ (3697960299336369/25000000000000000000 : ℝ) := by
    have hpowers : (5627/50000 : ℝ)^2067 ≤ (3697960299336369/25000000000000000000 : ℝ)^512 := by
      have hnat : (5627 : ℕ)^2067*25000000000000000000^512 ≤ 3697960299336369^512*50000^2067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5627 50000 3697960299336369 25000000000000000000 2067 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5627/50000 : ℝ)) (X := (3697960299336369/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hpowhi : (701/5000 : ℝ) ^ (2067/512 : ℝ) ≤ (8979836208919081/25000000000000000000 : ℝ) := by
    have hpowers : (701/5000 : ℝ)^2067 ≤ (8979836208919081/25000000000000000000 : ℝ)^512 := by
      have hnat : (701 : ℕ)^2067*25000000000000000000^512 ≤ 8979836208919081^512*5000^2067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        701 5000 8979836208919081 25000000000000000000 2067 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (701/5000 : ℝ)) (X := (8979836208919081/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503697960299336369/12500000000000000000 : ℝ) ≤ (10000732712150731/10000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (12503697960299336369/12500000000000000000 : ℝ)^512 ≤ (10000732712150731/10000000000000000 : ℝ)^2067 := by
      have hnat : (12503697960299336369 : ℕ)^512*10000000000000000^2067 ≤ 10000732712150731^2067*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503697960299336369 12500000000000000000 10000732712150731 10000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000732712150731/10000000000000000 : ℝ)) (X := (12503697960299336369/12500000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (500253555930165109/500000000000000000 : ℝ) ≤ (10001255886602221/10000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (500253555930165109/500000000000000000 : ℝ)^512 ≤ (10001255886602221/10000000000000000 : ℝ)^2067 := by
      have hnat : (500253555930165109 : ℕ)^512*10000000000000000^2067 ≤ 10001255886602221^2067*500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        500253555930165109 500000000000000000 10001255886602221 10000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001255886602221/10000000000000000 : ℝ)) (X := (500253555930165109/500000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508979836208919081/12500000000000000000 : ℝ) ≤ (10001779061053711/10000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (12508979836208919081/12500000000000000000 : ℝ)^512 ≤ (10001779061053711/10000000000000000 : ℝ)^2067 := by
      have hnat : (12508979836208919081 : ℕ)^512*10000000000000000^2067 ≤ 10001779061053711^2067*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508979836208919081 12500000000000000000 10001779061053711 10000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001779061053711/10000000000000000 : ℝ)) (X := (12508979836208919081/12500000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3697960299336369/25000000000000000000 : ℝ) ≤ ((4608375178542464171/4610000000000000000 : ℝ)+2*(17439148383/9220000000000 : ℝ)*(5627/50000 : ℝ))^(2067/512 : ℝ) := by
    rw [show (4608375178542464171/4610000000000000000 : ℝ)+2*(17439148383/9220000000000 : ℝ)*(5627/50000 : ℝ)=(10000732712150731/10000000000000000 : ℝ) by norm_num, show 1+2*(3697960299336369/25000000000000000000 : ℝ)=(12503697960299336369/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8979836208919081/25000000000000000000 : ℝ)+(3697960299336369/25000000000000000000 : ℝ) ≤ ((4608375178542464171/4610000000000000000 : ℝ)+(17439148383/9220000000000 : ℝ)*((701/5000 : ℝ)+(5627/50000 : ℝ)))^(2067/512 : ℝ) := by
    rw [show (4608375178542464171/4610000000000000000 : ℝ)+(17439148383/9220000000000 : ℝ)*((701/5000 : ℝ)+(5627/50000 : ℝ))=(10001255886602221/10000000000000000 : ℝ) by norm_num, show 1+(8979836208919081/25000000000000000000 : ℝ)+(3697960299336369/25000000000000000000 : ℝ)=(500253555930165109/500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8979836208919081/25000000000000000000 : ℝ) ≤ ((4608375178542464171/4610000000000000000 : ℝ)+2*(17439148383/9220000000000 : ℝ)*(701/5000 : ℝ))^(2067/512 : ℝ) := by
    rw [show (4608375178542464171/4610000000000000000 : ℝ)+2*(17439148383/9220000000000 : ℝ)*(701/5000 : ℝ)=(10001779061053711/10000000000000000 : ℝ) by norm_num, show 1+2*(8979836208919081/25000000000000000000 : ℝ)=(12508979836208919081/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4608375178542464171/4610000000000000000 : ℝ)*(X 1 0+X 2 0)+(17439148383/9220000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (5627/50000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (4608375178542464171/4610000000000000000 : ℝ)) (alpha := (17439148383/9220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4608375178542464171/4610000000000000000 : ℝ)*(X 0 1+X 2 1)+(17439148383/9220000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (5627/50000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (4608375178542464171/4610000000000000000 : ℝ)) (alpha := (17439148383/9220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4608375178542464171/4610000000000000000 : ℝ)*(X 0 2+X 1 2)+(17439148383/9220000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (5627/50000 : ℝ)) (hi := (701/5000 : ℝ)) (c := (4608375178542464171/4610000000000000000 : ℝ)) (alpha := (17439148383/9220000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-137428023/625000000 : ℝ)*X 0 0+(5394271381/10000000000 : ℝ)*X 0 1+(1316137303/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344976597/10000000000 : ℝ)*X 1 0+(-1132332307/5000000000 : ℝ)*X 1 1+(5264548853/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((213799061/400000000 : ℝ)*X 2 0+(526454917/1000000000 : ℝ)*X 2 1+(-566166073/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187025917/5000000000 : ℝ)*X 0 0+(53106923/125000000 : ℝ)*X 0 1+(450329761/1000000000 : ℝ)*X 0 2+(2187025917/5000000000 : ℝ)*X 1 0+(53106923/125000000 : ℝ)*X 1 1+(450329761/1000000000 : ℝ)*X 1 2+(2187025917/5000000000 : ℝ)*X 2 0+(53106923/125000000 : ℝ)*X 2 1+(450329761/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1099426799/5000000000 : ℝ)*X 0 0+(2632437167/5000000000 : ℝ)*X 0 1+(2696972477/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062455261/2000000000 : ℝ)*X 1 0+(-1067634147/5000000000 : ℝ)*X 1 1+(2696972477/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312276307/10000000000 : ℝ)*X 2 0+(5393944953/10000000000 : ℝ)*X 2 1+(-2135268293/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4374061463/10000000000 : ℝ)*X 0 0+(4502658393/10000000000 : ℝ)*X 0 1+(169967827/400000000 : ℝ)*X 0 2+(4374061463/10000000000 : ℝ)*X 1 0+(4502658393/10000000000 : ℝ)*X 1 1+(169967827/400000000 : ℝ)*X 1 2+(4374061463/10000000000 : ℝ)*X 2 0+(4502658393/10000000000 : ℝ)*X 2 1+(169967827/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (330092267275446715707807879/28812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (455941209/25000000000000 : ℝ)*(base19) + (68077001/6250000000000 : ℝ)*(base23) + (67420501/20000000000000 : ℝ)*(lower2) + (2721157/1250000000000 : ℝ)*(upper3) + (11835443/5000000000000 : ℝ)*(upper5) + (727149509318817/12500000000000 : ℝ)*(major0) + (727149509318817/12500000000000 : ℝ)*(major1) + (727149509318817/12500000000000 : ℝ)*(major2) + (308352062127093/4000000000000 : ℝ)*(sp0) + (7708828261677941/100000000000000 : ℝ)*(sp1) + (7708828996210761/100000000000000 : ℝ)*(sp2) + (245346005024011/6250000000000 : ℝ)*(sp3) + (7133066363/25000000000000 : ℝ)*(sp4) + (12800694313/50000000000000 : ℝ)*(sp7) + (3925561681772801/100000000000000 : ℝ)*(f.failure) + (7708830085442777/100000000000000 : ℝ)*(f.sum) + (1056660828699/230500000000000000000000000 : ℝ)*base66 + (278061948469769293/57625000000000000000000000000000 : ℝ)*base68 + (237742862881855707/57625000000000000000000000000000 : ℝ)*base69 + (332150685176730707/57625000000000000000000000000000 : ℝ)*base71 + (928045922359/115250000000000000000000000 : ℝ)*base74 + (1186632150176269293/57625000000000000000000000000000 : ℝ)*base76 + (625966802323230707/57625000000000000000000000000000 : ℝ)*base77 + (183383286655605707/57625000000000000000000000000000 : ℝ)*base79 + (86623320349/46100000000000000000000000 : ℝ)*base82 + (24968411/10000000000000000000000 : ℝ)*base89 + (24968411/10000000000000000000000 : ℝ)*base91 + (24968411/10000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (249052972491244086083250711/46100000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (99475687/10000000000000 : ℝ)*(base19) + (1088323673/100000000000000 : ℝ)*(base23) + (21624351/20000000000000 : ℝ)*(upper3) + (1637239/4000000000000 : ℝ)*(lower4) + (54812769/50000000000000 : ℝ)*(upper5) + (1169304885000247/20000000000000 : ℝ)*(major0) + (1169304885000247/20000000000000 : ℝ)*(major1) + (1169304885000247/20000000000000 : ℝ)*(major2) + (5410808087/20000000000000 : ℝ)*(sp1) + (5852698577/20000000000000 : ℝ)*(sp2) + (3873847811751831/50000000000000 : ℝ)*(sp4) + (3873833787353179/50000000000000 : ℝ)*(sp5) + (121057269870111/1562500000000 : ℝ)*(sp6) + (394535304641711/10000000000000 : ℝ)*(sp7) + (394535304641711/10000000000000 : ℝ)*(f.failure) + (3873847811751831/50000000000000 : ℝ)*(f.sum) + (952423512111/461000000000000000000000000 : ℝ)*base65 + (43964766460550237/92200000000000000000000000000000 : ℝ)*base67 + (2617231996951449763/92200000000000000000000000000000 : ℝ)*base70 + (670462006118849763/92200000000000000000000000000000 : ℝ)*base72 + (2366279240637/461000000000000000000000000 : ℝ)*base73 + (3300919617947249763/92200000000000000000000000000000 : ℝ)*base76 + (488203136108449763/92200000000000000000000000000000 : ℝ)*base78 + (23235398601750237/92200000000000000000000000000000 : ℝ)*base79 + (2686842935033/461000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (14042421/1000000000000000000000 : ℝ)*base89 + (14042421/1000000000000000000000 : ℝ)*base91 + (14042421/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1076_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (701/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5627/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1076_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1076_s8_0 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-87954219/400000000 : ℝ)*x 0 + (84284011/156250000 : ℝ)*x 1 + (5264639317/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (87954219/400000000 : ℝ)^8269 ≤ (6677484518423/50000000000000 : ℝ)^6221 := by
    have hnat : (87954219 : ℕ)^8269*50000000000000^6221 ≤ 6677484518423^6221*400000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87954219 400000000 6677484518423 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (84284011/156250000 : ℝ)^8269 ≤ (44022319157073/100000000000000 : ℝ)^6221 := by
    have hnat : (84284011 : ℕ)^8269*100000000000000^6221 ≤ 44022319157073^6221*156250000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84284011 156250000 44022319157073 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264639317/10000000000 : ℝ)^8269 ≤ (42622711780109/100000000000000 : ℝ)^6221 := by
    have hnat : (5264639317 : ℕ)^8269*100000000000000^6221 ≤ 42622711780109^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264639317 10000000000 42622711780109 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-87954219/400000000 : ℝ), (84284011/156250000 : ℝ), (5264639317/10000000000 : ℝ)] ![(6677484518423/50000000000000 : ℝ), (44022319157073/100000000000000 : ℝ), (42622711780109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-87954219/400000000 : ℝ)|^8269 ≤ (6677484518423/50000000000000 : ℝ)^6221
        have hw : |(-87954219/400000000 : ℝ)|=(87954219/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(84284011/156250000 : ℝ)|^8269 ≤ (44022319157073/100000000000000 : ℝ)^6221
        have hw : |(84284011/156250000 : ℝ)|=(84284011/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264639317/10000000000 : ℝ)|^8269 ≤ (42622711780109/100000000000000 : ℝ)^6221
        have hw : |(5264639317/10000000000 : ℝ)|=(5264639317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s8_1 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068990687/2000000000 : ℝ)*x 0 + (-566143979/2500000000 : ℝ)*x 1 + (131615983/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068990687/2000000000 : ℝ)^8269 ≤ (43489160051681/100000000000000 : ℝ)^6221 := by
    have hnat : (1068990687 : ℕ)^8269*100000000000000^6221 ≤ 43489160051681^6221*2000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068990687 2000000000 43489160051681 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (566143979/2500000000 : ℝ)^8269 ≤ (6944064057967/50000000000000 : ℝ)^6221 := by
    have hnat : (566143979 : ℕ)^8269*50000000000000^6221 ≤ 6944064057967^6221*2500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566143979 2500000000 6944064057967 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131615983/250000000 : ℝ)^8269 ≤ (42622711812393/100000000000000 : ℝ)^6221 := by
    have hnat : (131615983 : ℕ)^8269*100000000000000^6221 ≤ 42622711812393^6221*250000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131615983 250000000 42622711812393 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068990687/2000000000 : ℝ), (-566143979/2500000000 : ℝ), (131615983/250000000 : ℝ)] ![(43489160051681/100000000000000 : ℝ), (6944064057967/50000000000000 : ℝ), (42622711812393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068990687/2000000000 : ℝ)|^8269 ≤ (43489160051681/100000000000000 : ℝ)^6221
        have hw : |(1068990687/2000000000 : ℝ)|=(1068990687/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-566143979/2500000000 : ℝ)|^8269 ≤ (6944064057967/50000000000000 : ℝ)^6221
        have hw : |(-566143979/2500000000 : ℝ)|=(566143979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131615983/250000000 : ℝ)|^8269 ≤ (42622711812393/100000000000000 : ℝ)^6221
        have hw : |(131615983/250000000 : ℝ)|=(131615983/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s8_2 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344953431/10000000000 : ℝ)*x 0 + (164519979/312500000 : ℝ)*x 1 + (-283071989/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344953431/10000000000 : ℝ)^8269 ≤ (43489160008421/100000000000000 : ℝ)^6221 := by
    have hnat : (5344953431 : ℕ)^8269*100000000000000^6221 ≤ 43489160008421^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344953431 10000000000 43489160008421 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164519979/312500000 : ℝ)^8269 ≤ (42622711898483/100000000000000 : ℝ)^6221 := by
    have hnat : (164519979 : ℕ)^8269*100000000000000^6221 ≤ 42622711898483^6221*312500000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164519979 312500000 42622711898483 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (283071989/1250000000 : ℝ)^8269 ≤ (13888128083327/100000000000000 : ℝ)^6221 := by
    have hnat : (283071989 : ℕ)^8269*100000000000000^6221 ≤ 13888128083327^6221*1250000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      283071989 1250000000 13888128083327 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344953431/10000000000 : ℝ), (164519979/312500000 : ℝ), (-283071989/1250000000 : ℝ)] ![(43489160008421/100000000000000 : ℝ), (42622711898483/100000000000000 : ℝ), (13888128083327/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344953431/10000000000 : ℝ)|^8269 ≤ (43489160008421/100000000000000 : ℝ)^6221
        have hw : |(5344953431/10000000000 : ℝ)|=(5344953431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164519979/312500000 : ℝ)|^8269 ≤ (42622711898483/100000000000000 : ℝ)^6221
        have hw : |(164519979/312500000 : ℝ)|=(164519979/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-283071989/1250000000 : ℝ)|^8269 ≤ (13888128083327/100000000000000 : ℝ)^6221
        have hw : |(-283071989/1250000000 : ℝ)|=(283071989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s8_3 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (874811249/2000000000 : ℝ)*x 0 + (2124367799/5000000000 : ℝ)*x 1 + (4503114931/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (874811249/2000000000 : ℝ)^8269 ≤ (33316609152373/100000000000000 : ℝ)^6221 := by
    have hnat : (874811249 : ℕ)^8269*100000000000000^6221 ≤ 33316609152373^6221*2000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      874811249 2000000000 33316609152373 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2124367799/5000000000 : ℝ)^8269 ≤ (16026917754677/50000000000000 : ℝ)^6221 := by
    have hnat : (2124367799 : ℕ)^8269*50000000000000^6221 ≤ 16026917754677^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124367799 5000000000 16026917754677 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503114931/10000000000 : ℝ)^8269 ≤ (34629555317931/100000000000000 : ℝ)^6221 := by
    have hnat : (4503114931 : ℕ)^8269*100000000000000^6221 ≤ 34629555317931^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503114931 10000000000 34629555317931 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(874811249/2000000000 : ℝ), (2124367799/5000000000 : ℝ), (4503114931/10000000000 : ℝ)] ![(33316609152373/100000000000000 : ℝ), (16026917754677/50000000000000 : ℝ), (34629555317931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(874811249/2000000000 : ℝ)|^8269 ≤ (33316609152373/100000000000000 : ℝ)^6221
        have hw : |(874811249/2000000000 : ℝ)|=(874811249/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2124367799/5000000000 : ℝ)|^8269 ≤ (16026917754677/50000000000000 : ℝ)^6221
        have hw : |(2124367799/5000000000 : ℝ)|=(2124367799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503114931/10000000000 : ℝ)|^8269 ≤ (34629555317931/100000000000000 : ℝ)^6221
        have hw : |(4503114931/10000000000 : ℝ)|=(4503114931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s8_4 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1099430181/5000000000 : ℝ)*x 0 + (1316241007/2500000000 : ℝ)*x 1 + (5393850939/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1099430181/5000000000 : ℝ)^8269 ≤ (6677504244989/50000000000000 : ℝ)^6221 := by
    have hnat : (1099430181 : ℕ)^8269*50000000000000^6221 ≤ 6677504244989^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1099430181 5000000000 6677504244989 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316241007/2500000000 : ℝ)^8269 ≤ (42626206132143/100000000000000 : ℝ)^6221 := by
    have hnat : (1316241007 : ℕ)^8269*100000000000000^6221 ≤ 42626206132143^6221*2500000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316241007 2500000000 42626206132143 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393850939/10000000000 : ℝ)^8269 ≤ (4401878536783/10000000000000 : ℝ)^6221 := by
    have hnat : (5393850939 : ℕ)^8269*10000000000000^6221 ≤ 4401878536783^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393850939 10000000000 4401878536783 10000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1099430181/5000000000 : ℝ), (1316241007/2500000000 : ℝ), (5393850939/10000000000 : ℝ)] ![(6677504244989/50000000000000 : ℝ), (42626206132143/100000000000000 : ℝ), (4401878536783/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1099430181/5000000000 : ℝ)|^8269 ≤ (6677504244989/50000000000000 : ℝ)^6221
        have hw : |(-1099430181/5000000000 : ℝ)|=(1099430181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316241007/2500000000 : ℝ)|^8269 ≤ (42626206132143/100000000000000 : ℝ)^6221
        have hw : |(1316241007/2500000000 : ℝ)|=(1316241007/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393850939/10000000000 : ℝ)|^8269 ≤ (4401878536783/10000000000000 : ℝ)^6221
        have hw : |(5393850939/10000000000 : ℝ)|=(5393850939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s8_5 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062459867/2000000000 : ℝ)*x 0 + (-42707303/200000000 : ℝ)*x 1 + (5393850649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062459867/2000000000 : ℝ)^8269 ≤ (10784089713773/25000000000000 : ℝ)^6221 := by
    have hnat : (1062459867 : ℕ)^8269*25000000000000^6221 ≤ 10784089713773^6221*2000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062459867 2000000000 10784089713773 25000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42707303/200000000 : ℝ)^8269 ≤ (1605607363661/12500000000000 : ℝ)^6221 := by
    have hnat : (42707303 : ℕ)^8269*12500000000000^6221 ≤ 1605607363661^6221*200000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42707303 200000000 1605607363661 12500000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393850649/10000000000 : ℝ)^8269 ≤ (22009391111019/50000000000000 : ℝ)^6221 := by
    have hnat : (5393850649 : ℕ)^8269*50000000000000^6221 ≤ 22009391111019^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393850649 10000000000 22009391111019 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062459867/2000000000 : ℝ), (-42707303/200000000 : ℝ), (5393850649/10000000000 : ℝ)] ![(10784089713773/25000000000000 : ℝ), (1605607363661/12500000000000 : ℝ), (22009391111019/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062459867/2000000000 : ℝ)|^8269 ≤ (10784089713773/25000000000000 : ℝ)^6221
        have hw : |(1062459867/2000000000 : ℝ)|=(1062459867/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-42707303/200000000 : ℝ)|^8269 ≤ (1605607363661/12500000000000 : ℝ)^6221
        have hw : |(-42707303/200000000 : ℝ)|=(42707303/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393850649/10000000000 : ℝ)|^8269 ≤ (22009391111019/50000000000000 : ℝ)^6221
        have hw : |(5393850649/10000000000 : ℝ)|=(5393850649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s8_6 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312300529/10000000000 : ℝ)*x 0 + (215754027/400000000 : ℝ)*x 1 + (-1067681751/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312300529/10000000000 : ℝ)^8269 ≤ (43136371742277/100000000000000 : ℝ)^6221 := by
    have hnat : (5312300529 : ℕ)^8269*100000000000000^6221 ≤ 43136371742277^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312300529 10000000000 43136371742277 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215754027/400000000 : ℝ)^8269 ≤ (1760751300163/4000000000000 : ℝ)^6221 := by
    have hnat : (215754027 : ℕ)^8269*4000000000000^6221 ≤ 1760751300163^6221*400000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215754027 400000000 1760751300163 4000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1067681751/5000000000 : ℝ)^8269 ≤ (6422422866287/50000000000000 : ℝ)^6221 := by
    have hnat : (1067681751 : ℕ)^8269*50000000000000^6221 ≤ 6422422866287^6221*5000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1067681751 5000000000 6422422866287 50000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312300529/10000000000 : ℝ), (215754027/400000000 : ℝ), (-1067681751/5000000000 : ℝ)] ![(43136371742277/100000000000000 : ℝ), (1760751300163/4000000000000 : ℝ), (6422422866287/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312300529/10000000000 : ℝ)|^8269 ≤ (43136371742277/100000000000000 : ℝ)^6221
        have hw : |(5312300529/10000000000 : ℝ)|=(5312300529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215754027/400000000 : ℝ)|^8269 ≤ (1760751300163/4000000000000 : ℝ)^6221
        have hw : |(215754027/400000000 : ℝ)|=(215754027/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1067681751/5000000000 : ℝ)|^8269 ≤ (6422422866287/50000000000000 : ℝ)^6221
        have hw : |(-1067681751/5000000000 : ℝ)|=(1067681751/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1076_s8_7 (p : ℝ) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (174962679/400000000 : ℝ)*x 0 + (4502477507/10000000000 : ℝ)*x 1 + (4249374477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (174962679/400000000 : ℝ)^8269 ≤ (33316717787211/100000000000000 : ℝ)^6221 := by
    have hnat : (174962679 : ℕ)^8269*100000000000000^6221 ≤ 33316717787211^6221*400000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      174962679 400000000 33316717787211 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502477507/10000000000 : ℝ)^8269 ≤ (4327879982461/12500000000000 : ℝ)^6221 := by
    have hnat : (4502477507 : ℕ)^8269*12500000000000^6221 ≤ 4327879982461^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502477507 10000000000 4327879982461 12500000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4249374477/10000000000 : ℝ)^8269 ≤ (32060242328297/100000000000000 : ℝ)^6221 := by
    have hnat : (4249374477 : ℕ)^8269*100000000000000^6221 ≤ 32060242328297^6221*10000000000^8269 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249374477 10000000000 32060242328297 100000000000000 8269 6221 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8269/2048 : ℝ)) 8269 6221 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(174962679/400000000 : ℝ), (4502477507/10000000000 : ℝ), (4249374477/10000000000 : ℝ)] ![(33316717787211/100000000000000 : ℝ), (4327879982461/12500000000000 : ℝ), (32060242328297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(174962679/400000000 : ℝ)|^8269 ≤ (33316717787211/100000000000000 : ℝ)^6221
        have hw : |(174962679/400000000 : ℝ)|=(174962679/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502477507/10000000000 : ℝ)|^8269 ≤ (4327879982461/12500000000000 : ℝ)^6221
        have hw : |(4502477507/10000000000 : ℝ)|=(4502477507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4249374477/10000000000 : ℝ)|^8269 ≤ (32060242328297/100000000000000 : ℝ)^6221
        have hw : |(4249374477/10000000000 : ℝ)|=(4249374477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1076_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2253/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14009/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14011/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11263/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14011/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11263/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14011/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11263/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11263/100000 : ℝ) ^ (2067/512 : ℝ) ≤ (14839655269047503/100000000000000000000 : ℝ) := by
    have hpowers : (11263/100000 : ℝ)^2067 ≤ (14839655269047503/100000000000000000000 : ℝ)^512 := by
      have hnat : (11263 : ℕ)^2067*100000000000000000000^512 ≤ 14839655269047503^512*100000^2067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11263 100000 14839655269047503 100000000000000000000 2067 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11263/100000 : ℝ)) (X := (14839655269047503/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14011/100000 : ℝ) ^ (2067/512 : ℝ) ≤ (17913173800279309/50000000000000000000 : ℝ) := by
    have hpowers : (14011/100000 : ℝ)^2067 ≤ (17913173800279309/50000000000000000000 : ℝ)^512 := by
      have hnat : (14011 : ℕ)^2067*50000000000000000000^512 ≤ 17913173800279309^512*100000^2067 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14011 100000 17913173800279309 50000000000000000000 2067 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14011/100000 : ℝ)) (X := (17913173800279309/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014839655269047503/50000000000000000000 : ℝ) ≤ (5000367540175459/5000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (50014839655269047503/50000000000000000000 : ℝ)^512 ≤ (5000367540175459/5000000000000000 : ℝ)^2067 := by
      have hnat : (50014839655269047503 : ℕ)^512*5000000000000000^2067 ≤ 5000367540175459^2067*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014839655269047503 50000000000000000000 5000367540175459 5000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000367540175459/5000000000000000 : ℝ)) (X := (50014839655269047503/50000000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100050666002869606121/100000000000000000000 : ℝ) ≤ (5000627383916447/5000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (100050666002869606121/100000000000000000000 : ℝ)^512 ≤ (5000627383916447/5000000000000000 : ℝ)^2067 := by
      have hnat : (100050666002869606121 : ℕ)^512*5000000000000000^2067 ≤ 5000627383916447^2067*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100050666002869606121 100000000000000000000 5000627383916447 5000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000627383916447/5000000000000000 : ℝ)) (X := (100050666002869606121/100000000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017913173800279309/25000000000000000000 : ℝ) ≤ (1000177445531487/1000000000000000 : ℝ) ^ (2067/512 : ℝ) := by
    have hpowers : (25017913173800279309/25000000000000000000 : ℝ)^512 ≤ (1000177445531487/1000000000000000 : ℝ)^2067 := by
      have hnat : (25017913173800279309 : ℕ)^512*1000000000000000^2067 ≤ 1000177445531487^2067*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017913173800279309 25000000000000000000 1000177445531487 1000000000000000 512 2067 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000177445531487/1000000000000000 : ℝ)) (X := (25017913173800279309/25000000000000000000 : ℝ)) (by norm_num) 2067 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14839655269047503/100000000000000000000 : ℝ) ≤ ((3433789190073166411/3435000000000000000 : ℝ)+2*(64960935247/34350000000000 : ℝ)*(11263/100000 : ℝ))^(2067/512 : ℝ) := by
    rw [show (3433789190073166411/3435000000000000000 : ℝ)+2*(64960935247/34350000000000 : ℝ)*(11263/100000 : ℝ)=(5000367540175459/5000000000000000 : ℝ) by norm_num, show 1+2*(14839655269047503/100000000000000000000 : ℝ)=(50014839655269047503/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17913173800279309/50000000000000000000 : ℝ)+(14839655269047503/100000000000000000000 : ℝ) ≤ ((3433789190073166411/3435000000000000000 : ℝ)+(64960935247/34350000000000 : ℝ)*((14011/100000 : ℝ)+(11263/100000 : ℝ)))^(2067/512 : ℝ) := by
    rw [show (3433789190073166411/3435000000000000000 : ℝ)+(64960935247/34350000000000 : ℝ)*((14011/100000 : ℝ)+(11263/100000 : ℝ))=(5000627383916447/5000000000000000 : ℝ) by norm_num, show 1+(17913173800279309/50000000000000000000 : ℝ)+(14839655269047503/100000000000000000000 : ℝ)=(100050666002869606121/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17913173800279309/50000000000000000000 : ℝ) ≤ ((3433789190073166411/3435000000000000000 : ℝ)+2*(64960935247/34350000000000 : ℝ)*(14011/100000 : ℝ))^(2067/512 : ℝ) := by
    rw [show (3433789190073166411/3435000000000000000 : ℝ)+2*(64960935247/34350000000000 : ℝ)*(14011/100000 : ℝ)=(1000177445531487/1000000000000000 : ℝ) by norm_num, show 1+2*(17913173800279309/50000000000000000000 : ℝ)=(25017913173800279309/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3433789190073166411/3435000000000000000 : ℝ)*(X 1 0+X 2 0)+(64960935247/34350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (3433789190073166411/3435000000000000000 : ℝ)) (alpha := (64960935247/34350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3433789190073166411/3435000000000000000 : ℝ)*(X 0 1+X 2 1)+(64960935247/34350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (3433789190073166411/3435000000000000000 : ℝ)) (alpha := (64960935247/34350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3433789190073166411/3435000000000000000 : ℝ)*(X 0 2+X 1 2)+(64960935247/34350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2067/512 : ℝ)) (lo := (11263/100000 : ℝ)) (hi := (14011/100000 : ℝ)) (c := (3433789190073166411/3435000000000000000 : ℝ)) (alpha := (64960935247/34350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-87954219/400000000 : ℝ)*X 0 0+(84284011/156250000 : ℝ)*X 0 1+(5264639317/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1068990687/2000000000 : ℝ)*X 1 0+(-566143979/2500000000 : ℝ)*X 1 1+(131615983/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344953431/10000000000 : ℝ)*X 2 0+(164519979/312500000 : ℝ)*X 2 1+(-283071989/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((874811249/2000000000 : ℝ)*X 0 0+(2124367799/5000000000 : ℝ)*X 0 1+(4503114931/10000000000 : ℝ)*X 0 2+(874811249/2000000000 : ℝ)*X 1 0+(2124367799/5000000000 : ℝ)*X 1 1+(4503114931/10000000000 : ℝ)*X 1 2+(874811249/2000000000 : ℝ)*X 2 0+(2124367799/5000000000 : ℝ)*X 2 1+(4503114931/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1099430181/5000000000 : ℝ)*X 0 0+(1316241007/2500000000 : ℝ)*X 0 1+(5393850939/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062459867/2000000000 : ℝ)*X 1 0+(-42707303/200000000 : ℝ)*X 1 1+(5393850649/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312300529/10000000000 : ℝ)*X 2 0+(215754027/400000000 : ℝ)*X 2 1+(-1067681751/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((174962679/400000000 : ℝ)*X 0 0+(4502477507/10000000000 : ℝ)*X 0 1+(4249374477/10000000000 : ℝ)*X 0 2+(174962679/400000000 : ℝ)*X 1 0+(4502477507/10000000000 : ℝ)*X 1 1+(4249374477/10000000000 : ℝ)*X 1 2+(174962679/400000000 : ℝ)*X 2 0+(4502477507/10000000000 : ℝ)*X 2 1+(4249374477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1076_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (261238671548096766657805987/28625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1818714863/100000000000000 : ℝ)*(base19) + (170070531/10000000000000 : ℝ)*(base23) + (11997521/20000000000000 : ℝ)*(lower2) + (223468299/100000000000000 : ℝ)*(upper3) + (146033181/100000000000000 : ℝ)*(upper5) + (2912767208867983/50000000000000 : ℝ)*(major0) + (2912767208867983/50000000000000 : ℝ)*(major1) + (2912767208867983/50000000000000 : ℝ)*(major2) + (1543966085952809/20000000000000 : ℝ)*(sp0) + (3859939073991359/50000000000000 : ℝ)*(sp1) + (771987826599227/10000000000000 : ℝ)*(sp2) + (1965580820790001/50000000000000 : ℝ)*(sp3) + (1548029173/3125000000000 : ℝ)*(sp4) + (26922986279/100000000000000 : ℝ)*(sp7) + (1965594282283141/50000000000000 : ℝ)*(f.failure) + (385993998334879/5000000000000 : ℝ)*(f.sum) + (489138515507/107343750000000000000000000 : ℝ)*base65 + (633755855489269013/171750000000000000000000000000000 : ℝ)*base67 + (891619472410480987/171750000000000000000000000000000 : ℝ)*base70 + (6407319759730987/171750000000000000000000000000000 : ℝ)*base72 + (27192432291169/3435000000000000000000000000 : ℝ)*base73 + (4400148447785269013/171750000000000000000000000000000 : ℝ)*base75 + (463974359870269013/171750000000000000000000000000000 : ℝ)*base77 + (1430101545473269013/171750000000000000000000000000000 : ℝ)*base79 + (7068853215529/3435000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (9633849/5000000000000000000000 : ℝ)*base90 + (9633849/5000000000000000000000 : ℝ)*base92 + (9633849/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (36994727046126388432336407/14312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (484168733/50000000000000 : ℝ)*(base19) + (1212337329/50000000000000 : ℝ)*(base23) + (114924767/25000000000000 : ℝ)*(lower2) + (110513161/50000000000000 : ℝ)*(upper3) + (54160841/50000000000000 : ℝ)*(upper5) + (1463720619097763/25000000000000 : ℝ)*(major0) + (1463720619097763/25000000000000 : ℝ)*(major1) + (1463720619097763/25000000000000 : ℝ)*(major2) + (94004487899/100000000000000 : ℝ)*(sp2) + (137184339/2000000000000 : ℝ)*(sp3) + (1551754327583341/20000000000000 : ℝ)*(sp4) + (7758770669579239/100000000000000 : ℝ)*(sp5) + (1939668802188537/25000000000000 : ℝ)*(sp6) + (1975493184744479/50000000000000 : ℝ)*(sp7) + (987748307176477/25000000000000 : ℝ)*(f.failure) + (1551754327583341/20000000000000 : ℝ)*(f.sum) + (6193859374019/1717500000000000000000000000 : ℝ)*base65 + (604648598639811407/85875000000000000000000000000000 : ℝ)*base68 + (836308150453313593/85875000000000000000000000000000 : ℝ)*base69 + (831827239841063593/85875000000000000000000000000000 : ℝ)*base71 + (2343737071043/858750000000000000000000000 : ℝ)*base74 + (1216816830491813593/85875000000000000000000000000000 : ℝ)*base75 + (1266365929697063593/85875000000000000000000000000000 : ℝ)*base77 + (260208613637811407/85875000000000000000000000000000 : ℝ)*base80 + (6124900657/3354492187500000000000000 : ℝ)*base81 + (17973553/2500000000000000000000 : ℝ)*base90 + (17973553/2500000000000000000000 : ℝ)*base92 + (17973553/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1076_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14011/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1076_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1076_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1076_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1076_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1076_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2067/512 : ℝ) ≤ p) (hpb : p ≤ (8269/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148187611/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5607/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14009/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1076_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
