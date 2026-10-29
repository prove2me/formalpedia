-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1499_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T23:52:16.650803+00:00
-- url     : https://prove2.me/submissions/5d3d6126-6a5f-444d-a2de-c2f599603ec2

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
theorem support_rectangle_w1499_s3_0 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-943407211/5000000000 : ℝ)*x 0 + (1359682329/2500000000 : ℝ)*x 1 + (2606767871/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943407211/5000000000 : ℝ)^4495 ≤ (5768034179431/50000000000000 : ℝ)^3471 := by
    have hnat : (943407211 : ℕ)^4495*50000000000000^3471 ≤ 5768034179431^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943407211 5000000000 5768034179431 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1359682329/2500000000 : ℝ)^4495 ≤ (9088558255349/20000000000000 : ℝ)^3471 := by
    have hnat : (1359682329 : ℕ)^4495*20000000000000^3471 ≤ 9088558255349^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359682329 2500000000 9088558255349 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606767871/5000000000 : ℝ)^4495 ≤ (43021140340679/100000000000000 : ℝ)^3471 := by
    have hnat : (2606767871 : ℕ)^4495*100000000000000^3471 ≤ 43021140340679^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606767871 5000000000 43021140340679 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-943407211/5000000000 : ℝ), (1359682329/2500000000 : ℝ), (2606767871/5000000000 : ℝ)] ![(5768034179431/50000000000000 : ℝ), (9088558255349/20000000000000 : ℝ), (43021140340679/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-943407211/5000000000 : ℝ)|^4495 ≤ (5768034179431/50000000000000 : ℝ)^3471
        have hw : |(-943407211/5000000000 : ℝ)|=(943407211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1359682329/2500000000 : ℝ)|^4495 ≤ (9088558255349/20000000000000 : ℝ)^3471
        have hw : |(1359682329/2500000000 : ℝ)|=(1359682329/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606767871/5000000000 : ℝ)|^4495 ≤ (43021140340679/100000000000000 : ℝ)^3471
        have hw : |(2606767871/5000000000 : ℝ)|=(2606767871/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s3_1 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676647421/5000000000 : ℝ)*x 0 + (-2002269423/10000000000 : ℝ)*x 1 + (2606767887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676647421/5000000000 : ℝ)^4495 ≤ (8904101507027/20000000000000 : ℝ)^3471 := by
    have hnat : (2676647421 : ℕ)^4495*20000000000000^3471 ≤ 8904101507027^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676647421 5000000000 8904101507027 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002269423/10000000000 : ℝ)^4495 ≤ (12458351773683/100000000000000 : ℝ)^3471 := by
    have hnat : (2002269423 : ℕ)^4495*100000000000000^3471 ≤ 12458351773683^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002269423 10000000000 12458351773683 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2606767887/5000000000 : ℝ)^4495 ≤ (21510570341319/50000000000000 : ℝ)^3471 := by
    have hnat : (2606767887 : ℕ)^4495*50000000000000^3471 ≤ 21510570341319^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2606767887 5000000000 21510570341319 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676647421/5000000000 : ℝ), (-2002269423/10000000000 : ℝ), (2606767887/5000000000 : ℝ)] ![(8904101507027/20000000000000 : ℝ), (12458351773683/100000000000000 : ℝ), (21510570341319/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676647421/5000000000 : ℝ)|^4495 ≤ (8904101507027/20000000000000 : ℝ)^3471
        have hw : |(2676647421/5000000000 : ℝ)|=(2676647421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2002269423/10000000000 : ℝ)|^4495 ≤ (12458351773683/100000000000000 : ℝ)^3471
        have hw : |(-2002269423/10000000000 : ℝ)|=(2002269423/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2606767887/5000000000 : ℝ)|^4495 ≤ (21510570341319/50000000000000 : ℝ)^3471
        have hw : |(2606767887/5000000000 : ℝ)|=(2606767887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s3_2 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5353295263/10000000000 : ℝ)*x 0 + (5213535313/10000000000 : ℝ)*x 1 + (-200226947/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5353295263/10000000000 : ℝ)^4495 ≤ (44520512069287/100000000000000 : ℝ)^3471 := by
    have hnat : (5353295263 : ℕ)^4495*100000000000000^3471 ≤ 44520512069287^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5353295263 10000000000 44520512069287 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5213535313/10000000000 : ℝ)^4495 ≤ (8604227151257/20000000000000 : ℝ)^3471 := by
    have hnat : (5213535313 : ℕ)^4495*20000000000000^3471 ≤ 8604227151257^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5213535313 10000000000 8604227151257 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200226947/1000000000 : ℝ)^4495 ≤ (3114588038099/25000000000000 : ℝ)^3471 := by
    have hnat : (200226947 : ℕ)^4495*25000000000000^3471 ≤ 3114588038099^3471*1000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200226947 1000000000 3114588038099 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5353295263/10000000000 : ℝ), (5213535313/10000000000 : ℝ), (-200226947/1000000000 : ℝ)] ![(44520512069287/100000000000000 : ℝ), (8604227151257/20000000000000 : ℝ), (3114588038099/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5353295263/10000000000 : ℝ)|^4495 ≤ (44520512069287/100000000000000 : ℝ)^3471
        have hw : |(5353295263/10000000000 : ℝ)|=(5353295263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5213535313/10000000000 : ℝ)|^4495 ≤ (8604227151257/20000000000000 : ℝ)^3471
        have hw : |(5213535313/10000000000 : ℝ)|=(5213535313/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-200226947/1000000000 : ℝ)|^4495 ≤ (3114588038099/25000000000000 : ℝ)^3471
        have hw : |(-200226947/1000000000 : ℝ)|=(200226947/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s3_3 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4275502393/10000000000 : ℝ)*x 0 + (4028938841/10000000000 : ℝ)*x 1 + (90698231/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4275502393/10000000000 : ℝ)^4495 ≤ (16637670586679/50000000000000 : ℝ)^3471 := by
    have hnat : (4275502393 : ℕ)^4495*50000000000000^3471 ≤ 16637670586679^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4275502393 10000000000 16637670586679 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4028938841/10000000000 : ℝ)^4495 ≤ (30811700518783/100000000000000 : ℝ)^3471 := by
    have hnat : (4028938841 : ℕ)^4495*100000000000000^3471 ≤ 30811700518783^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4028938841 10000000000 30811700518783 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90698231/200000000 : ℝ)^4495 ≤ (17956479147867/50000000000000 : ℝ)^3471 := by
    have hnat : (90698231 : ℕ)^4495*50000000000000^3471 ≤ 17956479147867^3471*200000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90698231 200000000 17956479147867 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4275502393/10000000000 : ℝ), (4028938841/10000000000 : ℝ), (90698231/200000000 : ℝ)] ![(16637670586679/50000000000000 : ℝ), (30811700518783/100000000000000 : ℝ), (17956479147867/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4275502393/10000000000 : ℝ)|^4495 ≤ (16637670586679/50000000000000 : ℝ)^3471
        have hw : |(4275502393/10000000000 : ℝ)|=(4275502393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4028938841/10000000000 : ℝ)|^4495 ≤ (30811700518783/100000000000000 : ℝ)^3471
        have hw : |(4028938841/10000000000 : ℝ)|=(4028938841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(90698231/200000000 : ℝ)|^4495 ≤ (17956479147867/50000000000000 : ℝ)^3471
        have hw : |(90698231/200000000 : ℝ)|=(90698231/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s3_4 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-943423153/5000000000 : ℝ)*x 0 + (41717839/80000000 : ℝ)*x 1 + (5437526579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943423153/5000000000 : ℝ)^4495 ≤ (2307264162031/20000000000000 : ℝ)^3471 := by
    have hnat : (943423153 : ℕ)^4495*20000000000000^3471 ≤ 2307264162031^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943423153 5000000000 2307264162031 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41717839/80000000 : ℝ)^4495 ≤ (43033901555431/100000000000000 : ℝ)^3471 := by
    have hnat : (41717839 : ℕ)^4495*100000000000000^3471 ≤ 43033901555431^3471*80000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41717839 80000000 43033901555431 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437526579/10000000000 : ℝ)^4495 ≤ (5678722203273/12500000000000 : ℝ)^3471 := by
    have hnat : (5437526579 : ℕ)^4495*12500000000000^3471 ≤ 5678722203273^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437526579 10000000000 5678722203273 12500000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-943423153/5000000000 : ℝ), (41717839/80000000 : ℝ), (5437526579/10000000000 : ℝ)] ![(2307264162031/20000000000000 : ℝ), (43033901555431/100000000000000 : ℝ), (5678722203273/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-943423153/5000000000 : ℝ)|^4495 ≤ (2307264162031/20000000000000 : ℝ)^3471
        have hw : |(-943423153/5000000000 : ℝ)|=(943423153/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(41717839/80000000 : ℝ)|^4495 ≤ (43033901555431/100000000000000 : ℝ)^3471
        have hw : |(41717839/80000000 : ℝ)|=(41717839/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437526579/10000000000 : ℝ)|^4495 ≤ (5678722203273/12500000000000 : ℝ)^3471
        have hw : |(5437526579/10000000000 : ℝ)|=(5437526579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s3_5 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1058859123/2000000000 : ℝ)*x 0 + (-1778278729/10000000000 : ℝ)*x 1 + (5437526527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1058859123/2000000000 : ℝ)^4495 ≤ (43886124004433/100000000000000 : ℝ)^3471 := by
    have hnat : (1058859123 : ℕ)^4495*100000000000000^3471 ≤ 43886124004433^3471*2000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058859123 2000000000 43886124004433 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1778278729/10000000000 : ℝ)^4495 ≤ (2136819784437/20000000000000 : ℝ)^3471 := by
    have hnat : (1778278729 : ℕ)^4495*20000000000000^3471 ≤ 2136819784437^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778278729 10000000000 2136819784437 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5437526527/10000000000 : ℝ)^4495 ≤ (45429777063561/100000000000000 : ℝ)^3471 := by
    have hnat : (5437526527 : ℕ)^4495*100000000000000^3471 ≤ 45429777063561^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437526527 10000000000 45429777063561 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1058859123/2000000000 : ℝ), (-1778278729/10000000000 : ℝ), (5437526527/10000000000 : ℝ)] ![(43886124004433/100000000000000 : ℝ), (2136819784437/20000000000000 : ℝ), (45429777063561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1058859123/2000000000 : ℝ)|^4495 ≤ (43886124004433/100000000000000 : ℝ)^3471
        have hw : |(1058859123/2000000000 : ℝ)|=(1058859123/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1778278729/10000000000 : ℝ)|^4495 ≤ (2136819784437/20000000000000 : ℝ)^3471
        have hw : |(-1778278729/10000000000 : ℝ)|=(1778278729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5437526527/10000000000 : ℝ)|^4495 ≤ (45429777063561/100000000000000 : ℝ)^3471
        have hw : |(5437526527/10000000000 : ℝ)|=(5437526527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s3_6 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294295691/10000000000 : ℝ)*x 0 + (5437526509/10000000000 : ℝ)*x 1 + (-222284831/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294295691/10000000000 : ℝ)^4495 ≤ (21943062410139/50000000000000 : ℝ)^3471 := by
    have hnat : (5294295691 : ℕ)^4495*50000000000000^3471 ≤ 21943062410139^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294295691 10000000000 21943062410139 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5437526509/10000000000 : ℝ)^4495 ≤ (22714888434403/50000000000000 : ℝ)^3471 := by
    have hnat : (5437526509 : ℕ)^4495*50000000000000^3471 ≤ 22714888434403^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5437526509 10000000000 22714888434403 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222284831/1250000000 : ℝ)^4495 ≤ (10684098291957/100000000000000 : ℝ)^3471 := by
    have hnat : (222284831 : ℕ)^4495*100000000000000^3471 ≤ 10684098291957^3471*1250000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222284831 1250000000 10684098291957 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294295691/10000000000 : ℝ), (5437526509/10000000000 : ℝ), (-222284831/1250000000 : ℝ)] ![(21943062410139/50000000000000 : ℝ), (22714888434403/50000000000000 : ℝ), (10684098291957/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294295691/10000000000 : ℝ)|^4495 ≤ (21943062410139/50000000000000 : ℝ)^3471
        have hw : |(5294295691/10000000000 : ℝ)|=(5294295691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5437526509/10000000000 : ℝ)|^4495 ≤ (22714888434403/50000000000000 : ℝ)^3471
        have hw : |(5437526509/10000000000 : ℝ)|=(5437526509/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222284831/1250000000 : ℝ)|^4495 ≤ (10684098291957/100000000000000 : ℝ)^3471
        have hw : |(-222284831/1250000000 : ℝ)|=(222284831/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s3_7 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2137787633/5000000000 : ℝ)*x 0 + (1133057127/2500000000 : ℝ)*x 1 + (2015821253/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137787633/5000000000 : ℝ)^4495 ≤ (16638037825167/50000000000000 : ℝ)^3471 := by
    have hnat : (2137787633 : ℕ)^4495*50000000000000^3471 ≤ 16638037825167^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137787633 5000000000 16638037825167 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133057127/2500000000 : ℝ)^4495 ≤ (7177088944391/20000000000000 : ℝ)^3471 := by
    have hnat : (1133057127 : ℕ)^4495*20000000000000^3471 ≤ 7177088944391^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133057127 2500000000 7177088944391 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2015821253/5000000000 : ℝ)^4495 ≤ (481851244003/1562500000000 : ℝ)^3471 := by
    have hnat : (2015821253 : ℕ)^4495*1562500000000^3471 ≤ 481851244003^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015821253 5000000000 481851244003 1562500000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2137787633/5000000000 : ℝ), (1133057127/2500000000 : ℝ), (2015821253/5000000000 : ℝ)] ![(16638037825167/50000000000000 : ℝ), (7177088944391/20000000000000 : ℝ), (481851244003/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2137787633/5000000000 : ℝ)|^4495 ≤ (16638037825167/50000000000000 : ℝ)^3471
        have hw : |(2137787633/5000000000 : ℝ)|=(2137787633/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1133057127/2500000000 : ℝ)|^4495 ≤ (7177088944391/20000000000000 : ℝ)^3471
        have hw : |(1133057127/2500000000 : ℝ)|=(1133057127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2015821253/5000000000 : ℝ)|^4495 ≤ (481851244003/1562500000000 : ℝ)^3471
        have hw : |(2015821253/5000000000 : ℝ)|=(2015821253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1499_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1003/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (10791/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15559/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1003/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5171/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1003/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5171/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1003/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5171/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1003/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5171/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1003/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5171/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1003/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5171/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5171/50000 : ℝ) ^ (4493/1024 : ℝ) ≤ (237331254432007/5000000000000000000 : ℝ) := by
    have hpowers : (5171/50000 : ℝ)^4493 ≤ (237331254432007/5000000000000000000 : ℝ)^1024 := by
      have hnat : (5171 : ℕ)^4493*5000000000000000000^1024 ≤ 237331254432007^1024*50000^4493 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5171 50000 237331254432007 5000000000000000000 4493 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5171/50000 : ℝ)) (X := (237331254432007/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1003/6250 : ℝ) ^ (4493/1024 : ℝ) ≤ (32630901801616197/100000000000000000000 : ℝ) := by
    have hpowers : (1003/6250 : ℝ)^4493 ≤ (32630901801616197/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1003 : ℕ)^4493*100000000000000000000^1024 ≤ 32630901801616197^1024*6250^4493 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1003 6250 32630901801616197 100000000000000000000 4493 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1003/6250 : ℝ)) (X := (32630901801616197/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (2500237331254432007/2500000000000000000 : ℝ) ≤ (5000108176407089/5000000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (2500237331254432007/2500000000000000000 : ℝ)^1024 ≤ (5000108176407089/5000000000000000 : ℝ)^4493 := by
      have hnat : (2500237331254432007 : ℕ)^1024*5000000000000000^4493 ≤ 5000108176407089^4493*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2500237331254432007 2500000000000000000 5000108176407089 5000000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000108176407089/5000000000000000 : ℝ)) (X := (2500237331254432007/2500000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100037377526890256337/100000000000000000000 : ℝ) ≤ (5000425874315147/5000000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (100037377526890256337/100000000000000000000 : ℝ)^1024 ≤ (5000425874315147/5000000000000000 : ℝ)^4493 := by
      have hnat : (100037377526890256337 : ℕ)^1024*5000000000000000^4493 ≤ 5000425874315147^4493*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100037377526890256337 100000000000000000000 5000425874315147 5000000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000425874315147/5000000000000000 : ℝ)) (X := (100037377526890256337/100000000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032630901801616197/50000000000000000000 : ℝ) ≤ (1000148714444641/1000000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (50032630901801616197/50000000000000000000 : ℝ)^1024 ≤ (1000148714444641/1000000000000000 : ℝ)^4493 := by
      have hnat : (50032630901801616197 : ℕ)^1024*1000000000000000^4493 ≤ 1000148714444641^4493*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032630901801616197 50000000000000000000 1000148714444641 1000000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000148714444641/1000000000000000 : ℝ)) (X := (50032630901801616197/50000000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(237331254432007/5000000000000000000 : ℝ) ≤ ((1584669221724921009/1585000000000000000 : ℝ)+2*(17649883781/15850000000000 : ℝ)*(5171/50000 : ℝ))^(4493/1024 : ℝ) := by
    rw [show (1584669221724921009/1585000000000000000 : ℝ)+2*(17649883781/15850000000000 : ℝ)*(5171/50000 : ℝ)=(5000108176407089/5000000000000000 : ℝ) by norm_num, show 1+2*(237331254432007/5000000000000000000 : ℝ)=(2500237331254432007/2500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32630901801616197/100000000000000000000 : ℝ)+(237331254432007/5000000000000000000 : ℝ) ≤ ((1584669221724921009/1585000000000000000 : ℝ)+(17649883781/15850000000000 : ℝ)*((1003/6250 : ℝ)+(5171/50000 : ℝ)))^(4493/1024 : ℝ) := by
    rw [show (1584669221724921009/1585000000000000000 : ℝ)+(17649883781/15850000000000 : ℝ)*((1003/6250 : ℝ)+(5171/50000 : ℝ))=(5000425874315147/5000000000000000 : ℝ) by norm_num, show 1+(32630901801616197/100000000000000000000 : ℝ)+(237331254432007/5000000000000000000 : ℝ)=(100037377526890256337/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32630901801616197/100000000000000000000 : ℝ) ≤ ((1584669221724921009/1585000000000000000 : ℝ)+2*(17649883781/15850000000000 : ℝ)*(1003/6250 : ℝ))^(4493/1024 : ℝ) := by
    rw [show (1584669221724921009/1585000000000000000 : ℝ)+2*(17649883781/15850000000000 : ℝ)*(1003/6250 : ℝ)=(1000148714444641/1000000000000000 : ℝ) by norm_num, show 1+2*(32630901801616197/100000000000000000000 : ℝ)=(50032630901801616197/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1584669221724921009/1585000000000000000 : ℝ)*(X 1 0+X 2 0)+(17649883781/15850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (5171/50000 : ℝ)) (hi := (1003/6250 : ℝ)) (c := (1584669221724921009/1585000000000000000 : ℝ)) (alpha := (17649883781/15850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1584669221724921009/1585000000000000000 : ℝ)*(X 0 1+X 2 1)+(17649883781/15850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (5171/50000 : ℝ)) (hi := (1003/6250 : ℝ)) (c := (1584669221724921009/1585000000000000000 : ℝ)) (alpha := (17649883781/15850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1584669221724921009/1585000000000000000 : ℝ)*(X 0 2+X 1 2)+(17649883781/15850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (5171/50000 : ℝ)) (hi := (1003/6250 : ℝ)) (c := (1584669221724921009/1585000000000000000 : ℝ)) (alpha := (17649883781/15850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-943407211/5000000000 : ℝ)*X 0 0+(1359682329/2500000000 : ℝ)*X 0 1+(2606767871/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676647421/5000000000 : ℝ)*X 1 0+(-2002269423/10000000000 : ℝ)*X 1 1+(2606767887/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5353295263/10000000000 : ℝ)*X 2 0+(5213535313/10000000000 : ℝ)*X 2 1+(-200226947/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4275502393/10000000000 : ℝ)*X 0 0+(4028938841/10000000000 : ℝ)*X 0 1+(90698231/200000000 : ℝ)*X 0 2+(4275502393/10000000000 : ℝ)*X 1 0+(4028938841/10000000000 : ℝ)*X 1 1+(90698231/200000000 : ℝ)*X 1 2+(4275502393/10000000000 : ℝ)*X 2 0+(4028938841/10000000000 : ℝ)*X 2 1+(90698231/200000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-943423153/5000000000 : ℝ)*X 0 0+(41717839/80000000 : ℝ)*X 0 1+(5437526579/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1058859123/2000000000 : ℝ)*X 1 0+(-1778278729/10000000000 : ℝ)*X 1 1+(5437526527/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5294295691/10000000000 : ℝ)*X 2 0+(5437526509/10000000000 : ℝ)*X 2 1+(-222284831/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2137787633/5000000000 : ℝ)*X 0 0+(1133057127/2500000000 : ℝ)*X 0 1+(2015821253/5000000000 : ℝ)*X 0 2+(2137787633/5000000000 : ℝ)*X 1 0+(1133057127/2500000000 : ℝ)*X 1 1+(2015821253/5000000000 : ℝ)*X 1 2+(2137787633/5000000000 : ℝ)*X 2 0+(1133057127/2500000000 : ℝ)*X 2 1+(2015821253/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (46432818554938204271169423/4953125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55334423/2000000000000 : ℝ)*(base19) + (33702771/1250000000000 : ℝ)*(base23) + (101514723/20000000000000 : ℝ)*(upper3) + (224693793/100000000000000 : ℝ)*(upper4) + (224806357/100000000000000 : ℝ)*(upper5) + (200535326875651/6250000000000 : ℝ)*(major0) + (200535326875651/6250000000000 : ℝ)*(major1) + (200535326875651/6250000000000 : ℝ)*(major2) + (2220331358008533/50000000000000 : ℝ)*(sp0) + (2220348522679183/50000000000000 : ℝ)*(sp1) + (1110174278964459/25000000000000 : ℝ)*(sp2) + (197640819190963/10000000000000 : ℝ)*(sp3) + (37096062449/100000000000000 : ℝ)*(sp4) + (11071775019/50000000000000 : ℝ)*(sp7) + (1976430335459669/100000000000000 : ℝ)*(f.failure) + (1110174953019879/25000000000000 : ℝ)*(f.sum) + (1845614858593/396250000000000000000000000 : ℝ)*base65 + (128977670689645609/9906250000000000000000000000000 : ℝ)*base67 + (22337859201041891/9906250000000000000000000000000 : ℝ)*base70 + (27748079390114359/9906250000000000000000000000000 : ℝ)*base71 + (1903085427483/396250000000000000000000000 : ℝ)*base73 + (179384294920926859/9906250000000000000000000000000 : ℝ)*base75 + (20702227317135641/9906250000000000000000000000000 : ℝ)*base78 + (223247438739359/9906250000000000000000000000000 : ℝ)*base79 + (277009705611/198125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (25466833/2500000000000000000000 : ℝ)*base89 + (25466833/2500000000000000000000 : ℝ)*base91 + (25466833/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2444203799074782563781/317000000000000000000000000 : ℝ) := by norm_num
    linear_combination (625681331/50000000000000 : ℝ)*(base19) + (84762843/6250000000000 : ℝ)*(base23) + (79708079/50000000000000 : ℝ)*(upper3) + (339423/4000000000000 : ℝ)*(lower4) + (154484257/100000000000000 : ℝ)*(upper5) + (324302807278433/10000000000000 : ℝ)*(major0) + (324302807278433/10000000000000 : ℝ)*(major1) + (324302807278433/10000000000000 : ℝ)*(major2) + (17329959721/100000000000000 : ℝ)*(sp1) + (19517926829/100000000000000 : ℝ)*(sp2) + (561049616796927/12500000000000 : ℝ)*(sp4) + (2244189176526517/50000000000000 : ℝ)*(sp5) + (44883760602431/1000000000000 : ℝ)*(sp6) + (199765895417917/10000000000000 : ℝ)*(sp7) + (199765895417917/10000000000000 : ℝ)*(f.failure) + (561049616796927/12500000000000 : ℝ)*(f.sum) + (44196045451/19812500000000000000000000 : ℝ)*base66 + (111232604655598897/15850000000000000000000000000000 : ℝ)*base67 + (87913283850198897/15850000000000000000000000000000 : ℝ)*base69 + (1645976451398897/15850000000000000000000000000000 : ℝ)*base71 + (372341531/63400000000000000000000000 : ℝ)*base74 + (38271896361601103/15850000000000000000000000000000 : ℝ)*base76 + (25981970488351103/15850000000000000000000000000000 : ℝ)*base78 + (55116273769851103/15850000000000000000000000000000 : ℝ)*base80 + (311455686831/158500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (641369/250000000000000000000 : ℝ)*base89 + (641369/250000000000000000000 : ℝ)*base91 + (641369/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1499_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1003/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10791/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15559/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1499_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1499_s4_0 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1887322481/10000000000 : ℝ)*x 0 + (2717705421/5000000000 : ℝ)*x 1 + (1304129717/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1887322481/10000000000 : ℝ)^4495 ≤ (5770045610333/50000000000000 : ℝ)^3471 := by
    have hnat : (1887322481 : ℕ)^4495*50000000000000^3471 ≤ 5770045610333^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887322481 10000000000 5770045610333 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2717705421/5000000000 : ℝ)^4495 ≤ (11351721837243/25000000000000 : ℝ)^3471 := by
    have hnat : (2717705421 : ℕ)^4495*25000000000000^3471 ≤ 11351721837243^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2717705421 5000000000 11351721837243 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304129717/2500000000 : ℝ)^4495 ≤ (43053021410857/100000000000000 : ℝ)^3471 := by
    have hnat : (1304129717 : ℕ)^4495*100000000000000^3471 ≤ 43053021410857^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304129717 2500000000 43053021410857 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1887322481/10000000000 : ℝ), (2717705421/5000000000 : ℝ), (1304129717/2500000000 : ℝ)] ![(5770045610333/50000000000000 : ℝ), (11351721837243/25000000000000 : ℝ), (43053021410857/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1887322481/10000000000 : ℝ)|^4495 ≤ (5770045610333/50000000000000 : ℝ)^3471
        have hw : |(-1887322481/10000000000 : ℝ)|=(1887322481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2717705421/5000000000 : ℝ)|^4495 ≤ (11351721837243/25000000000000 : ℝ)^3471
        have hw : |(2717705421/5000000000 : ℝ)|=(2717705421/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304129717/2500000000 : ℝ)|^4495 ≤ (43053021410857/100000000000000 : ℝ)^3471
        have hw : |(1304129717/2500000000 : ℝ)|=(1304129717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s4_1 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535242909/1000000000 : ℝ)*x 0 + (-1999469689/10000000000 : ℝ)*x 1 + (5216518683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535242909/1000000000 : ℝ)^4495 ≤ (11127795911139/25000000000000 : ℝ)^3471 := by
    have hnat : (535242909 : ℕ)^4495*25000000000000^3471 ≤ 11127795911139^3471*1000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535242909 1000000000 11127795911139 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1999469689/10000000000 : ℝ)^4495 ≤ (3108949226121/25000000000000 : ℝ)^3471 := by
    have hnat : (1999469689 : ℕ)^4495*25000000000000^3471 ≤ 3108949226121^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999469689 10000000000 3108949226121 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5216518683/10000000000 : ℝ)^4495 ≤ (4305301943357/10000000000000 : ℝ)^3471 := by
    have hnat : (5216518683 : ℕ)^4495*10000000000000^3471 ≤ 4305301943357^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216518683 10000000000 4305301943357 10000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535242909/1000000000 : ℝ), (-1999469689/10000000000 : ℝ), (5216518683/10000000000 : ℝ)] ![(11127795911139/25000000000000 : ℝ), (3108949226121/25000000000000 : ℝ), (4305301943357/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535242909/1000000000 : ℝ)|^4495 ≤ (11127795911139/25000000000000 : ℝ)^3471
        have hw : |(535242909/1000000000 : ℝ)|=(535242909/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1999469689/10000000000 : ℝ)|^4495 ≤ (3108949226121/25000000000000 : ℝ)^3471
        have hw : |(-1999469689/10000000000 : ℝ)|=(1999469689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5216518683/10000000000 : ℝ)|^4495 ≤ (4305301943357/10000000000000 : ℝ)^3471
        have hw : |(5216518683/10000000000 : ℝ)|=(5216518683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s4_2 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338107257/2500000000 : ℝ)*x 0 + (1304129713/2500000000 : ℝ)*x 1 + (-499867387/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338107257/2500000000 : ℝ)^4495 ≤ (890223659537/2000000000000 : ℝ)^3471 := by
    have hnat : (1338107257 : ℕ)^4495*2000000000000^3471 ≤ 890223659537^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338107257 2500000000 890223659537 2000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1304129713/2500000000 : ℝ)^4495 ≤ (5381627654981/12500000000000 : ℝ)^3471 := by
    have hnat : (1304129713 : ℕ)^4495*12500000000000^3471 ≤ 5381627654981^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304129713 2500000000 5381627654981 12500000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (499867387/2500000000 : ℝ)^4495 ≤ (3108948942203/25000000000000 : ℝ)^3471 := by
    have hnat : (499867387 : ℕ)^4495*25000000000000^3471 ≤ 3108948942203^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499867387 2500000000 3108948942203 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338107257/2500000000 : ℝ), (1304129713/2500000000 : ℝ), (-499867387/2500000000 : ℝ)] ![(890223659537/2000000000000 : ℝ), (5381627654981/12500000000000 : ℝ), (3108948942203/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338107257/2500000000 : ℝ)|^4495 ≤ (890223659537/2000000000000 : ℝ)^3471
        have hw : |(1338107257/2500000000 : ℝ)|=(1338107257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1304129713/2500000000 : ℝ)|^4495 ≤ (5381627654981/12500000000000 : ℝ)^3471
        have hw : |(1304129713/2500000000 : ℝ)|=(1304129713/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-499867387/2500000000 : ℝ)|^4495 ≤ (3108948942203/25000000000000 : ℝ)^3471
        have hw : |(-499867387/2500000000 : ℝ)|=(499867387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s4_3 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (427581977/1000000000 : ℝ)*x 0 + (4035981377/10000000000 : ℝ)*x 1 + (4527795253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (427581977/1000000000 : ℝ)^4495 ≤ (3327853999961/10000000000000 : ℝ)^3471 := by
    have hnat : (427581977 : ℕ)^4495*10000000000000^3471 ≤ 3327853999961^3471*1000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427581977 1000000000 3327853999961 10000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4035981377/10000000000 : ℝ)^4495 ≤ (15440733038233/50000000000000 : ℝ)^3471 := by
    have hnat : (4035981377 : ℕ)^4495*50000000000000^3471 ≤ 15440733038233^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4035981377 10000000000 15440733038233 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4527795253/10000000000 : ℝ)^4495 ≤ (8959998477459/25000000000000 : ℝ)^3471 := by
    have hnat : (4527795253 : ℕ)^4495*25000000000000^3471 ≤ 8959998477459^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4527795253 10000000000 8959998477459 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(427581977/1000000000 : ℝ), (4035981377/10000000000 : ℝ), (4527795253/10000000000 : ℝ)] ![(3327853999961/10000000000000 : ℝ), (15440733038233/50000000000000 : ℝ), (8959998477459/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(427581977/1000000000 : ℝ)|^4495 ≤ (3327853999961/10000000000000 : ℝ)^3471
        have hw : |(427581977/1000000000 : ℝ)|=(427581977/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4035981377/10000000000 : ℝ)|^4495 ≤ (15440733038233/50000000000000 : ℝ)^3471
        have hw : |(4035981377/10000000000 : ℝ)|=(4035981377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4527795253/10000000000 : ℝ)|^4495 ≤ (8959998477459/25000000000000 : ℝ)^3471
        have hw : |(4527795253/10000000000 : ℝ)|=(4527795253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s4_4 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-943676107/5000000000 : ℝ)*x 0 + (2608823637/5000000000 : ℝ)*x 1 + (1358568551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943676107/5000000000 : ℝ)^4495 ≤ (577016332971/5000000000000 : ℝ)^3471 := by
    have hnat : (943676107 : ℕ)^4495*5000000000000^3471 ≤ 577016332971^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943676107 5000000000 577016332971 5000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2608823637/5000000000 : ℝ)^4495 ≤ (10766270560091/25000000000000 : ℝ)^3471 := by
    have hnat : (2608823637 : ℕ)^4495*25000000000000^3471 ≤ 10766270560091^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608823637 5000000000 10766270560091 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358568551/2500000000 : ℝ)^4495 ≤ (9078918216807/20000000000000 : ℝ)^3471 := by
    have hnat : (1358568551 : ℕ)^4495*20000000000000^3471 ≤ 9078918216807^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358568551 2500000000 9078918216807 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-943676107/5000000000 : ℝ), (2608823637/5000000000 : ℝ), (1358568551/2500000000 : ℝ)] ![(577016332971/5000000000000 : ℝ), (10766270560091/25000000000000 : ℝ), (9078918216807/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-943676107/5000000000 : ℝ)|^4495 ≤ (577016332971/5000000000000 : ℝ)^3471
        have hw : |(-943676107/5000000000 : ℝ)|=(943676107/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2608823637/5000000000 : ℝ)|^4495 ≤ (10766270560091/25000000000000 : ℝ)^3471
        have hw : |(2608823637/5000000000 : ℝ)|=(2608823637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358568551/2500000000 : ℝ)|^4495 ≤ (9078918216807/20000000000000 : ℝ)^3471
        have hw : |(1358568551/2500000000 : ℝ)|=(1358568551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s4_5 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059016531/2000000000 : ℝ)*x 0 + (-890857063/5000000000 : ℝ)*x 1 + (1358568551/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059016531/2000000000 : ℝ)^4495 ≤ (10973643227467/25000000000000 : ℝ)^3471 := by
    have hnat : (1059016531 : ℕ)^4495*25000000000000^3471 ≤ 10973643227467^3471*2000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059016531 2000000000 10973643227467 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (890857063/5000000000 : ℝ)^4495 ≤ (2142167197863/20000000000000 : ℝ)^3471 := by
    have hnat : (890857063 : ℕ)^4495*20000000000000^3471 ≤ 2142167197863^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890857063 5000000000 2142167197863 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1358568551/2500000000 : ℝ)^4495 ≤ (9078918216807/20000000000000 : ℝ)^3471 := by
    have hnat : (1358568551 : ℕ)^4495*20000000000000^3471 ≤ 9078918216807^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358568551 2500000000 9078918216807 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059016531/2000000000 : ℝ), (-890857063/5000000000 : ℝ), (1358568551/2500000000 : ℝ)] ![(10973643227467/25000000000000 : ℝ), (2142167197863/20000000000000 : ℝ), (9078918216807/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059016531/2000000000 : ℝ)|^4495 ≤ (10973643227467/25000000000000 : ℝ)^3471
        have hw : |(1059016531/2000000000 : ℝ)|=(1059016531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-890857063/5000000000 : ℝ)|^4495 ≤ (2142167197863/20000000000000 : ℝ)^3471
        have hw : |(-890857063/5000000000 : ℝ)|=(890857063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1358568551/2500000000 : ℝ)|^4495 ≤ (9078918216807/20000000000000 : ℝ)^3471
        have hw : |(1358568551/2500000000 : ℝ)|=(1358568551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s4_6 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1059016531/2000000000 : ℝ)*x 0 + (1358568551/2500000000 : ℝ)*x 1 + (-890857063/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059016531/2000000000 : ℝ)^4495 ≤ (10973643227467/25000000000000 : ℝ)^3471 := by
    have hnat : (1059016531 : ℕ)^4495*25000000000000^3471 ≤ 10973643227467^3471*2000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059016531 2000000000 10973643227467 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1358568551/2500000000 : ℝ)^4495 ≤ (9078918216807/20000000000000 : ℝ)^3471 := by
    have hnat : (1358568551 : ℕ)^4495*20000000000000^3471 ≤ 9078918216807^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1358568551 2500000000 9078918216807 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (890857063/5000000000 : ℝ)^4495 ≤ (2142167197863/20000000000000 : ℝ)^3471 := by
    have hnat : (890857063 : ℕ)^4495*20000000000000^3471 ≤ 2142167197863^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      890857063 5000000000 2142167197863 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1059016531/2000000000 : ℝ), (1358568551/2500000000 : ℝ), (-890857063/5000000000 : ℝ)] ![(10973643227467/25000000000000 : ℝ), (9078918216807/20000000000000 : ℝ), (2142167197863/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1059016531/2000000000 : ℝ)|^4495 ≤ (10973643227467/25000000000000 : ℝ)^3471
        have hw : |(1059016531/2000000000 : ℝ)|=(1059016531/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1358568551/2500000000 : ℝ)|^4495 ≤ (9078918216807/20000000000000 : ℝ)^3471
        have hw : |(1358568551/2500000000 : ℝ)|=(1358568551/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-890857063/5000000000 : ℝ)|^4495 ≤ (2142167197863/20000000000000 : ℝ)^3471
        have hw : |(-890857063/5000000000 : ℝ)|=(890857063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s4_7 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4275886687/10000000000 : ℝ)*x 0 + (2262629793/5000000000 : ℝ)*x 1 + (2019268007/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4275886687/10000000000 : ℝ)^4495 ≤ (33279214461509/100000000000000 : ℝ)^3471 := by
    have hnat : (4275886687 : ℕ)^4495*100000000000000^3471 ≤ 33279214461509^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4275886687 10000000000 33279214461509 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2262629793/5000000000 : ℝ)^4495 ≤ (2238375220851/6250000000000 : ℝ)^3471 := by
    have hnat : (2262629793 : ℕ)^4495*6250000000000^3471 ≤ 2238375220851^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2262629793 5000000000 2238375220851 6250000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2019268007/5000000000 : ℝ)^4495 ≤ (30906781988489/100000000000000 : ℝ)^3471 := by
    have hnat : (2019268007 : ℕ)^4495*100000000000000^3471 ≤ 30906781988489^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2019268007 5000000000 30906781988489 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4275886687/10000000000 : ℝ), (2262629793/5000000000 : ℝ), (2019268007/5000000000 : ℝ)] ![(33279214461509/100000000000000 : ℝ), (2238375220851/6250000000000 : ℝ), (30906781988489/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4275886687/10000000000 : ℝ)|^4495 ≤ (33279214461509/100000000000000 : ℝ)^3471
        have hw : |(4275886687/10000000000 : ℝ)|=(4275886687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2262629793/5000000000 : ℝ)|^4495 ≤ (2238375220851/6250000000000 : ℝ)^3471
        have hw : |(2262629793/5000000000 : ℝ)|=(2262629793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2019268007/5000000000 : ℝ)|^4495 ≤ (30906781988489/100000000000000 : ℝ)^3471
        have hw : |(2019268007/5000000000 : ℝ)|=(2019268007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1499_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15559/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10791/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2171/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15559/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10791/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15559/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10791/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15559/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10791/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15559/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10791/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15559/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10791/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15559/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10791/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10791/100000 : ℝ) ^ (4493/1024 : ℝ) ≤ (714956030812269/12500000000000000000 : ℝ) := by
    have hpowers : (10791/100000 : ℝ)^4493 ≤ (714956030812269/12500000000000000000 : ℝ)^1024 := by
      have hnat : (10791 : ℕ)^4493*12500000000000000000^1024 ≤ 714956030812269^1024*100000^4493 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10791 100000 714956030812269 12500000000000000000 4493 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10791/100000 : ℝ)) (X := (714956030812269/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (15559/100000 : ℝ) ^ (4493/1024 : ℝ) ≤ (28487990014137529/100000000000000000000 : ℝ) := by
    have hpowers : (15559/100000 : ℝ)^4493 ≤ (28487990014137529/100000000000000000000 : ℝ)^1024 := by
      have hnat : (15559 : ℕ)^4493*100000000000000000000^1024 ≤ 28487990014137529^1024*100000^4493 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15559 100000 28487990014137529 100000000000000000000 4493 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15559/100000 : ℝ)) (X := (28487990014137529/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250714956030812269/6250000000000000000 : ℝ) ≤ (10000260701588047/10000000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (6250714956030812269/6250000000000000000 : ℝ)^1024 ≤ (10000260701588047/10000000000000000 : ℝ)^4493 := by
      have hnat : (6250714956030812269 : ℕ)^1024*10000000000000000^4493 ≤ 10000260701588047^4493*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250714956030812269 6250000000000000000 10000260701588047 10000000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000260701588047/10000000000000000 : ℝ)) (X := (6250714956030812269/6250000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100034207638260635681/100000000000000000000 : ℝ) ≤ (500038976181553/500000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (100034207638260635681/100000000000000000000 : ℝ)^1024 ≤ (500038976181553/500000000000000 : ℝ)^4493 := by
      have hnat : (100034207638260635681 : ℕ)^1024*500000000000000^4493 ≤ 500038976181553^4493*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100034207638260635681 100000000000000000000 500038976181553 500000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500038976181553/500000000000000 : ℝ)) (X := (100034207638260635681/100000000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50028487990014137529/50000000000000000000 : ℝ) ≤ (10001298345674073/10000000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (50028487990014137529/50000000000000000000 : ℝ)^1024 ≤ (10001298345674073/10000000000000000 : ℝ)^4493 := by
      have hnat : (50028487990014137529 : ℕ)^1024*10000000000000000^4493 ≤ 10001298345674073^4493*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50028487990014137529 50000000000000000000 10001298345674073 10000000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001298345674073/10000000000000000 : ℝ)) (X := (50028487990014137529/50000000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(714956030812269/12500000000000000000 : ℝ) ≤ ((4767004580783950153/4768000000000000000 : ℝ)+2*(518822043013/476800000000000 : ℝ)*(10791/100000 : ℝ))^(4493/1024 : ℝ) := by
    rw [show (4767004580783950153/4768000000000000000 : ℝ)+2*(518822043013/476800000000000 : ℝ)*(10791/100000 : ℝ)=(10000260701588047/10000000000000000 : ℝ) by norm_num, show 1+2*(714956030812269/12500000000000000000 : ℝ)=(6250714956030812269/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(28487990014137529/100000000000000000000 : ℝ)+(714956030812269/12500000000000000000 : ℝ) ≤ ((4767004580783950153/4768000000000000000 : ℝ)+(518822043013/476800000000000 : ℝ)*((15559/100000 : ℝ)+(10791/100000 : ℝ)))^(4493/1024 : ℝ) := by
    rw [show (4767004580783950153/4768000000000000000 : ℝ)+(518822043013/476800000000000 : ℝ)*((15559/100000 : ℝ)+(10791/100000 : ℝ))=(500038976181553/500000000000000 : ℝ) by norm_num, show 1+(28487990014137529/100000000000000000000 : ℝ)+(714956030812269/12500000000000000000 : ℝ)=(100034207638260635681/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(28487990014137529/100000000000000000000 : ℝ) ≤ ((4767004580783950153/4768000000000000000 : ℝ)+2*(518822043013/476800000000000 : ℝ)*(15559/100000 : ℝ))^(4493/1024 : ℝ) := by
    rw [show (4767004580783950153/4768000000000000000 : ℝ)+2*(518822043013/476800000000000 : ℝ)*(15559/100000 : ℝ)=(10001298345674073/10000000000000000 : ℝ) by norm_num, show 1+2*(28487990014137529/100000000000000000000 : ℝ)=(50028487990014137529/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4767004580783950153/4768000000000000000 : ℝ)*(X 1 0+X 2 0)+(518822043013/476800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (10791/100000 : ℝ)) (hi := (15559/100000 : ℝ)) (c := (4767004580783950153/4768000000000000000 : ℝ)) (alpha := (518822043013/476800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4767004580783950153/4768000000000000000 : ℝ)*(X 0 1+X 2 1)+(518822043013/476800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (10791/100000 : ℝ)) (hi := (15559/100000 : ℝ)) (c := (4767004580783950153/4768000000000000000 : ℝ)) (alpha := (518822043013/476800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4767004580783950153/4768000000000000000 : ℝ)*(X 0 2+X 1 2)+(518822043013/476800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (10791/100000 : ℝ)) (hi := (15559/100000 : ℝ)) (c := (4767004580783950153/4768000000000000000 : ℝ)) (alpha := (518822043013/476800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1887322481/10000000000 : ℝ)*X 0 0+(2717705421/5000000000 : ℝ)*X 0 1+(1304129717/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((535242909/1000000000 : ℝ)*X 1 0+(-1999469689/10000000000 : ℝ)*X 1 1+(5216518683/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1338107257/2500000000 : ℝ)*X 2 0+(1304129713/2500000000 : ℝ)*X 2 1+(-499867387/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((427581977/1000000000 : ℝ)*X 0 0+(4035981377/10000000000 : ℝ)*X 0 1+(4527795253/10000000000 : ℝ)*X 0 2+(427581977/1000000000 : ℝ)*X 1 0+(4035981377/10000000000 : ℝ)*X 1 1+(4527795253/10000000000 : ℝ)*X 1 2+(427581977/1000000000 : ℝ)*X 2 0+(4035981377/10000000000 : ℝ)*X 2 1+(4527795253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-943676107/5000000000 : ℝ)*X 0 0+(2608823637/5000000000 : ℝ)*X 0 1+(1358568551/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1059016531/2000000000 : ℝ)*X 1 0+(-890857063/5000000000 : ℝ)*X 1 1+(1358568551/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1059016531/2000000000 : ℝ)*X 2 0+(1358568551/2500000000 : ℝ)*X 2 1+(-890857063/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4275886687/10000000000 : ℝ)*X 0 0+(2262629793/5000000000 : ℝ)*X 0 1+(2019268007/5000000000 : ℝ)*X 0 2+(4275886687/10000000000 : ℝ)*X 1 0+(2262629793/5000000000 : ℝ)*X 1 1+(2019268007/5000000000 : ℝ)*X 1 2+(4275886687/10000000000 : ℝ)*X 2 0+(2262629793/5000000000 : ℝ)*X 2 1+(2019268007/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2486622764956012093806682371/238400000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2006278701/100000000000000 : ℝ)*(base19) + (234105339/12500000000000 : ℝ)*(base23) + (43095859/100000000000000 : ℝ)*(lower2) + (240924057/100000000000000 : ℝ)*(upper3) + (306964877/100000000000000 : ℝ)*(upper5) + (3300919261377369/100000000000000 : ℝ)*(major0) + (3300919261377369/100000000000000 : ℝ)*(major1) + (3300919261377369/100000000000000 : ℝ)*(major2) + (1142122487204043/25000000000000 : ℝ)*(sp0) + (913703413926247/20000000000000 : ℝ)*(sp1) + (4568517203067223/100000000000000 : ℝ)*(sp2) + (101665226102249/5000000000000 : ℝ)*(sp3) + (29127093763/100000000000000 : ℝ)*(sp4) + (7288558831/50000000000000 : ℝ)*(sp7) + (1016659549581321/50000000000000 : ℝ)*(f.failure) + (285532442244371/6250000000000 : ℝ)*(f.sum) + (58158487726403/23840000000000000000000000000 : ℝ)*base66 + (737709819395857457/476800000000000000000000000000000 : ℝ)*base67 + (3415670128834542543/476800000000000000000000000000000 : ℝ)*base70 + (1284688930967057457/476800000000000000000000000000000 : ℝ)*base71 + (77596172841117/23840000000000000000000000000 : ℝ)*base73 + (3432901946412142543/476800000000000000000000000000000 : ℝ)*base76 + (2164445600252142543/476800000000000000000000000000000 : ℝ)*base78 + (5265058716252142543/476800000000000000000000000000000 : ℝ)*base80 + (2313707882563/23840000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (816597/1250000000000000000000 : ℝ)*base89 + (816597/1250000000000000000000 : ℝ)*base91 + (816597/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (585590752211417564173952433/59600000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (806072271/50000000000000 : ℝ)*(base19) + (349875993/20000000000000 : ℝ)*(base23) + (101499967/50000000000000 : ℝ)*(upper3) + (62064269/100000000000000 : ℝ)*(lower4) + (202867433/100000000000000 : ℝ)*(upper5) + (1667696120417413/50000000000000 : ℝ)*(major0) + (1667696120417413/50000000000000 : ℝ)*(major1) + (1667696120417413/50000000000000 : ℝ)*(major2) + (12239897649/50000000000000 : ℝ)*(sp1) + (13164382813/50000000000000 : ℝ)*(sp2) + (1154057548055919/25000000000000 : ℝ)*(sp4) + (1154051025070959/25000000000000 : ℝ)*(sp5) + (1154050528519521/25000000000000 : ℝ)*(sp6) + (1027276980967183/50000000000000 : ℝ)*(sp7) + (1027276980967183/50000000000000 : ℝ)*(f.failure) + (1154057548055919/25000000000000 : ℝ)*(f.sum) + (63479828191609/11920000000000000000000000000 : ℝ)*base65 + (504027697918904189/238400000000000000000000000000000 : ℝ)*base67 + (709070930123704189/238400000000000000000000000000000 : ℝ)*base69 + (367024667266104189/238400000000000000000000000000000 : ℝ)*base71 + (13911678205191/11920000000000000000000000000 : ℝ)*base74 + (53967647357895811/238400000000000000000000000000000 : ℝ)*base76 + (110949417582904189/238400000000000000000000000000000 : ℝ)*base77 + (1466718542181304189/238400000000000000000000000000000 : ℝ)*base79 + (51751517120729/11920000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2339331/1250000000000000000000 : ℝ)*base89 + (2339331/1250000000000000000000 : ℝ)*base91 + (2339331/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1499_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15559/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10791/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2171/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1499_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1499_s5_0 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1887386643/10000000000 : ℝ)*x 0 + (1086997027/2000000000 : ℝ)*x 1 + (208676089/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1887386643/10000000000 : ℝ)^4495 ≤ (23081198569/200000000000 : ℝ)^3471 := by
    have hnat : (1887386643 : ℕ)^4495*200000000000^3471 ≤ 23081198569^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1887386643 10000000000 23081198569 200000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1086997027/2000000000 : ℝ)^4495 ≤ (45402281918693/100000000000000 : ℝ)^3471 := by
    have hnat : (1086997027 : ℕ)^4495*100000000000000^3471 ≤ 45402281918693^3471*2000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1086997027 2000000000 45402281918693 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208676089/400000000 : ℝ)^4495 ≤ (2691069924309/6250000000000 : ℝ)^3471 := by
    have hnat : (208676089 : ℕ)^4495*6250000000000^3471 ≤ 2691069924309^3471*400000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208676089 400000000 2691069924309 6250000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1887386643/10000000000 : ℝ), (1086997027/2000000000 : ℝ), (208676089/400000000 : ℝ)] ![(23081198569/200000000000 : ℝ), (45402281918693/100000000000000 : ℝ), (2691069924309/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1887386643/10000000000 : ℝ)|^4495 ≤ (23081198569/200000000000 : ℝ)^3471
        have hw : |(-1887386643/10000000000 : ℝ)|=(1887386643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1086997027/2000000000 : ℝ)|^4495 ≤ (45402281918693/100000000000000 : ℝ)^3471
        have hw : |(1086997027/2000000000 : ℝ)|=(1086997027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(208676089/400000000 : ℝ)|^4495 ≤ (2691069924309/6250000000000 : ℝ)^3471
        have hw : |(208676089/400000000 : ℝ)|=(208676089/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s5_1 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5352317991/10000000000 : ℝ)*x 0 + (-1999109271/10000000000 : ℝ)*x 1 + (326056389/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352317991/10000000000 : ℝ)^4495 ≤ (44509987173703/100000000000000 : ℝ)^3471 := by
    have hnat : (5352317991 : ℕ)^4495*100000000000000^3471 ≤ 44509987173703^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352317991 10000000000 44509987173703 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1999109271/10000000000 : ℝ)^4495 ≤ (12432894026361/100000000000000 : ℝ)^3471 := by
    have hnat : (1999109271 : ℕ)^4495*100000000000000^3471 ≤ 12432894026361^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1999109271 10000000000 12432894026361 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326056389/625000000 : ℝ)^4495 ≤ (2691069923641/6250000000000 : ℝ)^3471 := by
    have hnat : (326056389 : ℕ)^4495*6250000000000^3471 ≤ 2691069923641^3471*625000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326056389 625000000 2691069923641 6250000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352317991/10000000000 : ℝ), (-1999109271/10000000000 : ℝ), (326056389/625000000 : ℝ)] ![(44509987173703/100000000000000 : ℝ), (12432894026361/100000000000000 : ℝ), (2691069923641/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352317991/10000000000 : ℝ)|^4495 ≤ (44509987173703/100000000000000 : ℝ)^3471
        have hw : |(5352317991/10000000000 : ℝ)|=(5352317991/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1999109271/10000000000 : ℝ)|^4495 ≤ (12432894026361/100000000000000 : ℝ)^3471
        have hw : |(-1999109271/10000000000 : ℝ)|=(1999109271/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326056389/625000000 : ℝ)|^4495 ≤ (2691069923641/6250000000000 : ℝ)^3471
        have hw : |(326056389/625000000 : ℝ)|=(326056389/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s5_2 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669039749/1250000000 : ℝ)*x 0 + (5216902223/10000000000 : ℝ)*x 1 + (-249888659/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669039749/1250000000 : ℝ)^4495 ≤ (5563748398059/12500000000000 : ℝ)^3471 := by
    have hnat : (669039749 : ℕ)^4495*12500000000000^3471 ≤ 5563748398059^3471*1250000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669039749 1250000000 5563748398059 12500000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5216902223/10000000000 : ℝ)^4495 ≤ (2691069922973/6250000000000 : ℝ)^3471 := by
    have hnat : (5216902223 : ℕ)^4495*6250000000000^3471 ≤ 2691069922973^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5216902223 10000000000 2691069922973 6250000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249888659/1250000000 : ℝ)^4495 ≤ (2486578806883/20000000000000 : ℝ)^3471 := by
    have hnat : (249888659 : ℕ)^4495*20000000000000^3471 ≤ 2486578806883^3471*1250000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249888659 1250000000 2486578806883 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669039749/1250000000 : ℝ), (5216902223/10000000000 : ℝ), (-249888659/1250000000 : ℝ)] ![(5563748398059/12500000000000 : ℝ), (2691069922973/6250000000000 : ℝ), (2486578806883/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669039749/1250000000 : ℝ)|^4495 ≤ (5563748398059/12500000000000 : ℝ)^3471
        have hw : |(669039749/1250000000 : ℝ)|=(669039749/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5216902223/10000000000 : ℝ)|^4495 ≤ (2691069922973/6250000000000 : ℝ)^3471
        have hw : |(5216902223/10000000000 : ℝ)|=(5216902223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-249888659/1250000000 : ℝ)|^4495 ≤ (2486578806883/20000000000000 : ℝ)^3471
        have hw : |(-249888659/1250000000 : ℝ)|=(249888659/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s5_3 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1068964911/2500000000 : ℝ)*x 0 + (4036886323/10000000000 : ℝ)*x 1 + (1131720307/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068964911/2500000000 : ℝ)^4495 ≤ (8319735473133/25000000000000 : ℝ)^3471 := by
    have hnat : (1068964911 : ℕ)^4495*25000000000000^3471 ≤ 8319735473133^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068964911 2500000000 8319735473133 25000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4036886323/10000000000 : ℝ)^4495 ≤ (30890433359269/100000000000000 : ℝ)^3471 := by
    have hnat : (4036886323 : ℕ)^4495*100000000000000^3471 ≤ 30890433359269^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4036886323 10000000000 30890433359269 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1131720307/2500000000 : ℝ)^4495 ≤ (7166124946879/20000000000000 : ℝ)^3471 := by
    have hnat : (1131720307 : ℕ)^4495*20000000000000^3471 ≤ 7166124946879^3471*2500000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1131720307 2500000000 7166124946879 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068964911/2500000000 : ℝ), (4036886323/10000000000 : ℝ), (1131720307/2500000000 : ℝ)] ![(8319735473133/25000000000000 : ℝ), (30890433359269/100000000000000 : ℝ), (7166124946879/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068964911/2500000000 : ℝ)|^4495 ≤ (8319735473133/25000000000000 : ℝ)^3471
        have hw : |(1068964911/2500000000 : ℝ)|=(1068964911/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4036886323/10000000000 : ℝ)|^4495 ≤ (30890433359269/100000000000000 : ℝ)^3471
        have hw : |(4036886323/10000000000 : ℝ)|=(4036886323/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1131720307/2500000000 : ℝ)|^4495 ≤ (7166124946879/20000000000000 : ℝ)^3471
        have hw : |(1131720307/2500000000 : ℝ)|=(1131720307/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s5_4 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-943708099/5000000000 : ℝ)*x 0 + (5218022471/10000000000 : ℝ)*x 1 + (5433856639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (943708099/5000000000 : ℝ)^4495 ≤ (5770416658059/50000000000000 : ℝ)^3471 := by
    have hnat : (943708099 : ℕ)^4495*50000000000000^3471 ≤ 5770416658059^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      943708099 5000000000 5770416658059 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218022471/10000000000 : ℝ)^4495 ≤ (8613818531617/20000000000000 : ℝ)^3471 := by
    have hnat : (5218022471 : ℕ)^4495*20000000000000^3471 ≤ 8613818531617^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218022471 10000000000 8613818531617 20000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433856639/10000000000 : ℝ)^4495 ≤ (45390074014157/100000000000000 : ℝ)^3471 := by
    have hnat : (5433856639 : ℕ)^4495*100000000000000^3471 ≤ 45390074014157^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433856639 10000000000 45390074014157 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-943708099/5000000000 : ℝ), (5218022471/10000000000 : ℝ), (5433856639/10000000000 : ℝ)] ![(5770416658059/50000000000000 : ℝ), (8613818531617/20000000000000 : ℝ), (45390074014157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-943708099/5000000000 : ℝ)|^4495 ≤ (5770416658059/50000000000000 : ℝ)^3471
        have hw : |(-943708099/5000000000 : ℝ)|=(943708099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218022471/10000000000 : ℝ)|^4495 ≤ (8613818531617/20000000000000 : ℝ)^3471
        have hw : |(5218022471/10000000000 : ℝ)|=(5218022471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433856639/10000000000 : ℝ)|^4495 ≤ (45390074014157/100000000000000 : ℝ)^3471
        have hw : |(5433856639/10000000000 : ℝ)|=(5433856639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s5_5 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295183803/10000000000 : ℝ)*x 0 + (-222769357/1250000000 : ℝ)*x 1 + (5433856639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295183803/10000000000 : ℝ)^4495 ≤ (5486957345563/12500000000000 : ℝ)^3471 := by
    have hnat : (5295183803 : ℕ)^4495*12500000000000^3471 ≤ 5486957345563^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295183803 10000000000 5486957345563 12500000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (222769357/1250000000 : ℝ)^4495 ≤ (5357133605931/50000000000000 : ℝ)^3471 := by
    have hnat : (222769357 : ℕ)^4495*50000000000000^3471 ≤ 5357133605931^3471*1250000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222769357 1250000000 5357133605931 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5433856639/10000000000 : ℝ)^4495 ≤ (45390074014157/100000000000000 : ℝ)^3471 := by
    have hnat : (5433856639 : ℕ)^4495*100000000000000^3471 ≤ 45390074014157^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433856639 10000000000 45390074014157 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295183803/10000000000 : ℝ), (-222769357/1250000000 : ℝ), (5433856639/10000000000 : ℝ)] ![(5486957345563/12500000000000 : ℝ), (5357133605931/50000000000000 : ℝ), (45390074014157/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295183803/10000000000 : ℝ)|^4495 ≤ (5486957345563/12500000000000 : ℝ)^3471
        have hw : |(5295183803/10000000000 : ℝ)|=(5295183803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-222769357/1250000000 : ℝ)|^4495 ≤ (5357133605931/50000000000000 : ℝ)^3471
        have hw : |(-222769357/1250000000 : ℝ)|=(222769357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5433856639/10000000000 : ℝ)|^4495 ≤ (45390074014157/100000000000000 : ℝ)^3471
        have hw : |(5433856639/10000000000 : ℝ)|=(5433856639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s5_6 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5295183803/10000000000 : ℝ)*x 0 + (5433856639/10000000000 : ℝ)*x 1 + (-222769357/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5295183803/10000000000 : ℝ)^4495 ≤ (5486957345563/12500000000000 : ℝ)^3471 := by
    have hnat : (5295183803 : ℕ)^4495*12500000000000^3471 ≤ 5486957345563^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5295183803 10000000000 5486957345563 12500000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5433856639/10000000000 : ℝ)^4495 ≤ (45390074014157/100000000000000 : ℝ)^3471 := by
    have hnat : (5433856639 : ℕ)^4495*100000000000000^3471 ≤ 45390074014157^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5433856639 10000000000 45390074014157 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (222769357/1250000000 : ℝ)^4495 ≤ (5357133605931/50000000000000 : ℝ)^3471 := by
    have hnat : (222769357 : ℕ)^4495*50000000000000^3471 ≤ 5357133605931^3471*1250000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      222769357 1250000000 5357133605931 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5295183803/10000000000 : ℝ), (5433856639/10000000000 : ℝ), (-222769357/1250000000 : ℝ)] ![(5486957345563/12500000000000 : ℝ), (45390074014157/100000000000000 : ℝ), (5357133605931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5295183803/10000000000 : ℝ)|^4495 ≤ (5486957345563/12500000000000 : ℝ)^3471
        have hw : |(5295183803/10000000000 : ℝ)|=(5295183803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5433856639/10000000000 : ℝ)|^4495 ≤ (45390074014157/100000000000000 : ℝ)^3471
        have hw : |(5433856639/10000000000 : ℝ)|=(5433856639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-222769357/1250000000 : ℝ)|^4495 ≤ (5357133605931/50000000000000 : ℝ)^3471
        have hw : |(-222769357/1250000000 : ℝ)|=(222769357/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1499_s5_7 (p : ℝ) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2137963023/5000000000 : ℝ)*x 0 + (4524364229/10000000000 : ℝ)*x 1 + (126231933/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2137963023/5000000000 : ℝ)^4495 ≤ (16639805582767/50000000000000 : ℝ)^3471 := by
    have hnat : (2137963023 : ℕ)^4495*50000000000000^3471 ≤ 16639805582767^3471*5000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2137963023 5000000000 16639805582767 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4524364229/10000000000 : ℝ)^4495 ≤ (35804827224923/100000000000000 : ℝ)^3471 := by
    have hnat : (4524364229 : ℕ)^4495*100000000000000^3471 ≤ 35804827224923^3471*10000000000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4524364229 10000000000 35804827224923 100000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (126231933/312500000 : ℝ)^4495 ≤ (15457780799293/50000000000000 : ℝ)^3471 := by
    have hnat : (126231933 : ℕ)^4495*50000000000000^3471 ≤ 15457780799293^3471*312500000^4495 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      126231933 312500000 15457780799293 50000000000000 4495 3471 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4495/1024 : ℝ)) 4495 3471 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2137963023/5000000000 : ℝ), (4524364229/10000000000 : ℝ), (126231933/312500000 : ℝ)] ![(16639805582767/50000000000000 : ℝ), (35804827224923/100000000000000 : ℝ), (15457780799293/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2137963023/5000000000 : ℝ)|^4495 ≤ (16639805582767/50000000000000 : ℝ)^3471
        have hw : |(2137963023/5000000000 : ℝ)|=(2137963023/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4524364229/10000000000 : ℝ)|^4495 ≤ (35804827224923/100000000000000 : ℝ)^3471
        have hw : |(4524364229/10000000000 : ℝ)|=(4524364229/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(126231933/312500000 : ℝ)|^4495 ≤ (15457780799293/50000000000000 : ℝ)^3471
        have hw : |(126231933/312500000 : ℝ)|=(126231933/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1499_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2171/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (679/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15481/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2171/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2171/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2171/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2171/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2171/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2171/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2171/20000 : ℝ) ^ (4493/1024 : ℝ) ≤ (2934996044045979/50000000000000000000 : ℝ) := by
    have hpowers : (2171/20000 : ℝ)^4493 ≤ (2934996044045979/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2171 : ℕ)^4493*50000000000000000000^1024 ≤ 2934996044045979^1024*20000^4493 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2171 20000 2934996044045979 50000000000000000000 4493 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2171/20000 : ℝ)) (X := (2934996044045979/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4493/1024 : ℝ) ≤ (27937812757773123/100000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4493 ≤ (27937812757773123/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4493*100000000000000000000^1024 ≤ 27937812757773123^1024*10000^4493 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 27937812757773123 100000000000000000000 4493 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (27937812757773123/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002934996044045979/25000000000000000000 : ℝ) ≤ (10000267553950353/10000000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (25002934996044045979/25000000000000000000 : ℝ)^1024 ≤ (10000267553950353/10000000000000000 : ℝ)^4493 := by
      have hnat : (25002934996044045979 : ℕ)^1024*10000000000000000^4493 ≤ 10000267553950353^4493*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002934996044045979 25000000000000000000 10000267553950353 10000000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000267553950353/10000000000000000 : ℝ)) (X := (25002934996044045979/25000000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100033807804845865081/100000000000000000000 : ℝ) ≤ (10000770413416389/10000000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (100033807804845865081/100000000000000000000 : ℝ)^1024 ≤ (10000770413416389/10000000000000000 : ℝ)^4493 := by
      have hnat : (100033807804845865081 : ℕ)^1024*10000000000000000^4493 ≤ 10000770413416389^4493*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100033807804845865081 100000000000000000000 10000770413416389 10000000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000770413416389/10000000000000000 : ℝ)) (X := (100033807804845865081/100000000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50027937812757773123/50000000000000000000 : ℝ) ≤ (400050930915297/400000000000000 : ℝ) ^ (4493/1024 : ℝ) := by
    have hpowers : (50027937812757773123/50000000000000000000 : ℝ)^1024 ≤ (400050930915297/400000000000000 : ℝ)^4493 := by
      have hnat : (50027937812757773123 : ℕ)^1024*400000000000000^4493 ≤ 400050930915297^4493*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50027937812757773123 50000000000000000000 400050930915297 400000000000000 1024 4493 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400050930915297/400000000000000 : ℝ)) (X := (50027937812757773123/50000000000000000000 : ℝ)) (by norm_num) 4493 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2934996044045979/50000000000000000000 : ℝ) ≤ ((1029784956301160991/1030000000000000000 : ℝ)+2*(13968318501/12875000000000 : ℝ)*(2171/20000 : ℝ))^(4493/1024 : ℝ) := by
    rw [show (1029784956301160991/1030000000000000000 : ℝ)+2*(13968318501/12875000000000 : ℝ)*(2171/20000 : ℝ)=(10000267553950353/10000000000000000 : ℝ) by norm_num, show 1+2*(2934996044045979/50000000000000000000 : ℝ)=(25002934996044045979/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27937812757773123/100000000000000000000 : ℝ)+(2934996044045979/50000000000000000000 : ℝ) ≤ ((1029784956301160991/1030000000000000000 : ℝ)+(13968318501/12875000000000 : ℝ)*((1549/10000 : ℝ)+(2171/20000 : ℝ)))^(4493/1024 : ℝ) := by
    rw [show (1029784956301160991/1030000000000000000 : ℝ)+(13968318501/12875000000000 : ℝ)*((1549/10000 : ℝ)+(2171/20000 : ℝ))=(10000770413416389/10000000000000000 : ℝ) by norm_num, show 1+(27937812757773123/100000000000000000000 : ℝ)+(2934996044045979/50000000000000000000 : ℝ)=(100033807804845865081/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27937812757773123/100000000000000000000 : ℝ) ≤ ((1029784956301160991/1030000000000000000 : ℝ)+2*(13968318501/12875000000000 : ℝ)*(1549/10000 : ℝ))^(4493/1024 : ℝ) := by
    rw [show (1029784956301160991/1030000000000000000 : ℝ)+2*(13968318501/12875000000000 : ℝ)*(1549/10000 : ℝ)=(400050930915297/400000000000000 : ℝ) by norm_num, show 1+2*(27937812757773123/100000000000000000000 : ℝ)=(50027937812757773123/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1029784956301160991/1030000000000000000 : ℝ)*(X 1 0+X 2 0)+(13968318501/12875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (2171/20000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (1029784956301160991/1030000000000000000 : ℝ)) (alpha := (13968318501/12875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1029784956301160991/1030000000000000000 : ℝ)*(X 0 1+X 2 1)+(13968318501/12875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (2171/20000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (1029784956301160991/1030000000000000000 : ℝ)) (alpha := (13968318501/12875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1029784956301160991/1030000000000000000 : ℝ)*(X 0 2+X 1 2)+(13968318501/12875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4493/1024 : ℝ)) (lo := (2171/20000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (1029784956301160991/1030000000000000000 : ℝ)) (alpha := (13968318501/12875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1887386643/10000000000 : ℝ)*X 0 0+(1086997027/2000000000 : ℝ)*X 0 1+(208676089/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352317991/10000000000 : ℝ)*X 1 0+(-1999109271/10000000000 : ℝ)*X 1 1+(326056389/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((669039749/1250000000 : ℝ)*X 2 0+(5216902223/10000000000 : ℝ)*X 2 1+(-249888659/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1068964911/2500000000 : ℝ)*X 0 0+(4036886323/10000000000 : ℝ)*X 0 1+(1131720307/2500000000 : ℝ)*X 0 2+(1068964911/2500000000 : ℝ)*X 1 0+(4036886323/10000000000 : ℝ)*X 1 1+(1131720307/2500000000 : ℝ)*X 1 2+(1068964911/2500000000 : ℝ)*X 2 0+(4036886323/10000000000 : ℝ)*X 2 1+(1131720307/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-943708099/5000000000 : ℝ)*X 0 0+(5218022471/10000000000 : ℝ)*X 0 1+(5433856639/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5295183803/10000000000 : ℝ)*X 1 0+(-222769357/1250000000 : ℝ)*X 1 1+(5433856639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5295183803/10000000000 : ℝ)*X 2 0+(5433856639/10000000000 : ℝ)*X 2 1+(-222769357/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2137963023/5000000000 : ℝ)*X 0 0+(4524364229/10000000000 : ℝ)*X 0 1+(126231933/312500000 : ℝ)*X 0 2+(2137963023/5000000000 : ℝ)*X 1 0+(4524364229/10000000000 : ℝ)*X 1 1+(126231933/312500000 : ℝ)*X 1 2+(2137963023/5000000000 : ℝ)*X 2 0+(4524364229/10000000000 : ℝ)*X 2 1+(126231933/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1499_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1826112937574340717333/643750000000000000000000000 : ℝ) := by norm_num
    linear_combination (250633911/50000000000000 : ℝ)*(base19) + (23340553/5000000000000 : ℝ)*(base23) + (9450449/50000000000000 : ℝ)*(lower2) + (2228373/3125000000000 : ℝ)*(upper3) + (5624727/12500000000000 : ℝ)*(upper5) + (828284072430647/25000000000000 : ℝ)*(major0) + (828284072430647/25000000000000 : ℝ)*(major1) + (828284072430647/25000000000000 : ℝ)*(major2) + (4585420127507861/100000000000000 : ℝ)*(sp0) + (2292713684781749/50000000000000 : ℝ)*(sp1) + (229271370201013/5000000000000 : ℝ)*(sp2) + (2040840867747123/100000000000000 : ℝ)*(sp3) + (7743323459/100000000000000 : ℝ)*(sp4) + (1873155359/50000000000000 : ℝ)*(sp7) + (2040844614057841/100000000000000 : ℝ)*(f.failure) + (114635696770783/2500000000000 : ℝ)*(f.sum) + (9490351984727/2575000000000000000000000000 : ℝ)*base65 + (201077483134801177/25750000000000000000000000000000 : ℝ)*base67 + (160635920982551177/25750000000000000000000000000000 : ℝ)*base69 + (53110015827448823/25750000000000000000000000000000 : ℝ)*base72 + (8239572880377/2575000000000000000000000000 : ℝ)*base73 + (180755893061948823/25750000000000000000000000000000 : ℝ)*base76 + (86758180071051177/25750000000000000000000000000000 : ℝ)*base77 + (188183839182198823/25750000000000000000000000000000 : ℝ)*base80 + (2221285375613/643750000000000000000000000 : ℝ)*base81 + (4365763/2500000000000000000000 : ℝ)*base90 + (4365763/2500000000000000000000 : ℝ)*base92 + (4365763/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2224121054412958174836597/257500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1414769699/100000000000000 : ℝ)*(base19) + (1535926319/100000000000000 : ℝ)*(base23) + (29243189/6250000000000 : ℝ)*(lower1) + (44528277/25000000000000 : ℝ)*(upper3) + (54782131/100000000000000 : ℝ)*(lower4) + (3557223/2000000000000 : ℝ)*(upper5) + (33476275768411/1000000000000 : ℝ)*(major0) + (33476275768411/1000000000000 : ℝ)*(major1) + (33476275768411/1000000000000 : ℝ)*(major2) + (328088089/20000000000000 : ℝ)*(sp2) + (4633164111682893/100000000000000 : ℝ)*(sp4) + (4633162696913193/100000000000000 : ℝ)*(sp5) + (144786279228629/3125000000000 : ℝ)*(sp6) + (1031045377043591/50000000000000 : ℝ)*(sp7) + (1031045377043591/50000000000000 : ℝ)*(f.failure) + (4633164111682893/100000000000000 : ℝ)*(f.sum) + (90911964949/51500000000000000000000000 : ℝ)*base66 + (5278937376705301/1030000000000000000000000000000 : ℝ)*base67 + (185561484565301/1030000000000000000000000000000 : ℝ)*base69 + (25512556315394699/1030000000000000000000000000000 : ℝ)*base72 + (64747694417/51500000000000000000000000 : ℝ)*base74 + (58896630933565301/1030000000000000000000000000000 : ℝ)*base75 + (2732465992255301/1030000000000000000000000000000 : ℝ)*base77 + (8764566119985301/1030000000000000000000000000000 : ℝ)*base79 + (47779968297/12875000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4703013/1250000000000000000000 : ℝ)*base90 + (4703013/1250000000000000000000 : ℝ)*base92 + (4703013/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1499_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2171/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (679/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1499_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1499_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1003/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (679/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1499_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1499_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1499_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4493/1024 : ℝ) ≤ p) (hpb : p ≤ (4495/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (40585357/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1003/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5171/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (679/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15481/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1499_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
