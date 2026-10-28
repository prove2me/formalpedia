-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1235_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:16:30.948011+00:00
-- url     : https://prove2.me/submissions/c5fb9d6a-5aa9-4e41-ae29-c73ddf4c1af1

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
theorem support_rectangle_w1235_s0_0 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-74508877/400000000 : ℝ)*x 0 + (3016542159/5000000000 : ℝ)*x 1 + (4792120403/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (74508877/400000000 : ℝ)^2107 ≤ (10860835977989/100000000000000 : ℝ)^1595 := by
    have hnat : (74508877 : ℕ)^2107*100000000000000^1595 ≤ 10860835977989^1595*400000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      74508877 400000000 10860835977989 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3016542159/5000000000 : ℝ)^2107 ≤ (51296986515937/100000000000000 : ℝ)^1595 := by
    have hnat : (3016542159 : ℕ)^2107*100000000000000^1595 ≤ 51296986515937^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3016542159 5000000000 51296986515937 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4792120403/10000000000 : ℝ)^2107 ≤ (37842177486367/100000000000000 : ℝ)^1595 := by
    have hnat : (4792120403 : ℕ)^2107*100000000000000^1595 ≤ 37842177486367^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792120403 10000000000 37842177486367 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-74508877/400000000 : ℝ), (3016542159/5000000000 : ℝ), (4792120403/10000000000 : ℝ)] ![(10860835977989/100000000000000 : ℝ), (51296986515937/100000000000000 : ℝ), (37842177486367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-74508877/400000000 : ℝ)|^2107 ≤ (10860835977989/100000000000000 : ℝ)^1595
        have hw : |(-74508877/400000000 : ℝ)|=(74508877/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3016542159/5000000000 : ℝ)|^2107 ≤ (51296986515937/100000000000000 : ℝ)^1595
        have hw : |(3016542159/5000000000 : ℝ)|=(3016542159/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4792120403/10000000000 : ℝ)|^2107 ≤ (37842177486367/100000000000000 : ℝ)^1595
        have hw : |(4792120403/10000000000 : ℝ)|=(4792120403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s0_1 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5511553851/10000000000 : ℝ)*x 0 + (-1286169887/5000000000 : ℝ)*x 1 + (958424071/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5511553851/10000000000 : ℝ)^2107 ≤ (1422565386603/3125000000000 : ℝ)^1595 := by
    have hnat : (5511553851 : ℕ)^2107*3125000000000^1595 ≤ 1422565386603^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511553851 10000000000 1422565386603 3125000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1286169887/5000000000 : ℝ)^2107 ≤ (1663573062047/10000000000000 : ℝ)^1595 := by
    have hnat : (1286169887 : ℕ)^2107*10000000000000^1595 ≤ 1663573062047^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1286169887 5000000000 1663573062047 10000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (958424071/2000000000 : ℝ)^2107 ≤ (37842176985649/100000000000000 : ℝ)^1595 := by
    have hnat : (958424071 : ℕ)^2107*100000000000000^1595 ≤ 37842176985649^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      958424071 2000000000 37842176985649 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5511553851/10000000000 : ℝ), (-1286169887/5000000000 : ℝ), (958424071/2000000000 : ℝ)] ![(1422565386603/3125000000000 : ℝ), (1663573062047/10000000000000 : ℝ), (37842176985649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5511553851/10000000000 : ℝ)|^2107 ≤ (1422565386603/3125000000000 : ℝ)^1595
        have hw : |(5511553851/10000000000 : ℝ)|=(5511553851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1286169887/5000000000 : ℝ)|^2107 ≤ (1663573062047/10000000000000 : ℝ)^1595
        have hw : |(-1286169887/5000000000 : ℝ)|=(1286169887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(958424071/2000000000 : ℝ)|^2107 ≤ (37842176985649/100000000000000 : ℝ)^1595
        have hw : |(958424071/2000000000 : ℝ)|=(958424071/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s0_2 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1377888447/2500000000 : ℝ)*x 0 + (4792120421/10000000000 : ℝ)*x 1 + (-102893591/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1377888447/2500000000 : ℝ)^2107 ≤ (45522091683923/100000000000000 : ℝ)^1595 := by
    have hnat : (1377888447 : ℕ)^2107*100000000000000^1595 ≤ 45522091683923^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1377888447 2500000000 45522091683923 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4792120421/10000000000 : ℝ)^2107 ≤ (4730272209267/12500000000000 : ℝ)^1595 := by
    have hnat : (4792120421 : ℕ)^2107*12500000000000^1595 ≤ 4730272209267^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4792120421 10000000000 4730272209267 12500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (102893591/400000000 : ℝ)^2107 ≤ (16635730629013/100000000000000 : ℝ)^1595 := by
    have hnat : (102893591 : ℕ)^2107*100000000000000^1595 ≤ 16635730629013^1595*400000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102893591 400000000 16635730629013 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1377888447/2500000000 : ℝ), (4792120421/10000000000 : ℝ), (-102893591/400000000 : ℝ)] ![(45522091683923/100000000000000 : ℝ), (4730272209267/12500000000000 : ℝ), (16635730629013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1377888447/2500000000 : ℝ)|^2107 ≤ (45522091683923/100000000000000 : ℝ)^1595
        have hw : |(1377888447/2500000000 : ℝ)|=(1377888447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4792120421/10000000000 : ℝ)|^2107 ≤ (4730272209267/12500000000000 : ℝ)^1595
        have hw : |(4792120421/10000000000 : ℝ)|=(4792120421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-102893591/400000000 : ℝ)|^2107 ≤ (16635730629013/100000000000000 : ℝ)^1595
        have hw : |(-102893591/400000000 : ℝ)|=(102893591/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s0_3 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (419357189/1000000000 : ℝ)*x 0 + (3117155673/10000000000 : ℝ)*x 1 + (5631136289/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (419357189/1000000000 : ℝ)^2107 ≤ (6345449596011/20000000000000 : ℝ)^1595 := by
    have hnat : (419357189 : ℕ)^2107*20000000000000^1595 ≤ 6345449596011^1595*1000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      419357189 1000000000 6345449596011 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3117155673/10000000000 : ℝ)^2107 ≤ (5360352984759/25000000000000 : ℝ)^1595 := by
    have hnat : (3117155673 : ℕ)^2107*25000000000000^1595 ≤ 5360352984759^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3117155673 10000000000 5360352984759 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5631136289/10000000000 : ℝ)^2107 ≤ (46831340062687/100000000000000 : ℝ)^1595 := by
    have hnat : (5631136289 : ℕ)^2107*100000000000000^1595 ≤ 46831340062687^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5631136289 10000000000 46831340062687 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(419357189/1000000000 : ℝ), (3117155673/10000000000 : ℝ), (5631136289/10000000000 : ℝ)] ![(6345449596011/20000000000000 : ℝ), (5360352984759/25000000000000 : ℝ), (46831340062687/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(419357189/1000000000 : ℝ)|^2107 ≤ (6345449596011/20000000000000 : ℝ)^1595
        have hw : |(419357189/1000000000 : ℝ)|=(419357189/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3117155673/10000000000 : ℝ)|^2107 ≤ (5360352984759/25000000000000 : ℝ)^1595
        have hw : |(3117155673/10000000000 : ℝ)|=(3117155673/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5631136289/10000000000 : ℝ)|^2107 ≤ (46831340062687/100000000000000 : ℝ)^1595
        have hw : |(5631136289/10000000000 : ℝ)|=(5631136289/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s0_4 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-233449919/1250000000 : ℝ)*x 0 + (241204123/500000000 : ℝ)*x 1 + (299999639/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (233449919/1250000000 : ℝ)^2107 ≤ (340575595179/3125000000000 : ℝ)^1595 := by
    have hnat : (233449919 : ℕ)^2107*3125000000000^1595 ≤ 340575595179^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233449919 1250000000 340575595179 3125000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (241204123/500000000 : ℝ)^2107 ≤ (19087975138941/50000000000000 : ℝ)^1595 := by
    have hnat : (241204123 : ℕ)^2107*50000000000000^1595 ≤ 19087975138941^1595*500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241204123 500000000 19087975138941 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (299999639/500000000 : ℝ)^2107 ≤ (1018512613119/2000000000000 : ℝ)^1595 := by
    have hnat : (299999639 : ℕ)^2107*2000000000000^1595 ≤ 1018512613119^1595*500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      299999639 500000000 1018512613119 2000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-233449919/1250000000 : ℝ), (241204123/500000000 : ℝ), (299999639/500000000 : ℝ)] ![(340575595179/3125000000000 : ℝ), (19087975138941/50000000000000 : ℝ), (1018512613119/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-233449919/1250000000 : ℝ)|^2107 ≤ (340575595179/3125000000000 : ℝ)^1595
        have hw : |(-233449919/1250000000 : ℝ)|=(233449919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(241204123/500000000 : ℝ)|^2107 ≤ (19087975138941/50000000000000 : ℝ)^1595
        have hw : |(241204123/500000000 : ℝ)|=(241204123/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(299999639/500000000 : ℝ)|^2107 ≤ (1018512613119/2000000000000 : ℝ)^1595
        have hw : |(299999639/500000000 : ℝ)|=(299999639/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s0_5 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2586967407/5000000000 : ℝ)*x 0 + (-682232619/5000000000 : ℝ)*x 1 + (2999997491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2586967407/5000000000 : ℝ)^2107 ≤ (20937584920577/50000000000000 : ℝ)^1595 := by
    have hnat : (2586967407 : ℕ)^2107*50000000000000^1595 ≤ 20937584920577^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586967407 5000000000 20937584920577 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (682232619/5000000000 : ℝ)^2107 ≤ (1799793700757/25000000000000 : ℝ)^1595 := by
    have hnat : (682232619 : ℕ)^2107*25000000000000^1595 ≤ 1799793700757^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682232619 5000000000 1799793700757 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2999997491/5000000000 : ℝ)^2107 ≤ (25462827672571/50000000000000 : ℝ)^1595 := by
    have hnat : (2999997491 : ℕ)^2107*50000000000000^1595 ≤ 25462827672571^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2999997491 5000000000 25462827672571 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2586967407/5000000000 : ℝ), (-682232619/5000000000 : ℝ), (2999997491/5000000000 : ℝ)] ![(20937584920577/50000000000000 : ℝ), (1799793700757/25000000000000 : ℝ), (25462827672571/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2586967407/5000000000 : ℝ)|^2107 ≤ (20937584920577/50000000000000 : ℝ)^1595
        have hw : |(2586967407/5000000000 : ℝ)|=(2586967407/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-682232619/5000000000 : ℝ)|^2107 ≤ (1799793700757/25000000000000 : ℝ)^1595
        have hw : |(-682232619/5000000000 : ℝ)|=(682232619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2999997491/5000000000 : ℝ)|^2107 ≤ (25462827672571/50000000000000 : ℝ)^1595
        have hw : |(2999997491/5000000000 : ℝ)|=(2999997491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s0_6 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5173935651/10000000000 : ℝ)*x 0 + (1199998653/2000000000 : ℝ)*x 1 + (-272893343/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5173935651/10000000000 : ℝ)^2107 ≤ (41875178789957/100000000000000 : ℝ)^1595 := by
    have hnat : (5173935651 : ℕ)^2107*100000000000000^1595 ≤ 41875178789957^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5173935651 10000000000 41875178789957 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1199998653/2000000000 : ℝ)^2107 ≤ (50925636093851/100000000000000 : ℝ)^1595 := by
    have hnat : (1199998653 : ℕ)^2107*100000000000000^1595 ≤ 50925636093851^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1199998653 2000000000 50925636093851 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272893343/2000000000 : ℝ)^2107 ≤ (3599592548757/50000000000000 : ℝ)^1595 := by
    have hnat : (272893343 : ℕ)^2107*50000000000000^1595 ≤ 3599592548757^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272893343 2000000000 3599592548757 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5173935651/10000000000 : ℝ), (1199998653/2000000000 : ℝ), (-272893343/2000000000 : ℝ)] ![(41875178789957/100000000000000 : ℝ), (50925636093851/100000000000000 : ℝ), (3599592548757/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5173935651/10000000000 : ℝ)|^2107 ≤ (41875178789957/100000000000000 : ℝ)^1595
        have hw : |(5173935651/10000000000 : ℝ)|=(5173935651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1199998653/2000000000 : ℝ)|^2107 ≤ (50925636093851/100000000000000 : ℝ)^1595
        have hw : |(1199998653/2000000000 : ℝ)|=(1199998653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-272893343/2000000000 : ℝ)|^2107 ≤ (3599592548757/50000000000000 : ℝ)^1595
        have hw : |(-272893343/2000000000 : ℝ)|=(272893343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s0_7 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (840690643/2000000000 : ℝ)*x 0 + (2783195809/5000000000 : ℝ)*x 1 + (3184187809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840690643/2000000000 : ℝ)^2107 ≤ (15913021092417/50000000000000 : ℝ)^1595 := by
    have hnat : (840690643 : ℕ)^2107*50000000000000^1595 ≤ 15913021092417^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840690643 2000000000 15913021092417 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2783195809/5000000000 : ℝ)^2107 ≤ (230606816439/500000000000 : ℝ)^1595 := by
    have hnat : (2783195809 : ℕ)^2107*500000000000^1595 ≤ 230606816439^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2783195809 5000000000 230606816439 500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3184187809/10000000000 : ℝ)^2107 ≤ (22052594512283/100000000000000 : ℝ)^1595 := by
    have hnat : (3184187809 : ℕ)^2107*100000000000000^1595 ≤ 22052594512283^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3184187809 10000000000 22052594512283 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840690643/2000000000 : ℝ), (2783195809/5000000000 : ℝ), (3184187809/10000000000 : ℝ)] ![(15913021092417/50000000000000 : ℝ), (230606816439/500000000000 : ℝ), (22052594512283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840690643/2000000000 : ℝ)|^2107 ≤ (15913021092417/50000000000000 : ℝ)^1595
        have hw : |(840690643/2000000000 : ℝ)|=(840690643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2783195809/5000000000 : ℝ)|^2107 ≤ (230606816439/500000000000 : ℝ)^1595
        have hw : |(2783195809/5000000000 : ℝ)|=(2783195809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3184187809/10000000000 : ℝ)|^2107 ≤ (22052594512283/100000000000000 : ℝ)^1595
        have hw : |(3184187809/10000000000 : ℝ)|=(3184187809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1235_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (79/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (13731/50000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8427/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8427 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8427*1^2048 ≤ 0^2048*1^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8427/2048 : ℝ) ≤ (230450632146224213/10000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8427 ≤ (230450632146224213/10000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8427*10000000000000000000^2048 ≤ 230450632146224213^2048*5^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 230450632146224213 10000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (230450632146224213/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8427 := by
      have hnat : (1 : ℕ)^2048*1^8427 ≤ 1^8427*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10230450632146224213/10000000000000000000 : ℝ) ≤ (251388100800147/250000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (10230450632146224213/10000000000000000000 : ℝ)^2048 ≤ (251388100800147/250000000000000 : ℝ)^8427 := by
      have hnat : (10230450632146224213 : ℕ)^2048*250000000000000^8427 ≤ 251388100800147^8427*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10230450632146224213 10000000000000000000 251388100800147 250000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (251388100800147/250000000000000 : ℝ)) (X := (10230450632146224213/10000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (5230450632146224213/5000000000000000000 : ℝ) ≤ (126388100800147/125000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (5230450632146224213/5000000000000000000 : ℝ)^2048 ≤ (126388100800147/125000000000000 : ℝ)^8427 := by
      have hnat : (5230450632146224213 : ℕ)^2048*125000000000000^8427 ≤ 126388100800147^8427*5000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5230450632146224213 5000000000000000000 126388100800147 125000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (126388100800147/125000000000000 : ℝ)) (X := (5230450632146224213/5000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(1388100800147/100000000000000 : ℝ)*(0 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(1388100800147/100000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(230450632146224213/10000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(1388100800147/100000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8427/2048 : ℝ) := by
    rw [show (1 : ℝ)+(1388100800147/100000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(251388100800147/250000000000000 : ℝ) by norm_num, show 1+(230450632146224213/10000000000000000000 : ℝ)+(0 : ℝ)=(10230450632146224213/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(230450632146224213/10000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(1388100800147/100000000000000 : ℝ)*(2/5 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(1388100800147/100000000000000 : ℝ)*(2/5 : ℝ)=(126388100800147/125000000000000 : ℝ) by norm_num, show 1+2*(230450632146224213/10000000000000000000 : ℝ)=(5230450632146224213/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(1388100800147/100000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1388100800147/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(1388100800147/100000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1388100800147/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(1388100800147/100000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (1388100800147/100000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-74508877/400000000 : ℝ)*X 0 0+(3016542159/5000000000 : ℝ)*X 0 1+(4792120403/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5511553851/10000000000 : ℝ)*X 1 0+(-1286169887/5000000000 : ℝ)*X 1 1+(958424071/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1377888447/2500000000 : ℝ)*X 2 0+(4792120421/10000000000 : ℝ)*X 2 1+(-102893591/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((419357189/1000000000 : ℝ)*X 0 0+(3117155673/10000000000 : ℝ)*X 0 1+(5631136289/10000000000 : ℝ)*X 0 2+(419357189/1000000000 : ℝ)*X 1 0+(3117155673/10000000000 : ℝ)*X 1 1+(5631136289/10000000000 : ℝ)*X 1 2+(419357189/1000000000 : ℝ)*X 2 0+(3117155673/10000000000 : ℝ)*X 2 1+(5631136289/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-233449919/1250000000 : ℝ)*X 0 0+(241204123/500000000 : ℝ)*X 0 1+(299999639/500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2586967407/5000000000 : ℝ)*X 1 0+(-682232619/5000000000 : ℝ)*X 1 1+(2999997491/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5173935651/10000000000 : ℝ)*X 2 0+(1199998653/2000000000 : ℝ)*X 2 1+(-272893343/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((840690643/2000000000 : ℝ)*X 0 0+(2783195809/5000000000 : ℝ)*X 0 1+(3184187809/10000000000 : ℝ)*X 0 2+(840690643/2000000000 : ℝ)*X 1 0+(2783195809/5000000000 : ℝ)*X 1 1+(3184187809/10000000000 : ℝ)*X 1 2+(840690643/2000000000 : ℝ)*X 2 0+(2783195809/5000000000 : ℝ)*X 2 1+(3184187809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15486836198528691093123/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (37455861/50000000000000 : ℝ)*(base1) + (1510554441/100000000000000 : ℝ)*(base19) + (699997169/50000000000000 : ℝ)*(base23) + (25337253/25000000000000 : ℝ)*(base24) + (85261061/25000000000000 : ℝ)*(upper3) + (601806794256601/100000000000000 : ℝ)*(major0) + (601806794256601/100000000000000 : ℝ)*(major1) + (601806794256601/100000000000000 : ℝ)*(major2) + (805830323797749/100000000000000 : ℝ)*(sp0) + (80583209851877/10000000000000 : ℝ)*(sp1) + (805832107729861/100000000000000 : ℝ)*(sp2) + (49722134888599/12500000000000 : ℝ)*(sp3) + (210011699/6250000000000 : ℝ)*(sp4) + (104757133/4000000000000 : ℝ)*(sp7) + (397779772948839/100000000000000 : ℝ)*(f.failure) + (805833609073211/100000000000000 : ℝ)*(f.sum) + (12116964289653/5000000000000000000000000000 : ℝ)*base66 + (6513360359653/10000000000000000000000000000 : ℝ)*base68 + (15116335279653/10000000000000000000000000000 : ℝ)*base70 + (32629413729653/10000000000000000000000000000 : ℝ)*base72 + (4313857909653/5000000000000000000000000000 : ℝ)*base74 + (17012925109653/10000000000000000000000000000 : ℝ)*base76 + (45489215709653/10000000000000000000000000000 : ℝ)*base78 + (11541346949653/10000000000000000000000000000 : ℝ)*base80 + (16719971169653/5000000000000000000000000000 : ℝ)*base82 + (18506057/2500000000000000000000 : ℝ)*base89 + (18506057/2500000000000000000000 : ℝ)*base91 + (18506057/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4549183459671513977691/2500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31098359/50000000000000 : ℝ)*(base1) + (25414099/5000000000000 : ℝ)*(base19) + (607914091/100000000000000 : ℝ)*(base23) + (16190833/12500000000000 : ℝ)*(upper3) + (635092507962583/100000000000000 : ℝ)*(major0) + (635092507962583/100000000000000 : ℝ)*(major1) + (635092507962583/100000000000000 : ℝ)*(major2) + (1852240133/100000000000000 : ℝ)*(sp1) + (635412893/50000000000000 : ℝ)*(sp2) + (502176773/100000000000000 : ℝ)*(sp3) + (170080838149181/20000000000000 : ℝ)*(sp4) + (425200884013537/50000000000000 : ℝ)*(sp5) + (85040224980931/10000000000000 : ℝ)*(sp6) + (4197802623467/1000000000000 : ℝ)*(sp7) + (6559075417503/1562500000000 : ℝ)*(f.failure) + (850404128549187/100000000000000 : ℝ)*(f.sum) + (16187547349701/5000000000000000000000000000 : ℝ)*base65 + (53200335609701/10000000000000000000000000000 : ℝ)*base67 + (60239420929701/10000000000000000000000000000 : ℝ)*base69 + (57436958009701/10000000000000000000000000000 : ℝ)*base71 + (20106335524701/5000000000000000000000000000 : ℝ)*base73 + (31011581099701/10000000000000000000000000000 : ℝ)*base75 + (23426640419701/10000000000000000000000000000 : ℝ)*base77 + (17890868049701/10000000000000000000000000000 : ℝ)*base79 + (32485832414701/5000000000000000000000000000 : ℝ)*base81 + (106643/19531250000000000000 : ℝ)*base90 + (106643/19531250000000000000 : ℝ)*base92 + (106643/19531250000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1235_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (79/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (13731/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1235_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1235_s1_0 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-257580767/1250000000 : ℝ)*x 0 + (2838678863/5000000000 : ℝ)*x 1 + (1255288279/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257580767/1250000000 : ℝ)^2107 ≤ (620535126367/5000000000000 : ℝ)^1595 := by
    have hnat : (257580767 : ℕ)^2107*5000000000000^1595 ≤ 620535126367^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257580767 1250000000 620535126367 5000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2838678863/5000000000 : ℝ)^2107 ≤ (184921102053/390625000000 : ℝ)^1595 := by
    have hnat : (2838678863 : ℕ)^2107*390625000000^1595 ≤ 184921102053^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2838678863 5000000000 184921102053 390625000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1255288279/2500000000 : ℝ)^2107 ≤ (40249495336741/100000000000000 : ℝ)^1595 := by
    have hnat : (1255288279 : ℕ)^2107*100000000000000^1595 ≤ 40249495336741^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1255288279 2500000000 40249495336741 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257580767/1250000000 : ℝ), (2838678863/5000000000 : ℝ), (1255288279/2500000000 : ℝ)] ![(620535126367/5000000000000 : ℝ), (184921102053/390625000000 : ℝ), (40249495336741/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257580767/1250000000 : ℝ)|^2107 ≤ (620535126367/5000000000000 : ℝ)^1595
        have hw : |(-257580767/1250000000 : ℝ)|=(257580767/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2838678863/5000000000 : ℝ)|^2107 ≤ (184921102053/390625000000 : ℝ)^1595
        have hw : |(2838678863/5000000000 : ℝ)|=(2838678863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1255288279/2500000000 : ℝ)|^2107 ≤ (40249495336741/100000000000000 : ℝ)^1595
        have hw : |(1255288279/2500000000 : ℝ)|=(1255288279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s1_1 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5414036233/10000000000 : ℝ)*x 0 + (-30164239/125000000 : ℝ)*x 1 + (200846127/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5414036233/10000000000 : ℝ)^2107 ≤ (44461142076773/100000000000000 : ℝ)^1595 := by
    have hnat : (5414036233 : ℕ)^2107*100000000000000^1595 ≤ 44461142076773^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414036233 10000000000 44461142076773 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30164239/125000000 : ℝ)^2107 ≤ (15289361961361/100000000000000 : ℝ)^1595 := by
    have hnat : (30164239 : ℕ)^2107*100000000000000^1595 ≤ 15289361961361^1595*125000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30164239 125000000 15289361961361 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (200846127/400000000 : ℝ)^2107 ≤ (40249495961501/100000000000000 : ℝ)^1595 := by
    have hnat : (200846127 : ℕ)^2107*100000000000000^1595 ≤ 40249495961501^1595*400000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200846127 400000000 40249495961501 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5414036233/10000000000 : ℝ), (-30164239/125000000 : ℝ), (200846127/400000000 : ℝ)] ![(44461142076773/100000000000000 : ℝ), (15289361961361/100000000000000 : ℝ), (40249495961501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5414036233/10000000000 : ℝ)|^2107 ≤ (44461142076773/100000000000000 : ℝ)^1595
        have hw : |(5414036233/10000000000 : ℝ)|=(5414036233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-30164239/125000000 : ℝ)|^2107 ≤ (15289361961361/100000000000000 : ℝ)^1595
        have hw : |(-30164239/125000000 : ℝ)|=(30164239/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(200846127/400000000 : ℝ)|^2107 ≤ (40249495961501/100000000000000 : ℝ)^1595
        have hw : |(200846127/400000000 : ℝ)|=(200846127/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s1_2 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1082807257/2000000000 : ℝ)*x 0 + (627644143/1250000000 : ℝ)*x 1 + (-2413139091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1082807257/2000000000 : ℝ)^2107 ≤ (22230571320443/50000000000000 : ℝ)^1595 := by
    have hnat : (1082807257 : ℕ)^2107*50000000000000^1595 ≤ 22230571320443^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082807257 2000000000 22230571320443 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (627644143/1250000000 : ℝ)^2107 ≤ (40249495633237/100000000000000 : ℝ)^1595 := by
    have hnat : (627644143 : ℕ)^2107*100000000000000^1595 ≤ 40249495633237^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      627644143 1250000000 40249495633237 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2413139091/10000000000 : ℝ)^2107 ≤ (15289361718639/100000000000000 : ℝ)^1595 := by
    have hnat : (2413139091 : ℕ)^2107*100000000000000^1595 ≤ 15289361718639^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2413139091 10000000000 15289361718639 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1082807257/2000000000 : ℝ), (627644143/1250000000 : ℝ), (-2413139091/10000000000 : ℝ)] ![(22230571320443/50000000000000 : ℝ), (40249495633237/100000000000000 : ℝ), (15289361718639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1082807257/2000000000 : ℝ)|^2107 ≤ (22230571320443/50000000000000 : ℝ)^1595
        have hw : |(1082807257/2000000000 : ℝ)|=(1082807257/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(627644143/1250000000 : ℝ)|^2107 ≤ (40249495633237/100000000000000 : ℝ)^1595
        have hw : |(627644143/1250000000 : ℝ)|=(627644143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2413139091/10000000000 : ℝ)|^2107 ≤ (15289361718639/100000000000000 : ℝ)^1595
        have hw : |(-2413139091/10000000000 : ℝ)|=(2413139091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s1_3 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (269341549/625000000 : ℝ)*x 0 + (1847098361/5000000000 : ℝ)*x 1 + (5023555377/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (269341549/625000000 : ℝ)^2107 ≤ (32890621576537/100000000000000 : ℝ)^1595 := by
    have hnat : (269341549 : ℕ)^2107*100000000000000^1595 ≤ 32890621576537^1595*625000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269341549 625000000 32890621576537 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1847098361/5000000000 : ℝ)^2107 ≤ (6708610807763/25000000000000 : ℝ)^1595 := by
    have hnat : (1847098361 : ℕ)^2107*25000000000000^1595 ≤ 6708610807763^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847098361 5000000000 6708610807763 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5023555377/10000000000 : ℝ)^2107 ≤ (8054987035133/20000000000000 : ℝ)^1595 := by
    have hnat : (5023555377 : ℕ)^2107*20000000000000^1595 ≤ 8054987035133^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5023555377 10000000000 8054987035133 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(269341549/625000000 : ℝ), (1847098361/5000000000 : ℝ), (5023555377/10000000000 : ℝ)] ![(32890621576537/100000000000000 : ℝ), (6708610807763/25000000000000 : ℝ), (8054987035133/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(269341549/625000000 : ℝ)|^2107 ≤ (32890621576537/100000000000000 : ℝ)^1595
        have hw : |(269341549/625000000 : ℝ)|=(269341549/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1847098361/5000000000 : ℝ)|^2107 ≤ (6708610807763/25000000000000 : ℝ)^1595
        have hw : |(1847098361/5000000000 : ℝ)|=(1847098361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5023555377/10000000000 : ℝ)|^2107 ≤ (8054987035133/20000000000000 : ℝ)^1595
        have hw : |(5023555377/10000000000 : ℝ)|=(5023555377/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s1_4 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2061331453/10000000000 : ℝ)*x 0 + (5029796683/10000000000 : ℝ)*x 1 + (708568601/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2061331453/10000000000 : ℝ)^2107 ≤ (12416155225783/100000000000000 : ℝ)^1595 := by
    have hnat : (2061331453 : ℕ)^2107*100000000000000^1595 ≤ 12416155225783^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2061331453 10000000000 12416155225783 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5029796683/10000000000 : ℝ)^2107 ≤ (10085262146083/25000000000000 : ℝ)^1595 := by
    have hnat : (5029796683 : ℕ)^2107*25000000000000^1595 ≤ 10085262146083^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5029796683 10000000000 10085262146083 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (708568601/1250000000 : ℝ)^2107 ≤ (1181069904299/2500000000000 : ℝ)^1595 := by
    have hnat : (708568601 : ℕ)^2107*2500000000000^1595 ≤ 1181069904299^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      708568601 1250000000 1181069904299 2500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2061331453/10000000000 : ℝ), (5029796683/10000000000 : ℝ), (708568601/1250000000 : ℝ)] ![(12416155225783/100000000000000 : ℝ), (10085262146083/25000000000000 : ℝ), (1181069904299/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2061331453/10000000000 : ℝ)|^2107 ≤ (12416155225783/100000000000000 : ℝ)^1595
        have hw : |(-2061331453/10000000000 : ℝ)|=(2061331453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5029796683/10000000000 : ℝ)|^2107 ≤ (10085262146083/25000000000000 : ℝ)^1595
        have hw : |(5029796683/10000000000 : ℝ)|=(5029796683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(708568601/1250000000 : ℝ)|^2107 ≤ (1181069904299/2500000000000 : ℝ)^1595
        have hw : |(708568601/1250000000 : ℝ)|=(708568601/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s1_5 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1049006947/2000000000 : ℝ)*x 0 + (-882871461/5000000000 : ℝ)*x 1 + (177142157/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049006947/2000000000 : ℝ)^2107 ≤ (42637007551487/100000000000000 : ℝ)^1595 := by
    have hnat : (1049006947 : ℕ)^2107*100000000000000^1595 ≤ 42637007551487^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049006947 2000000000 42637007551487 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (882871461/5000000000 : ℝ)^2107 ≤ (10120193875619/100000000000000 : ℝ)^1595 := by
    have hnat : (882871461 : ℕ)^2107*100000000000000^1595 ≤ 10120193875619^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      882871461 5000000000 10120193875619 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (177142157/312500000 : ℝ)^2107 ≤ (11810699637503/25000000000000 : ℝ)^1595 := by
    have hnat : (177142157 : ℕ)^2107*25000000000000^1595 ≤ 11810699637503^1595*312500000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      177142157 312500000 11810699637503 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1049006947/2000000000 : ℝ), (-882871461/5000000000 : ℝ), (177142157/312500000 : ℝ)] ![(42637007551487/100000000000000 : ℝ), (10120193875619/100000000000000 : ℝ), (11810699637503/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1049006947/2000000000 : ℝ)|^2107 ≤ (42637007551487/100000000000000 : ℝ)^1595
        have hw : |(1049006947/2000000000 : ℝ)|=(1049006947/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-882871461/5000000000 : ℝ)|^2107 ≤ (10120193875619/100000000000000 : ℝ)^1595
        have hw : |(-882871461/5000000000 : ℝ)|=(882871461/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(177142157/312500000 : ℝ)|^2107 ≤ (11810699637503/25000000000000 : ℝ)^1595
        have hw : |(177142157/312500000 : ℝ)|=(177142157/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s1_6 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (524503507/1000000000 : ℝ)*x 0 + (5668549783/10000000000 : ℝ)*x 1 + (-55179417/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524503507/1000000000 : ℝ)^2107 ≤ (42637011148873/100000000000000 : ℝ)^1595 := by
    have hnat : (524503507 : ℕ)^2107*100000000000000^1595 ≤ 42637011148873^1595*1000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524503507 1000000000 42637011148873 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5668549783/10000000000 : ℝ)^2107 ≤ (23621403453111/50000000000000 : ℝ)^1595 := by
    have hnat : (5668549783 : ℕ)^2107*50000000000000^1595 ≤ 23621403453111^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5668549783 10000000000 23621403453111 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (55179417/312500000 : ℝ)^2107 ≤ (5060090964127/50000000000000 : ℝ)^1595 := by
    have hnat : (55179417 : ℕ)^2107*50000000000000^1595 ≤ 5060090964127^1595*312500000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      55179417 312500000 5060090964127 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524503507/1000000000 : ℝ), (5668549783/10000000000 : ℝ), (-55179417/312500000 : ℝ)] ![(42637011148873/100000000000000 : ℝ), (23621403453111/50000000000000 : ℝ), (5060090964127/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524503507/1000000000 : ℝ)|^2107 ≤ (42637011148873/100000000000000 : ℝ)^1595
        have hw : |(524503507/1000000000 : ℝ)|=(524503507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5668549783/10000000000 : ℝ)|^2107 ≤ (23621403453111/50000000000000 : ℝ)^1595
        have hw : |(5668549783/10000000000 : ℝ)|=(5668549783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-55179417/312500000 : ℝ)|^2107 ≤ (5060090964127/50000000000000 : ℝ)^1595
        have hw : |(-55179417/312500000 : ℝ)|=(55179417/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s1_7 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2155425723/5000000000 : ℝ)*x 0 + (5006045769/10000000000 : ℝ)*x 1 + (3712040407/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2155425723/5000000000 : ℝ)^2107 ≤ (8226150703679/25000000000000 : ℝ)^1595 := by
    have hnat : (2155425723 : ℕ)^2107*25000000000000^1595 ≤ 8226150703679^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2155425723 5000000000 8226150703679 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5006045769/10000000000 : ℝ)^2107 ≤ (4008959878083/10000000000000 : ℝ)^1595 := by
    have hnat : (5006045769 : ℕ)^2107*10000000000000^1595 ≤ 4008959878083^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5006045769 10000000000 4008959878083 10000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3712040407/10000000000 : ℝ)^2107 ≤ (13502899189689/50000000000000 : ℝ)^1595 := by
    have hnat : (3712040407 : ℕ)^2107*50000000000000^1595 ≤ 13502899189689^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3712040407 10000000000 13502899189689 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2155425723/5000000000 : ℝ), (5006045769/10000000000 : ℝ), (3712040407/10000000000 : ℝ)] ![(8226150703679/25000000000000 : ℝ), (4008959878083/10000000000000 : ℝ), (13502899189689/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2155425723/5000000000 : ℝ)|^2107 ≤ (8226150703679/25000000000000 : ℝ)^1595
        have hw : |(2155425723/5000000000 : ℝ)|=(2155425723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5006045769/10000000000 : ℝ)|^2107 ≤ (4008959878083/10000000000000 : ℝ)^1595
        have hw : |(5006045769/10000000000 : ℝ)|=(5006045769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3712040407/10000000000 : ℝ)|^2107 ≤ (13502899189689/50000000000000 : ℝ)^1595
        have hw : |(3712040407/10000000000 : ℝ)|=(3712040407/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1235_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13731/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (79/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (3077/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5007/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (13731/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (79/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (13731/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (79/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (13731/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (79/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (13731/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (79/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (13731/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (79/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (13731/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (79/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (79/10000 : ℝ) ^ (8427/2048 : ℝ) ≤ (223495758897/100000000000000000000 : ℝ) := by
    have hpowers : (79/10000 : ℝ)^8427 ≤ (223495758897/100000000000000000000 : ℝ)^2048 := by
      have hnat : (79 : ℕ)^8427*100000000000000000000^2048 ≤ 223495758897^2048*10000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        79 10000 223495758897 100000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (79/10000 : ℝ)) (X := (223495758897/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (13731/50000 : ℝ) ^ (8427/2048 : ℝ) ≤ (245185827900114537/50000000000000000000 : ℝ) := by
    have hpowers : (13731/50000 : ℝ)^8427 ≤ (245185827900114537/50000000000000000000 : ℝ)^2048 := by
      have hnat : (13731 : ℕ)^8427*50000000000000000000^2048 ≤ 245185827900114537^2048*50000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        13731 50000 245185827900114537 50000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (13731/50000 : ℝ)) (X := (245185827900114537/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000000223495758897/50000000000000000000 : ℝ) ≤ (5000000005431581/5000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (50000000223495758897/50000000000000000000 : ℝ)^2048 ≤ (5000000005431581/5000000000000000 : ℝ)^8427 := by
      have hnat : (50000000223495758897 : ℕ)^2048*5000000000000000^8427 ≤ 5000000005431581^8427*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000000223495758897 50000000000000000000 5000000005431581 5000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000005431581/5000000000000000 : ℝ)) (X := (50000000223495758897/50000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100490371879295987971/100000000000000000000 : ℝ) ≤ (10011895372127243/10000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (100490371879295987971/100000000000000000000 : ℝ)^2048 ≤ (10011895372127243/10000000000000000 : ℝ)^8427 := by
      have hnat : (100490371879295987971 : ℕ)^2048*10000000000000000^8427 ≤ 10011895372127243^8427*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100490371879295987971 100000000000000000000 10011895372127243 10000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10011895372127243/10000000000000000 : ℝ)) (X := (100490371879295987971/100000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25245185827900114537/25000000000000000000 : ℝ) ≤ (2505947683347831/2500000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (25245185827900114537/25000000000000000000 : ℝ)^2048 ≤ (2505947683347831/2500000000000000 : ℝ)^8427 := by
      have hnat : (25245185827900114537 : ℕ)^2048*2500000000000000^8427 ≤ 2505947683347831^8427*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25245185827900114537 25000000000000000000 2505947683347831 2500000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2505947683347831/2500000000000000 : ℝ)) (X := (25245185827900114537/25000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(223495758897/100000000000000000000 : ℝ) ≤ ((66675301404736252221/66680000000000000000 : ℝ)+2*(11895361264081/2667200000000000 : ℝ)*(79/10000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (66675301404736252221/66680000000000000000 : ℝ)+2*(11895361264081/2667200000000000 : ℝ)*(79/10000 : ℝ)=(5000000005431581/5000000000000000 : ℝ) by norm_num, show 1+2*(223495758897/100000000000000000000 : ℝ)=(50000000223495758897/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(245185827900114537/50000000000000000000 : ℝ)+(223495758897/100000000000000000000 : ℝ) ≤ ((66675301404736252221/66680000000000000000 : ℝ)+(11895361264081/2667200000000000 : ℝ)*((13731/50000 : ℝ)+(79/10000 : ℝ)))^(8427/2048 : ℝ) := by
    rw [show (66675301404736252221/66680000000000000000 : ℝ)+(11895361264081/2667200000000000 : ℝ)*((13731/50000 : ℝ)+(79/10000 : ℝ))=(10011895372127243/10000000000000000 : ℝ) by norm_num, show 1+(245185827900114537/50000000000000000000 : ℝ)+(223495758897/100000000000000000000 : ℝ)=(100490371879295987971/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(245185827900114537/50000000000000000000 : ℝ) ≤ ((66675301404736252221/66680000000000000000 : ℝ)+2*(11895361264081/2667200000000000 : ℝ)*(13731/50000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (66675301404736252221/66680000000000000000 : ℝ)+2*(11895361264081/2667200000000000 : ℝ)*(13731/50000 : ℝ)=(2505947683347831/2500000000000000 : ℝ) by norm_num, show 1+2*(245185827900114537/50000000000000000000 : ℝ)=(25245185827900114537/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (66675301404736252221/66680000000000000000 : ℝ)*(X 1 0+X 2 0)+(11895361264081/2667200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (79/10000 : ℝ)) (hi := (13731/50000 : ℝ)) (c := (66675301404736252221/66680000000000000000 : ℝ)) (alpha := (11895361264081/2667200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (66675301404736252221/66680000000000000000 : ℝ)*(X 0 1+X 2 1)+(11895361264081/2667200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (79/10000 : ℝ)) (hi := (13731/50000 : ℝ)) (c := (66675301404736252221/66680000000000000000 : ℝ)) (alpha := (11895361264081/2667200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (66675301404736252221/66680000000000000000 : ℝ)*(X 0 2+X 1 2)+(11895361264081/2667200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (79/10000 : ℝ)) (hi := (13731/50000 : ℝ)) (c := (66675301404736252221/66680000000000000000 : ℝ)) (alpha := (11895361264081/2667200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-257580767/1250000000 : ℝ)*X 0 0+(2838678863/5000000000 : ℝ)*X 0 1+(1255288279/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5414036233/10000000000 : ℝ)*X 1 0+(-30164239/125000000 : ℝ)*X 1 1+(200846127/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1082807257/2000000000 : ℝ)*X 2 0+(627644143/1250000000 : ℝ)*X 2 1+(-2413139091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((269341549/625000000 : ℝ)*X 0 0+(1847098361/5000000000 : ℝ)*X 0 1+(5023555377/10000000000 : ℝ)*X 0 2+(269341549/625000000 : ℝ)*X 1 0+(1847098361/5000000000 : ℝ)*X 1 1+(5023555377/10000000000 : ℝ)*X 1 2+(269341549/625000000 : ℝ)*X 2 0+(1847098361/5000000000 : ℝ)*X 2 1+(5023555377/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2061331453/10000000000 : ℝ)*X 0 0+(5029796683/10000000000 : ℝ)*X 0 1+(708568601/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1049006947/2000000000 : ℝ)*X 1 0+(-882871461/5000000000 : ℝ)*X 1 1+(177142157/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((524503507/1000000000 : ℝ)*X 2 0+(5668549783/10000000000 : ℝ)*X 2 1+(-55179417/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2155425723/5000000000 : ℝ)*X 0 0+(5006045769/10000000000 : ℝ)*X 0 1+(3712040407/10000000000 : ℝ)*X 0 2+(2155425723/5000000000 : ℝ)*X 1 0+(5006045769/10000000000 : ℝ)*X 1 1+(3712040407/10000000000 : ℝ)*X 1 2+(2155425723/5000000000 : ℝ)*X 2 0+(5006045769/10000000000 : ℝ)*X 2 1+(3712040407/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (286021309367657223339278001/33340000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (93015483/100000000000000 : ℝ)*(base1) + (92424023/5000000000000 : ℝ)*(base19) + (186311733/10000000000000 : ℝ)*(base23) + (201474979/100000000000000 : ℝ)*(upper3) + (53992627/25000000000000 : ℝ)*(upper5) + (11380942828727/1000000000000 : ℝ)*(major0) + (11380942828727/1000000000000 : ℝ)*(major1) + (11380942828727/1000000000000 : ℝ)*(major2) + (761962493036109/50000000000000 : ℝ)*(sp0) + (11905730983097/781250000000 : ℝ)*(sp1) + (761966775599773/50000000000000 : ℝ)*(sp2) + (94030945275821/12500000000000 : ℝ)*(sp3) + (5260630071/50000000000000 : ℝ)*(sp4) + (5210242351/100000000000000 : ℝ)*(sp7) + (376126432732201/50000000000000 : ℝ)*(f.failure) + (1523935414316877/100000000000000 : ℝ)*(f.sum) + (12473912012077/6668000000000000000000000000 : ℝ)*base66 + (226573034928392333/66680000000000000000000000000000 : ℝ)*base68 + (156634833285032333/66680000000000000000000000000000 : ℝ)*base70 + (73499327441952333/66680000000000000000000000000000 : ℝ)*base72 + (259080304441/266720000000000000000000000 : ℝ)*base74 + (435131577931287667/66680000000000000000000000000000 : ℝ)*base75 + (83145635117712333/66680000000000000000000000000000 : ℝ)*base78 + (246767789640007667/66680000000000000000000000000000 : ℝ)*base79 + (684524092641/6668000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4111463/1250000000000000000000 : ℝ)*base89 + (4111463/1250000000000000000000 : ℝ)*base91 + (4111463/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (90806131618628986219717467/104187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (836496649/100000000000000 : ℝ)*(base19) + (679223409/50000000000000 : ℝ)*(base23) + (61487009/50000000000000 : ℝ)*(upper2) + (174334137/100000000000000 : ℝ)*(upper3) + (6433717/20000000000000 : ℝ)*(upper5) + (73073311147491/6250000000000 : ℝ)*(major0) + (73073311147491/6250000000000 : ℝ)*(major1) + (73073311147491/6250000000000 : ℝ)*(major2) + (856532301/25000000000000 : ℝ)*(sp1) + (4622654619/50000000000000 : ℝ)*(sp2) + (195693849279011/12500000000000 : ℝ)*(sp4) + (313109306321247/20000000000000 : ℝ)*(sp5) + (6115391369047/390625000000 : ℝ)*(sp6) + (772795133435467/100000000000000 : ℝ)*(sp7) + (772795133435467/100000000000000 : ℝ)*(f.failure) + (195693849279011/12500000000000 : ℝ)*(f.sum) + (17119184198259/8335000000000000000000000000 : ℝ)*base66 + (327548814775647489/416750000000000000000000000000000 : ℝ)*base68 + (3294753439978852511/416750000000000000000000000000000 : ℝ)*base69 + (1058476954948352511/416750000000000000000000000000000 : ℝ)*base71 + (952034243227/1041875000000000000000000000 : ℝ)*base73 + (1845031788625852511/416750000000000000000000000000000 : ℝ)*base75 + (600417939380602511/416750000000000000000000000000000 : ℝ)*base77 + (1447105535122352511/416750000000000000000000000000000 : ℝ)*base79 + (20621851418383/4167500000000000000000000000 : ℝ)*base81 + (12317979/2500000000000000000000 : ℝ)*base90 + (12317979/2500000000000000000000 : ℝ)*base92 + (12317979/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1235_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (13731/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (79/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3077/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5007/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1235_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1235_s2_0 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-527259859/2500000000 : ℝ)*x 0 + (1098796411/2000000000 : ℝ)*x 1 + (1034734489/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527259859/2500000000 : ℝ)^2107 ≤ (6398582513957/50000000000000 : ℝ)^1595 := by
    have hnat : (527259859 : ℕ)^2107*50000000000000^1595 ≤ 6398582513957^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527259859 2500000000 6398582513957 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1098796411/2000000000 : ℝ)^2107 ≤ (45330470219617/100000000000000 : ℝ)^1595 := by
    have hnat : (1098796411 : ℕ)^2107*100000000000000^1595 ≤ 45330470219617^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098796411 2000000000 45330470219617 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034734489/2000000000 : ℝ)^2107 ≤ (41872364740417/100000000000000 : ℝ)^1595 := by
    have hnat : (1034734489 : ℕ)^2107*100000000000000^1595 ≤ 41872364740417^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034734489 2000000000 41872364740417 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-527259859/2500000000 : ℝ), (1098796411/2000000000 : ℝ), (1034734489/2000000000 : ℝ)] ![(6398582513957/50000000000000 : ℝ), (45330470219617/100000000000000 : ℝ), (41872364740417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-527259859/2500000000 : ℝ)|^2107 ≤ (6398582513957/50000000000000 : ℝ)^1595
        have hw : |(-527259859/2500000000 : ℝ)|=(527259859/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1098796411/2000000000 : ℝ)|^2107 ≤ (45330470219617/100000000000000 : ℝ)^1595
        have hw : |(1098796411/2000000000 : ℝ)|=(1098796411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034734489/2000000000 : ℝ)|^2107 ≤ (41872364740417/100000000000000 : ℝ)^1595
        have hw : |(1034734489/2000000000 : ℝ)|=(1034734489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s2_1 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1342492263/2500000000 : ℝ)*x 0 + (-227499797/1000000000 : ℝ)*x 1 + (517367241/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1342492263/2500000000 : ℝ)^2107 ≤ (43983711978809/100000000000000 : ℝ)^1595 := by
    have hnat : (1342492263 : ℕ)^2107*100000000000000^1595 ≤ 43983711978809^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1342492263 2500000000 43983711978809 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (227499797/1000000000 : ℝ)^2107 ≤ (14143923641489/100000000000000 : ℝ)^1595 := by
    have hnat : (227499797 : ℕ)^2107*100000000000000^1595 ≤ 14143923641489^1595*1000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      227499797 1000000000 14143923641489 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (517367241/1000000000 : ℝ)^2107 ≤ (2093618218311/5000000000000 : ℝ)^1595 := by
    have hnat : (517367241 : ℕ)^2107*5000000000000^1595 ≤ 2093618218311^1595*1000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517367241 1000000000 2093618218311 5000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1342492263/2500000000 : ℝ), (-227499797/1000000000 : ℝ), (517367241/1000000000 : ℝ)] ![(43983711978809/100000000000000 : ℝ), (14143923641489/100000000000000 : ℝ), (2093618218311/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1342492263/2500000000 : ℝ)|^2107 ≤ (43983711978809/100000000000000 : ℝ)^1595
        have hw : |(1342492263/2500000000 : ℝ)|=(1342492263/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-227499797/1000000000 : ℝ)|^2107 ≤ (14143923641489/100000000000000 : ℝ)^1595
        have hw : |(-227499797/1000000000 : ℝ)|=(227499797/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(517367241/1000000000 : ℝ)|^2107 ≤ (2093618218311/5000000000000 : ℝ)^1595
        have hw : |(517367241/1000000000 : ℝ)|=(517367241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s2_2 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5369968879/10000000000 : ℝ)*x 0 + (2586836279/5000000000 : ℝ)*x 1 + (-454999601/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5369968879/10000000000 : ℝ)^2107 ≤ (43983710106963/100000000000000 : ℝ)^1595 := by
    have hnat : (5369968879 : ℕ)^2107*100000000000000^1595 ≤ 43983710106963^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5369968879 10000000000 43983710106963 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2586836279/5000000000 : ℝ)^2107 ≤ (41872365948539/100000000000000 : ℝ)^1595 := by
    have hnat : (2586836279 : ℕ)^2107*100000000000000^1595 ≤ 41872365948539^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586836279 5000000000 41872365948539 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (454999601/2000000000 : ℝ)^2107 ≤ (7071961964469/50000000000000 : ℝ)^1595 := by
    have hnat : (454999601 : ℕ)^2107*50000000000000^1595 ≤ 7071961964469^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      454999601 2000000000 7071961964469 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5369968879/10000000000 : ℝ), (2586836279/5000000000 : ℝ), (-454999601/2000000000 : ℝ)] ![(43983710106963/100000000000000 : ℝ), (41872365948539/100000000000000 : ℝ), (7071961964469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5369968879/10000000000 : ℝ)|^2107 ≤ (43983710106963/100000000000000 : ℝ)^1595
        have hw : |(5369968879/10000000000 : ℝ)|=(5369968879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2586836279/5000000000 : ℝ)|^2107 ≤ (41872365948539/100000000000000 : ℝ)^1595
        have hw : |(2586836279/5000000000 : ℝ)|=(2586836279/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-454999601/2000000000 : ℝ)|^2107 ≤ (7071961964469/50000000000000 : ℝ)^1595
        have hw : |(-454999601/2000000000 : ℝ)|=(454999601/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s2_3 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1085719047/2500000000 : ℝ)*x 0 + (2015093533/5000000000 : ℝ)*x 1 + (584884963/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1085719047/2500000000 : ℝ)^2107 ≤ (8306974593071/25000000000000 : ℝ)^1595 := by
    have hnat : (1085719047 : ℕ)^2107*25000000000000^1595 ≤ 8306974593071^1595*2500000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085719047 2500000000 8306974593071 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2015093533/5000000000 : ℝ)^2107 ≤ (30104634475899/100000000000000 : ℝ)^1595 := by
    have hnat : (2015093533 : ℕ)^2107*100000000000000^1595 ≤ 30104634475899^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2015093533 5000000000 30104634475899 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (584884963/1250000000 : ℝ)^2107 ≤ (18333733564521/50000000000000 : ℝ)^1595 := by
    have hnat : (584884963 : ℕ)^2107*50000000000000^1595 ≤ 18333733564521^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      584884963 1250000000 18333733564521 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1085719047/2500000000 : ℝ), (2015093533/5000000000 : ℝ), (584884963/1250000000 : ℝ)] ![(8306974593071/25000000000000 : ℝ), (30104634475899/100000000000000 : ℝ), (18333733564521/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1085719047/2500000000 : ℝ)|^2107 ≤ (8306974593071/25000000000000 : ℝ)^1595
        have hw : |(1085719047/2500000000 : ℝ)|=(1085719047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2015093533/5000000000 : ℝ)|^2107 ≤ (30104634475899/100000000000000 : ℝ)^1595
        have hw : |(2015093533/5000000000 : ℝ)|=(2015093533/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(584884963/1250000000 : ℝ)|^2107 ≤ (18333733564521/50000000000000 : ℝ)^1595
        have hw : |(584884963/1250000000 : ℝ)|=(584884963/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s2_4 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2109119319/10000000000 : ℝ)*x 0 + (207029661/400000000 : ℝ)*x 1 + (2745946743/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2109119319/10000000000 : ℝ)^2107 ≤ (1599725667173/12500000000000 : ℝ)^1595 := by
    have hnat : (2109119319 : ℕ)^2107*12500000000000^1595 ≤ 1599725667173^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109119319 10000000000 1599725667173 12500000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (207029661/400000000 : ℝ)^2107 ≤ (8378897482311/20000000000000 : ℝ)^1595 := by
    have hnat : (207029661 : ℕ)^2107*20000000000000^1595 ≤ 8378897482311^1595*400000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207029661 400000000 8378897482311 20000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2745946743/5000000000 : ℝ)^2107 ≤ (45307707237273/100000000000000 : ℝ)^1595 := by
    have hnat : (2745946743 : ℕ)^2107*100000000000000^1595 ≤ 45307707237273^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745946743 5000000000 45307707237273 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2109119319/10000000000 : ℝ), (207029661/400000000 : ℝ), (2745946743/5000000000 : ℝ)] ![(1599725667173/12500000000000 : ℝ), (8378897482311/20000000000000 : ℝ), (45307707237273/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2109119319/10000000000 : ℝ)|^2107 ≤ (1599725667173/12500000000000 : ℝ)^1595
        have hw : |(-2109119319/10000000000 : ℝ)|=(2109119319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(207029661/400000000 : ℝ)|^2107 ≤ (8378897482311/20000000000000 : ℝ)^1595
        have hw : |(207029661/400000000 : ℝ)|=(207029661/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2745946743/5000000000 : ℝ)|^2107 ≤ (45307707237273/100000000000000 : ℝ)^1595
        have hw : |(2745946743/5000000000 : ℝ)|=(2745946743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s2_5 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288206303/10000000000 : ℝ)*x 0 + (-391355339/2000000000 : ℝ)*x 1 + (686486691/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288206303/10000000000 : ℝ)^2107 ≤ (21550607611567/50000000000000 : ℝ)^1595 := by
    have hnat : (5288206303 : ℕ)^2107*50000000000000^1595 ≤ 21550607611567^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288206303 10000000000 21550607611567 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (391355339/2000000000 : ℝ)^2107 ≤ (5795538531813/50000000000000 : ℝ)^1595 := by
    have hnat : (391355339 : ℕ)^2107*50000000000000^1595 ≤ 5795538531813^1595*2000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      391355339 2000000000 5795538531813 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (686486691/1250000000 : ℝ)^2107 ≤ (11326926923749/25000000000000 : ℝ)^1595 := by
    have hnat : (686486691 : ℕ)^2107*25000000000000^1595 ≤ 11326926923749^1595*1250000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      686486691 1250000000 11326926923749 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288206303/10000000000 : ℝ), (-391355339/2000000000 : ℝ), (686486691/1250000000 : ℝ)] ![(21550607611567/50000000000000 : ℝ), (5795538531813/50000000000000 : ℝ), (11326926923749/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288206303/10000000000 : ℝ)|^2107 ≤ (21550607611567/50000000000000 : ℝ)^1595
        have hw : |(5288206303/10000000000 : ℝ)|=(5288206303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-391355339/2000000000 : ℝ)|^2107 ≤ (5795538531813/50000000000000 : ℝ)^1595
        have hw : |(-391355339/2000000000 : ℝ)|=(391355339/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(686486691/1250000000 : ℝ)|^2107 ≤ (11326926923749/25000000000000 : ℝ)^1595
        have hw : |(686486691/1250000000 : ℝ)|=(686486691/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s2_6 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5288206477/10000000000 : ℝ)*x 0 + (2745946799/5000000000 : ℝ)*x 1 + (-978388179/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5288206477/10000000000 : ℝ)^2107 ≤ (862024341931/2000000000000 : ℝ)^1595 := by
    have hnat : (5288206477 : ℕ)^2107*2000000000000^1595 ≤ 862024341931^1595*10000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5288206477 10000000000 862024341931 2000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2745946799/5000000000 : ℝ)^2107 ≤ (45307708457869/100000000000000 : ℝ)^1595 := by
    have hnat : (2745946799 : ℕ)^2107*100000000000000^1595 ≤ 45307708457869^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2745946799 5000000000 45307708457869 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (978388179/5000000000 : ℝ)^2107 ≤ (2897768606647/25000000000000 : ℝ)^1595 := by
    have hnat : (978388179 : ℕ)^2107*25000000000000^1595 ≤ 2897768606647^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      978388179 5000000000 2897768606647 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5288206477/10000000000 : ℝ), (2745946799/5000000000 : ℝ), (-978388179/5000000000 : ℝ)] ![(862024341931/2000000000000 : ℝ), (45307708457869/100000000000000 : ℝ), (2897768606647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5288206477/10000000000 : ℝ)|^2107 ≤ (862024341931/2000000000000 : ℝ)^1595
        have hw : |(5288206477/10000000000 : ℝ)|=(5288206477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2745946799/5000000000 : ℝ)|^2107 ≤ (45307708457869/100000000000000 : ℝ)^1595
        have hw : |(2745946799/5000000000 : ℝ)|=(2745946799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-978388179/5000000000 : ℝ)|^2107 ≤ (2897768606647/25000000000000 : ℝ)^1595
        have hw : |(-978388179/5000000000 : ℝ)|=(978388179/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1235_s2_7 (p : ℝ) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ)) (x : Fin 3 → ℝ) :
    (135719921/312500000 : ℝ)*x 0 + (2337444149/5000000000 : ℝ)*x 1 + (50430221/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (135719921/312500000 : ℝ)^2107 ≤ (8307382126423/25000000000000 : ℝ)^1595 := by
    have hnat : (135719921 : ℕ)^2107*25000000000000^1595 ≤ 8307382126423^1595*312500000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135719921 312500000 8307382126423 25000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2337444149/5000000000 : ℝ)^2107 ≤ (18312041964167/50000000000000 : ℝ)^1595 := by
    have hnat : (2337444149 : ℕ)^2107*50000000000000^1595 ≤ 18312041964167^1595*5000000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2337444149 5000000000 18312041964167 50000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (50430221/125000000 : ℝ)^2107 ≤ (30146387559199/100000000000000 : ℝ)^1595 := by
    have hnat : (50430221 : ℕ)^2107*100000000000000^1595 ≤ 30146387559199^1595*125000000^2107 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      50430221 125000000 30146387559199 100000000000000 2107 1595 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2107/512 : ℝ)) 2107 1595 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(135719921/312500000 : ℝ), (2337444149/5000000000 : ℝ), (50430221/125000000 : ℝ)] ![(8307382126423/25000000000000 : ℝ), (18312041964167/50000000000000 : ℝ), (30146387559199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(135719921/312500000 : ℝ)|^2107 ≤ (8307382126423/25000000000000 : ℝ)^1595
        have hw : |(135719921/312500000 : ℝ)|=(135719921/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2337444149/5000000000 : ℝ)|^2107 ≤ (18312041964167/50000000000000 : ℝ)^1595
        have hw : |(2337444149/5000000000 : ℝ)|=(2337444149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(50430221/125000000 : ℝ)|^2107 ≤ (30146387559199/100000000000000 : ℝ)^1595
        have hw : |(50430221/125000000 : ℝ)|=(50430221/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1235_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5007/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3077/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9471/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16241/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5007/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3077/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5007/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3077/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5007/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3077/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5007/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3077/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5007/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3077/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5007/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3077/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3077/50000 : ℝ) ^ (8427/2048 : ℝ) ≤ (1041574933642957/100000000000000000000 : ℝ) := by
    have hpowers : (3077/50000 : ℝ)^8427 ≤ (1041574933642957/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3077 : ℕ)^8427*100000000000000000000^2048 ≤ 1041574933642957^2048*50000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3077 50000 1041574933642957 100000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3077/50000 : ℝ)) (X := (1041574933642957/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (5007/25000 : ℝ) ^ (8427/2048 : ℝ) ≤ (133787633410033871/100000000000000000000 : ℝ) := by
    have hpowers : (5007/25000 : ℝ)^8427 ≤ (133787633410033871/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5007 : ℕ)^8427*100000000000000000000^2048 ≤ 133787633410033871^2048*25000^8427 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5007 25000 133787633410033871 100000000000000000000 8427 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5007/25000 : ℝ)) (X := (133787633410033871/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001041574933642957/50000000000000000000 : ℝ) ≤ (10000050626050687/10000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (50001041574933642957/50000000000000000000 : ℝ)^2048 ≤ (10000050626050687/10000000000000000 : ℝ)^8427 := by
      have hnat : (50001041574933642957 : ℕ)^2048*10000000000000000^8427 ≤ 10000050626050687^8427*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001041574933642957 50000000000000000000 10000050626050687 10000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000050626050687/10000000000000000 : ℝ)) (X := (50001041574933642957/50000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25033707302085919207/25000000000000000000 : ℝ) ≤ (10003275061326667/10000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (25033707302085919207/25000000000000000000 : ℝ)^2048 ≤ (10003275061326667/10000000000000000 : ℝ)^8427 := by
      have hnat : (25033707302085919207 : ℕ)^2048*10000000000000000^8427 ≤ 10003275061326667^8427*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25033707302085919207 25000000000000000000 10003275061326667 10000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003275061326667/10000000000000000 : ℝ)) (X := (25033707302085919207/25000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50133787633410033871/50000000000000000000 : ℝ) ≤ (10006499496602647/10000000000000000 : ℝ) ^ (8427/2048 : ℝ) := by
    have hpowers : (50133787633410033871/50000000000000000000 : ℝ)^2048 ≤ (10006499496602647/10000000000000000 : ℝ)^8427 := by
      have hnat : (50133787633410033871 : ℕ)^2048*10000000000000000^8427 ≤ 10006499496602647^8427*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50133787633410033871 50000000000000000000 10006499496602647 10000000000000000 2048 8427 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006499496602647/10000000000000000 : ℝ)) (X := (50133787633410033871/50000000000000000000 : ℝ)) (by norm_num) 8427 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1041574933642957/100000000000000000000 : ℝ) ≤ ((69350508018225234799/69370000000000000000 : ℝ)+2*(161221763799/69370000000000 : ℝ)*(3077/50000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (69350508018225234799/69370000000000000000 : ℝ)+2*(161221763799/69370000000000 : ℝ)*(3077/50000 : ℝ)=(10000050626050687/10000000000000000 : ℝ) by norm_num, show 1+2*(1041574933642957/100000000000000000000 : ℝ)=(50001041574933642957/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(133787633410033871/100000000000000000000 : ℝ)+(1041574933642957/100000000000000000000 : ℝ) ≤ ((69350508018225234799/69370000000000000000 : ℝ)+(161221763799/69370000000000 : ℝ)*((5007/25000 : ℝ)+(3077/50000 : ℝ)))^(8427/2048 : ℝ) := by
    rw [show (69350508018225234799/69370000000000000000 : ℝ)+(161221763799/69370000000000 : ℝ)*((5007/25000 : ℝ)+(3077/50000 : ℝ))=(10003275061326667/10000000000000000 : ℝ) by norm_num, show 1+(133787633410033871/100000000000000000000 : ℝ)+(1041574933642957/100000000000000000000 : ℝ)=(25033707302085919207/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(133787633410033871/100000000000000000000 : ℝ) ≤ ((69350508018225234799/69370000000000000000 : ℝ)+2*(161221763799/69370000000000 : ℝ)*(5007/25000 : ℝ))^(8427/2048 : ℝ) := by
    rw [show (69350508018225234799/69370000000000000000 : ℝ)+2*(161221763799/69370000000000 : ℝ)*(5007/25000 : ℝ)=(10006499496602647/10000000000000000 : ℝ) by norm_num, show 1+2*(133787633410033871/100000000000000000000 : ℝ)=(50133787633410033871/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (69350508018225234799/69370000000000000000 : ℝ)*(X 1 0+X 2 0)+(161221763799/69370000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (3077/50000 : ℝ)) (hi := (5007/25000 : ℝ)) (c := (69350508018225234799/69370000000000000000 : ℝ)) (alpha := (161221763799/69370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (69350508018225234799/69370000000000000000 : ℝ)*(X 0 1+X 2 1)+(161221763799/69370000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (3077/50000 : ℝ)) (hi := (5007/25000 : ℝ)) (c := (69350508018225234799/69370000000000000000 : ℝ)) (alpha := (161221763799/69370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (69350508018225234799/69370000000000000000 : ℝ)*(X 0 2+X 1 2)+(161221763799/69370000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8427/2048 : ℝ)) (lo := (3077/50000 : ℝ)) (hi := (5007/25000 : ℝ)) (c := (69350508018225234799/69370000000000000000 : ℝ)) (alpha := (161221763799/69370000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-527259859/2500000000 : ℝ)*X 0 0+(1098796411/2000000000 : ℝ)*X 0 1+(1034734489/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1342492263/2500000000 : ℝ)*X 1 0+(-227499797/1000000000 : ℝ)*X 1 1+(517367241/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5369968879/10000000000 : ℝ)*X 2 0+(2586836279/5000000000 : ℝ)*X 2 1+(-454999601/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1085719047/2500000000 : ℝ)*X 0 0+(2015093533/5000000000 : ℝ)*X 0 1+(584884963/1250000000 : ℝ)*X 0 2+(1085719047/2500000000 : ℝ)*X 1 0+(2015093533/5000000000 : ℝ)*X 1 1+(584884963/1250000000 : ℝ)*X 1 2+(1085719047/2500000000 : ℝ)*X 2 0+(2015093533/5000000000 : ℝ)*X 2 1+(584884963/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2109119319/10000000000 : ℝ)*X 0 0+(207029661/400000000 : ℝ)*X 0 1+(2745946743/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5288206303/10000000000 : ℝ)*X 1 0+(-391355339/2000000000 : ℝ)*X 1 1+(686486691/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5288206477/10000000000 : ℝ)*X 2 0+(2745946799/5000000000 : ℝ)*X 2 1+(-978388179/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((135719921/312500000 : ℝ)*X 0 0+(2337444149/5000000000 : ℝ)*X 0 1+(50430221/125000000 : ℝ)*X 0 2+(135719921/312500000 : ℝ)*X 1 0+(2337444149/5000000000 : ℝ)*X 1 1+(50430221/125000000 : ℝ)*X 1 2+(135719921/312500000 : ℝ)*X 2 0+(2337444149/5000000000 : ℝ)*X 2 1+(50430221/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1235_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (290423349101409701452728711/61937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (445927567/50000000000000 : ℝ)*(base19) + (181121153/25000000000000 : ℝ)*(base23) + (17933451/50000000000000 : ℝ)*(lower2) + (78794757/50000000000000 : ℝ)*(upper3) + (27921051/50000000000000 : ℝ)*(upper5) + (582886809026859/25000000000000 : ℝ)*(major0) + (582886809026859/25000000000000 : ℝ)*(major1) + (582886809026859/25000000000000 : ℝ)*(major2) + (624397921707363/20000000000000 : ℝ)*(sp0) + (195124809218829/6250000000000 : ℝ)*(sp1) + (1560998557435893/50000000000000 : ℝ)*(sp2) + (1541091291423421/100000000000000 : ℝ)*(sp3) + (8230819583/100000000000000 : ℝ)*(sp4) + (5185135899/100000000000000 : ℝ)*(sp7) + (38527411913983/2500000000000 : ℝ)*(f.failure) + (1560998919678199/50000000000000 : ℝ)*(f.sum) + (3611429422749/1387400000000000000000000000 : ℝ)*base65 + (1702015783675533659/1734250000000000000000000000000000 : ℝ)*base68 + (8767098016856216341/1734250000000000000000000000000000 : ℝ)*base69 + (13449317237526466341/1734250000000000000000000000000000 : ℝ)*base71 + (529914978129/867125000000000000000000000 : ℝ)*base73 + (10250875098431466341/1734250000000000000000000000000000 : ℝ)*base75 + (9140978639140966341/1734250000000000000000000000000000 : ℝ)*base77 + (5263582539910466341/1734250000000000000000000000000000 : ℝ)*base79 + (442796345149/693700000000000000000000000 : ℝ)*base81 + (706671/62500000000000000000 : ℝ)*base90 + (706671/62500000000000000000 : ℝ)*base92 + (706671/62500000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (67657730252418158519466849/30968750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (406131867/50000000000000 : ℝ)*(base19) + (285160341/25000000000000 : ℝ)*(base23) + (4178659/6250000000000 : ℝ)*(upper2) + (67289989/50000000000000 : ℝ)*(upper3) + (8097307/20000000000000 : ℝ)*(upper5) + (295274177727719/12500000000000 : ℝ)*(major0) + (295274177727719/12500000000000 : ℝ)*(major1) + (295274177727719/12500000000000 : ℝ)*(major2) + (7695337921/100000000000000 : ℝ)*(sp1) + (3506402307/25000000000000 : ℝ)*(sp2) + (3163033904815387/100000000000000 : ℝ)*(sp4) + (790756349303433/25000000000000 : ℝ)*(sp5) + (1581509369282397/50000000000000 : ℝ)*(sp6) + (780676433002227/50000000000000 : ℝ)*(sp7) + (780676433002227/50000000000000 : ℝ)*(f.failure) + (3163033904815387/100000000000000 : ℝ)*(f.sum) + (43344906586699/6937000000000000000000000000 : ℝ)*base66 + (2919788948900681519/867125000000000000000000000000000 : ℝ)*base68 + (892876747762556519/867125000000000000000000000000000 : ℝ)*base70 + (474279241892306519/867125000000000000000000000000000 : ℝ)*base72 + (13969415460919/3468500000000000000000000000 : ℝ)*base74 + (4023299472198556519/867125000000000000000000000000000 : ℝ)*base76 + (506893948004056519/867125000000000000000000000000000 : ℝ)*base78 + (2233440530004693481/867125000000000000000000000000000 : ℝ)*base79 + (567800783891/173425000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (10515901/1250000000000000000000 : ℝ)*base89 + (10515901/1250000000000000000000 : ℝ)*base91 + (10515901/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1235_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5007/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3077/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9471/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1235_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1235_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9471/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1235_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1235_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1235_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8427/2048 : ℝ) ≤ p) (hpb : p ≤ (2107/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37822863/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9471/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16241/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1235_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
