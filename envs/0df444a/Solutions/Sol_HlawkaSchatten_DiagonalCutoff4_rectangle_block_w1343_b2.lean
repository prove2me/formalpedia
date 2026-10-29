-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1343_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:04:50.952969+00:00
-- url     : https://prove2.me/submissions/b7233e62-cbec-494e-bba3-20038ab7b53e

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
theorem support_rectangle_w1343_s6_0 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2553877/12500000 : ℝ)*x 0 + (2706334493/5000000000 : ℝ)*x 1 + (2622314613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2553877/12500000 : ℝ)^4303 ≤ (12442286217343/100000000000000 : ℝ)^3279 := by
    have hnat : (2553877 : ℕ)^4303*100000000000000^3279 ≤ 12442286217343^3279*12500000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2553877 12500000 12442286217343 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706334493/5000000000 : ℝ)^4303 ≤ (2234232946067/5000000000000 : ℝ)^3279 := by
    have hnat : (2706334493 : ℕ)^4303*5000000000000^3279 ≤ 2234232946067^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706334493 5000000000 2234232946067 5000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622314613/5000000000 : ℝ)^4303 ≤ (10718263713219/25000000000000 : ℝ)^3279 := by
    have hnat : (2622314613 : ℕ)^4303*25000000000000^3279 ≤ 10718263713219^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622314613 5000000000 10718263713219 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2553877/12500000 : ℝ), (2706334493/5000000000 : ℝ), (2622314613/5000000000 : ℝ)] ![(12442286217343/100000000000000 : ℝ), (2234232946067/5000000000000 : ℝ), (10718263713219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2553877/12500000 : ℝ)|^4303 ≤ (12442286217343/100000000000000 : ℝ)^3279
        have hw : |(-2553877/12500000 : ℝ)|=(2553877/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706334493/5000000000 : ℝ)|^4303 ≤ (2234232946067/5000000000000 : ℝ)^3279
        have hw : |(2706334493/5000000000 : ℝ)|=(2706334493/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622314613/5000000000 : ℝ)|^4303 ≤ (10718263713219/25000000000000 : ℝ)^3279
        have hw : |(2622314613/5000000000 : ℝ)|=(2622314613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s6_1 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348985161/10000000000 : ℝ)*x 0 + (-1064359231/5000000000 : ℝ)*x 1 + (2622314613/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348985161/10000000000 : ℝ)^4303 ≤ (8799199650193/20000000000000 : ℝ)^3279 := by
    have hnat : (5348985161 : ℕ)^4303*20000000000000^3279 ≤ 8799199650193^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348985161 10000000000 8799199650193 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064359231/5000000000 : ℝ)^4303 ≤ (6565473439637/50000000000000 : ℝ)^3279 := by
    have hnat : (1064359231 : ℕ)^4303*50000000000000^3279 ≤ 6565473439637^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064359231 5000000000 6565473439637 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622314613/5000000000 : ℝ)^4303 ≤ (10718263713219/25000000000000 : ℝ)^3279 := by
    have hnat : (2622314613 : ℕ)^4303*25000000000000^3279 ≤ 10718263713219^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622314613 5000000000 10718263713219 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348985161/10000000000 : ℝ), (-1064359231/5000000000 : ℝ), (2622314613/5000000000 : ℝ)] ![(8799199650193/20000000000000 : ℝ), (6565473439637/50000000000000 : ℝ), (10718263713219/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348985161/10000000000 : ℝ)|^4303 ≤ (8799199650193/20000000000000 : ℝ)^3279
        have hw : |(5348985161/10000000000 : ℝ)|=(5348985161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1064359231/5000000000 : ℝ)|^4303 ≤ (6565473439637/50000000000000 : ℝ)^3279
        have hw : |(-1064359231/5000000000 : ℝ)|=(1064359231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622314613/5000000000 : ℝ)|^4303 ≤ (10718263713219/25000000000000 : ℝ)^3279
        have hw : |(2622314613/5000000000 : ℝ)|=(2622314613/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s6_2 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348985163/10000000000 : ℝ)*x 0 + (209785169/400000000 : ℝ)*x 1 + (-2128718461/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348985163/10000000000 : ℝ)^4303 ≤ (43995998272553/100000000000000 : ℝ)^3279 := by
    have hnat : (5348985163 : ℕ)^4303*100000000000000^3279 ≤ 43995998272553^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348985163 10000000000 43995998272553 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209785169/400000000 : ℝ)^4303 ≤ (10718263710537/25000000000000 : ℝ)^3279 := by
    have hnat : (209785169 : ℕ)^4303*25000000000000^3279 ≤ 10718263710537^3279*400000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209785169 400000000 10718263710537 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2128718461/10000000000 : ℝ)^4303 ≤ (13130946871179/100000000000000 : ℝ)^3279 := by
    have hnat : (2128718461 : ℕ)^4303*100000000000000^3279 ≤ 13130946871179^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128718461 10000000000 13130946871179 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348985163/10000000000 : ℝ), (209785169/400000000 : ℝ), (-2128718461/10000000000 : ℝ)] ![(43995998272553/100000000000000 : ℝ), (10718263710537/25000000000000 : ℝ), (13130946871179/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348985163/10000000000 : ℝ)|^4303 ≤ (43995998272553/100000000000000 : ℝ)^3279
        have hw : |(5348985163/10000000000 : ℝ)|=(5348985163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209785169/400000000 : ℝ)|^4303 ≤ (10718263710537/25000000000000 : ℝ)^3279
        have hw : |(209785169/400000000 : ℝ)|=(209785169/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2128718461/10000000000 : ℝ)|^4303 ≤ (13130946871179/100000000000000 : ℝ)^3279
        have hw : |(-2128718461/10000000000 : ℝ)|=(2128718461/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s6_3 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2163178229/5000000000 : ℝ)*x 0 + (259603173/625000000 : ℝ)*x 1 + (56321933/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163178229/5000000000 : ℝ)^4303 ≤ (33303264825059/100000000000000 : ℝ)^3279 := by
    have hnat : (2163178229 : ℕ)^4303*100000000000000^3279 ≤ 33303264825059^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163178229 5000000000 33303264825059 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (259603173/625000000 : ℝ)^4303 ≤ (31569619702487/100000000000000 : ℝ)^3279 := by
    have hnat : (259603173 : ℕ)^4303*100000000000000^3279 ≤ 31569619702487^3279*625000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      259603173 625000000 31569619702487 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (56321933/125000000 : ℝ)^4303 ≤ (4390889431831/12500000000000 : ℝ)^3279 := by
    have hnat : (56321933 : ℕ)^4303*12500000000000^3279 ≤ 4390889431831^3279*125000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56321933 125000000 4390889431831 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163178229/5000000000 : ℝ), (259603173/625000000 : ℝ), (56321933/125000000 : ℝ)] ![(33303264825059/100000000000000 : ℝ), (31569619702487/100000000000000 : ℝ), (4390889431831/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163178229/5000000000 : ℝ)|^4303 ≤ (33303264825059/100000000000000 : ℝ)^3279
        have hw : |(2163178229/5000000000 : ℝ)|=(2163178229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(259603173/625000000 : ℝ)|^4303 ≤ (31569619702487/100000000000000 : ℝ)^3279
        have hw : |(259603173/625000000 : ℝ)|=(259603173/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(56321933/125000000 : ℝ)|^4303 ≤ (4390889431831/12500000000000 : ℝ)^3279
        have hw : |(56321933/125000000 : ℝ)|=(56321933/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s6_4 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-204311377/1000000000 : ℝ)*x 0 + (2622615509/5000000000 : ℝ)*x 1 + (5412064093/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (204311377/1000000000 : ℝ)^4303 ≤ (12442383476643/100000000000000 : ℝ)^3279 := by
    have hnat : (204311377 : ℕ)^4303*100000000000000^3279 ≤ 12442383476643^3279*1000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204311377 1000000000 12442383476643 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622615509/5000000000 : ℝ)^4303 ≤ (42879510707753/100000000000000 : ℝ)^3279 := by
    have hnat : (2622615509 : ℕ)^4303*100000000000000^3279 ≤ 42879510707753^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622615509 5000000000 42879510707753 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412064093/10000000000 : ℝ)^4303 ≤ (44678105804847/100000000000000 : ℝ)^3279 := by
    have hnat : (5412064093 : ℕ)^4303*100000000000000^3279 ≤ 44678105804847^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412064093 10000000000 44678105804847 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-204311377/1000000000 : ℝ), (2622615509/5000000000 : ℝ), (5412064093/10000000000 : ℝ)] ![(12442383476643/100000000000000 : ℝ), (42879510707753/100000000000000 : ℝ), (44678105804847/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-204311377/1000000000 : ℝ)|^4303 ≤ (12442383476643/100000000000000 : ℝ)^3279
        have hw : |(-204311377/1000000000 : ℝ)|=(204311377/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622615509/5000000000 : ℝ)|^4303 ≤ (42879510707753/100000000000000 : ℝ)^3279
        have hw : |(2622615509/5000000000 : ℝ)|=(2622615509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412064093/10000000000 : ℝ)|^4303 ≤ (44678105804847/100000000000000 : ℝ)^3279
        have hw : |(5412064093/10000000000 : ℝ)|=(5412064093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s6_5 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305696883/10000000000 : ℝ)*x 0 + (-196128359/1000000000 : ℝ)*x 1 + (2706032047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305696883/10000000000 : ℝ)^4303 ≤ (43529347622079/100000000000000 : ℝ)^3279 := by
    have hnat : (5305696883 : ℕ)^4303*100000000000000^3279 ≤ 43529347622079^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305696883 10000000000 43529347622079 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196128359/1000000000 : ℝ)^4303 ≤ (2358509310133/20000000000000 : ℝ)^3279 := by
    have hnat : (196128359 : ℕ)^4303*20000000000000^3279 ≤ 2358509310133^3279*1000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196128359 1000000000 2358509310133 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706032047/5000000000 : ℝ)^4303 ≤ (44678105815681/100000000000000 : ℝ)^3279 := by
    have hnat : (2706032047 : ℕ)^4303*100000000000000^3279 ≤ 44678105815681^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706032047 5000000000 44678105815681 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305696883/10000000000 : ℝ), (-196128359/1000000000 : ℝ), (2706032047/5000000000 : ℝ)] ![(43529347622079/100000000000000 : ℝ), (2358509310133/20000000000000 : ℝ), (44678105815681/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305696883/10000000000 : ℝ)|^4303 ≤ (43529347622079/100000000000000 : ℝ)^3279
        have hw : |(5305696883/10000000000 : ℝ)|=(5305696883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-196128359/1000000000 : ℝ)|^4303 ≤ (2358509310133/20000000000000 : ℝ)^3279
        have hw : |(-196128359/1000000000 : ℝ)|=(196128359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706032047/5000000000 : ℝ)|^4303 ≤ (44678105815681/100000000000000 : ℝ)^3279
        have hw : |(2706032047/5000000000 : ℝ)|=(2706032047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s6_6 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305696883/10000000000 : ℝ)*x 0 + (1082412819/2000000000 : ℝ)*x 1 + (-1961283589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305696883/10000000000 : ℝ)^4303 ≤ (43529347622079/100000000000000 : ℝ)^3279 := by
    have hnat : (5305696883 : ℕ)^4303*100000000000000^3279 ≤ 43529347622079^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305696883 10000000000 43529347622079 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082412819/2000000000 : ℝ)^4303 ≤ (22339052913257/50000000000000 : ℝ)^3279 := by
    have hnat : (1082412819 : ℕ)^4303*50000000000000^3279 ≤ 22339052913257^3279*2000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082412819 2000000000 22339052913257 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1961283589/10000000000 : ℝ)^4303 ≤ (471701861711/4000000000000 : ℝ)^3279 := by
    have hnat : (1961283589 : ℕ)^4303*4000000000000^3279 ≤ 471701861711^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1961283589 10000000000 471701861711 4000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305696883/10000000000 : ℝ), (1082412819/2000000000 : ℝ), (-1961283589/10000000000 : ℝ)] ![(43529347622079/100000000000000 : ℝ), (22339052913257/50000000000000 : ℝ), (471701861711/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305696883/10000000000 : ℝ)|^4303 ≤ (43529347622079/100000000000000 : ℝ)^3279
        have hw : |(5305696883/10000000000 : ℝ)|=(5305696883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082412819/2000000000 : ℝ)|^4303 ≤ (22339052913257/50000000000000 : ℝ)^3279
        have hw : |(1082412819/2000000000 : ℝ)|=(1082412819/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1961283589/10000000000 : ℝ)|^4303 ≤ (471701861711/4000000000000 : ℝ)^3279
        have hw : |(-1961283589/10000000000 : ℝ)|=(1961283589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s6_7 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2163190981/5000000000 : ℝ)*x 0 + (2252246839/5000000000 : ℝ)*x 1 + (830983647/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163190981/5000000000 : ℝ)^4303 ≤ (16651761229519/50000000000000 : ℝ)^3279 := by
    have hnat : (2163190981 : ℕ)^4303*50000000000000^3279 ≤ 16651761229519^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163190981 5000000000 16651761229519 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252246839/5000000000 : ℝ)^4303 ≤ (17557107754233/50000000000000 : ℝ)^3279 := by
    have hnat : (2252246839 : ℕ)^4303*50000000000000^3279 ≤ 17557107754233^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252246839 5000000000 17557107754233 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (830983647/2000000000 : ℝ)^4303 ≤ (31582262018803/100000000000000 : ℝ)^3279 := by
    have hnat : (830983647 : ℕ)^4303*100000000000000^3279 ≤ 31582262018803^3279*2000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830983647 2000000000 31582262018803 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163190981/5000000000 : ℝ), (2252246839/5000000000 : ℝ), (830983647/2000000000 : ℝ)] ![(16651761229519/50000000000000 : ℝ), (17557107754233/50000000000000 : ℝ), (31582262018803/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163190981/5000000000 : ℝ)|^4303 ≤ (16651761229519/50000000000000 : ℝ)^3279
        have hw : |(2163190981/5000000000 : ℝ)|=(2163190981/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252246839/5000000000 : ℝ)|^4303 ≤ (17557107754233/50000000000000 : ℝ)^3279
        have hw : |(2252246839/5000000000 : ℝ)|=(2252246839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(830983647/2000000000 : ℝ)|^4303 ≤ (31582262018803/100000000000000 : ℝ)^3279
        have hw : |(830983647/2000000000 : ℝ)|=(830983647/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1343_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (11151/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3677/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3679/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1393/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3679/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1393/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3679/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1393/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3679/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1393/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3679/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1393/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3679/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1393/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1393/12500 : ℝ) ^ (2151/512 : ℝ) ≤ (9918725826131051/100000000000000000000 : ℝ) := by
    have hpowers : (1393/12500 : ℝ)^2151 ≤ (9918725826131051/100000000000000000000 : ℝ)^512 := by
      have hnat : (1393 : ℕ)^2151*100000000000000000000^512 ≤ 9918725826131051^512*12500^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1393 12500 9918725826131051 100000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1393/12500 : ℝ)) (X := (9918725826131051/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3679/25000 : ℝ) ^ (2151/512 : ℝ) ≤ (7974102884771599/25000000000000000000 : ℝ) := by
    have hpowers : (3679/25000 : ℝ)^2151 ≤ (7974102884771599/25000000000000000000 : ℝ)^512 := by
      have hnat : (3679 : ℕ)^2151*25000000000000000000^512 ≤ 7974102884771599^512*25000^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3679 25000 7974102884771599 25000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3679/25000 : ℝ)) (X := (7974102884771599/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50009918725826131051/50000000000000000000 : ℝ) ≤ (1250059019105697/1250000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (50009918725826131051/50000000000000000000 : ℝ)^512 ≤ (1250059019105697/1250000000000000 : ℝ)^2151 := by
      have hnat : (50009918725826131051 : ℕ)^512*1250000000000000^2151 ≤ 1250059019105697^2151*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50009918725826131051 50000000000000000000 1250059019105697 1250000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250059019105697/1250000000000000 : ℝ)) (X := (50009918725826131051/50000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100041815137365217447/100000000000000000000 : ℝ) ≤ (5000497581135573/5000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (100041815137365217447/100000000000000000000 : ℝ)^512 ≤ (5000497581135573/5000000000000000 : ℝ)^2151 := by
      have hnat : (100041815137365217447 : ℕ)^512*5000000000000000^2151 ≤ 5000497581135573^2151*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100041815137365217447 100000000000000000000 5000497581135573 5000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000497581135573/5000000000000000 : ℝ)) (X := (100041815137365217447/100000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (12507974102884771599/12500000000000000000 : ℝ) ≤ (2500379542924179/2500000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (12507974102884771599/12500000000000000000 : ℝ)^512 ≤ (2500379542924179/2500000000000000 : ℝ)^2151 := by
      have hnat : (12507974102884771599 : ℕ)^512*2500000000000000^2151 ≤ 2500379542924179^2151*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12507974102884771599 12500000000000000000 2500379542924179 2500000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500379542924179/2500000000000000 : ℝ)) (X := (12507974102884771599/12500000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(9918725826131051/100000000000000000000 : ℝ) ≤ ((278984606999119479/279062500000000000 : ℝ)+2*(52300942557/35720000000000 : ℝ)*(1393/12500 : ℝ))^(2151/512 : ℝ) := by
    rw [show (278984606999119479/279062500000000000 : ℝ)+2*(52300942557/35720000000000 : ℝ)*(1393/12500 : ℝ)=(1250059019105697/1250000000000000 : ℝ) by norm_num, show 1+2*(9918725826131051/100000000000000000000 : ℝ)=(50009918725826131051/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(7974102884771599/25000000000000000000 : ℝ)+(9918725826131051/100000000000000000000 : ℝ) ≤ ((278984606999119479/279062500000000000 : ℝ)+(52300942557/35720000000000 : ℝ)*((3679/25000 : ℝ)+(1393/12500 : ℝ)))^(2151/512 : ℝ) := by
    rw [show (278984606999119479/279062500000000000 : ℝ)+(52300942557/35720000000000 : ℝ)*((3679/25000 : ℝ)+(1393/12500 : ℝ))=(5000497581135573/5000000000000000 : ℝ) by norm_num, show 1+(7974102884771599/25000000000000000000 : ℝ)+(9918725826131051/100000000000000000000 : ℝ)=(100041815137365217447/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(7974102884771599/25000000000000000000 : ℝ) ≤ ((278984606999119479/279062500000000000 : ℝ)+2*(52300942557/35720000000000 : ℝ)*(3679/25000 : ℝ))^(2151/512 : ℝ) := by
    rw [show (278984606999119479/279062500000000000 : ℝ)+2*(52300942557/35720000000000 : ℝ)*(3679/25000 : ℝ)=(2500379542924179/2500000000000000 : ℝ) by norm_num, show 1+2*(7974102884771599/25000000000000000000 : ℝ)=(12507974102884771599/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (278984606999119479/279062500000000000 : ℝ)*(X 1 0+X 2 0)+(52300942557/35720000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (1393/12500 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (278984606999119479/279062500000000000 : ℝ)) (alpha := (52300942557/35720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (278984606999119479/279062500000000000 : ℝ)*(X 0 1+X 2 1)+(52300942557/35720000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (1393/12500 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (278984606999119479/279062500000000000 : ℝ)) (alpha := (52300942557/35720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (278984606999119479/279062500000000000 : ℝ)*(X 0 2+X 1 2)+(52300942557/35720000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (1393/12500 : ℝ)) (hi := (3679/25000 : ℝ)) (c := (278984606999119479/279062500000000000 : ℝ)) (alpha := (52300942557/35720000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2553877/12500000 : ℝ)*X 0 0+(2706334493/5000000000 : ℝ)*X 0 1+(2622314613/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348985161/10000000000 : ℝ)*X 1 0+(-1064359231/5000000000 : ℝ)*X 1 1+(2622314613/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5348985163/10000000000 : ℝ)*X 2 0+(209785169/400000000 : ℝ)*X 2 1+(-2128718461/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2163178229/5000000000 : ℝ)*X 0 0+(259603173/625000000 : ℝ)*X 0 1+(56321933/125000000 : ℝ)*X 0 2+(2163178229/5000000000 : ℝ)*X 1 0+(259603173/625000000 : ℝ)*X 1 1+(56321933/125000000 : ℝ)*X 1 2+(2163178229/5000000000 : ℝ)*X 2 0+(259603173/625000000 : ℝ)*X 2 1+(56321933/125000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-204311377/1000000000 : ℝ)*X 0 0+(2622615509/5000000000 : ℝ)*X 0 1+(5412064093/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305696883/10000000000 : ℝ)*X 1 0+(-196128359/1000000000 : ℝ)*X 1 1+(2706032047/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305696883/10000000000 : ℝ)*X 2 0+(1082412819/2000000000 : ℝ)*X 2 1+(-1961283589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163190981/5000000000 : ℝ)*X 0 0+(2252246839/5000000000 : ℝ)*X 0 1+(830983647/2000000000 : ℝ)*X 0 2+(2163190981/5000000000 : ℝ)*X 1 0+(2252246839/5000000000 : ℝ)*X 1 1+(830983647/2000000000 : ℝ)*X 1 2+(2163190981/5000000000 : ℝ)*X 2 0+(2252246839/5000000000 : ℝ)*X 2 1+(830983647/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (38576613583820201611141563/6976562500000000000000000000000 : ℝ) := by norm_num
    linear_combination (25949191/2500000000000 : ℝ)*(base19) + (968638147/100000000000000 : ℝ)*(base23) + (7654889/20000000000000 : ℝ)*(lower2) + (138797227/100000000000000 : ℝ)*(upper3) + (2195901/2500000000000 : ℝ)*(upper5) + (2197776923578309/50000000000000 : ℝ)*(major0) + (2197776923578309/50000000000000 : ℝ)*(major1) + (219777692357831/5000000000000 : ℝ)*(major2) + (5950994628712471/100000000000000 : ℝ)*(sp0) + (5951014780768039/100000000000000 : ℝ)*(sp1) + (1487753712524383/25000000000000 : ℝ)*(sp2) + (1420040394915817/50000000000000 : ℝ)*(sp3) + (2648752901/12500000000000 : ℝ)*(sp4) + (10901430629/100000000000000 : ℝ)*(sp7) + (2840091691262263/100000000000000 : ℝ)*(f.failure) + (5951015818735679/100000000000000 : ℝ)*(f.sum) + (5029256758723/1786000000000000000000000000 : ℝ)*base65 + (53856945318398557/6976562500000000000000000000000 : ℝ)*base68 + (41831671405607071/5581250000000000000000000000000 : ℝ)*base69 + (58993481051874761/13953125000000000000000000000000 : ℝ)*base71 + (4997209406967/1786000000000000000000000000 : ℝ)*base73 + (86172693271657071/5581250000000000000000000000000 : ℝ)*base75 + (133340416818734853/27906250000000000000000000000000 : ℝ)*base78 + (238374152786984853/27906250000000000000000000000000 : ℝ)*base80 + (2439781025663/446500000000000000000000000 : ℝ)*base82 + (46401419/5000000000000000000000 : ℝ)*base89 + (46401419/5000000000000000000000 : ℝ)*base91 + (53598581/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (250703779686932649181443/54504394531250000000000000000 : ℝ) := by norm_num
    linear_combination (799330953/100000000000000 : ℝ)*(base19) + (109062031/12500000000000 : ℝ)*(base23) + (46562409/50000000000000 : ℝ)*(upper3) + (32935557/100000000000000 : ℝ)*(lower4) + (46521747/50000000000000 : ℝ)*(upper5) + (2213656839173421/50000000000000 : ℝ)*(major0) + (2213656839173421/50000000000000 : ℝ)*(major1) + (2213656839173421/50000000000000 : ℝ)*(major2) + (3275333323/20000000000000 : ℝ)*(sp1) + (4433965761/25000000000000 : ℝ)*(sp2) + (2997007293343823/50000000000000 : ℝ)*(sp4) + (2996998705345039/50000000000000 : ℝ)*(sp5) + (2996997989164177/50000000000000 : ℝ)*(sp6) + (11174268033917/390625000000 : ℝ)*(sp7) + (11174268033917/390625000000 : ℝ)*(f.failure) + (2997007293343823/50000000000000 : ℝ)*(f.sum) + (258124656477/35720000000000000000000000 : ℝ)*base65 + (225918644154149057/27906250000000000000000000000000 : ℝ)*base68 + (29040952166711557/27906250000000000000000000000000 : ℝ)*base70 + (67093036038430307/27906250000000000000000000000000 : ℝ)*base72 + (3335616172039/893000000000000000000000000 : ℝ)*base73 + (75645903413336557/27906250000000000000000000000000 : ℝ)*base76 + (87230461333586557/27906250000000000000000000000000 : ℝ)*base78 + (240475528861913443/27906250000000000000000000000000 : ℝ)*base79 + (77313044993/893000000000000000000000000 : ℝ)*base82 + (2301/4882812500000000000 : ℝ)*base90 + (2301/4882812500000000000 : ℝ)*base92 + (2301/4882812500000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1343_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1343_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1343_s7_0 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2043110281/10000000000 : ℝ)*x 0 + (541260569/1000000000 : ℝ)*x 1 + (5244686681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2043110281/10000000000 : ℝ)^4303 ≤ (6221177796747/50000000000000 : ℝ)^3279 := by
    have hnat : (2043110281 : ℕ)^4303*50000000000000^3279 ≤ 6221177796747^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2043110281 10000000000 6221177796747 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541260569/1000000000 : ℝ)^4303 ≤ (22341986596277/50000000000000 : ℝ)^3279 := by
    have hnat : (541260569 : ℕ)^4303*50000000000000^3279 ≤ 22341986596277^3279*1000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541260569 1000000000 22341986596277 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244686681/10000000000 : ℝ)^4303 ≤ (1714946848157/4000000000000 : ℝ)^3279 := by
    have hnat : (5244686681 : ℕ)^4303*4000000000000^3279 ≤ 1714946848157^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244686681 10000000000 1714946848157 4000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2043110281/10000000000 : ℝ), (541260569/1000000000 : ℝ), (5244686681/10000000000 : ℝ)] ![(6221177796747/50000000000000 : ℝ), (22341986596277/50000000000000 : ℝ), (1714946848157/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2043110281/10000000000 : ℝ)|^4303 ≤ (6221177796747/50000000000000 : ℝ)^3279
        have hw : |(-2043110281/10000000000 : ℝ)|=(2043110281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541260569/1000000000 : ℝ)|^4303 ≤ (22341986596277/50000000000000 : ℝ)^3279
        have hw : |(541260569/1000000000 : ℝ)|=(541260569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244686681/10000000000 : ℝ)|^4303 ≤ (1714946848157/4000000000000 : ℝ)^3279
        have hw : |(5244686681/10000000000 : ℝ)|=(5244686681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s7_1 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (534896857/1000000000 : ℝ)*x 0 + (-532166113/2500000000 : ℝ)*x 1 + (2622343337/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534896857/1000000000 : ℝ)^4303 ≤ (43995819172211/100000000000000 : ℝ)^3279 := by
    have hnat : (534896857 : ℕ)^4303*100000000000000^3279 ≤ 43995819172211^3279*1000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534896857 1000000000 43995819172211 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (532166113/2500000000 : ℝ)^4303 ≤ (13130509679223/100000000000000 : ℝ)^3279 := by
    have hnat : (532166113 : ℕ)^4303*100000000000000^3279 ≤ 13130509679223^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      532166113 2500000000 13130509679223 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622343337/5000000000 : ℝ)^4303 ≤ (167475277847/390625000000 : ℝ)^3279 := by
    have hnat : (2622343337 : ℕ)^4303*390625000000^3279 ≤ 167475277847^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622343337 5000000000 167475277847 390625000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534896857/1000000000 : ℝ), (-532166113/2500000000 : ℝ), (2622343337/5000000000 : ℝ)] ![(43995819172211/100000000000000 : ℝ), (13130509679223/100000000000000 : ℝ), (167475277847/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534896857/1000000000 : ℝ)|^4303 ≤ (43995819172211/100000000000000 : ℝ)^3279
        have hw : |(534896857/1000000000 : ℝ)|=(534896857/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-532166113/2500000000 : ℝ)|^4303 ≤ (13130509679223/100000000000000 : ℝ)^3279
        have hw : |(-532166113/2500000000 : ℝ)|=(532166113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622343337/5000000000 : ℝ)|^4303 ≤ (167475277847/390625000000 : ℝ)^3279
        have hw : |(2622343337/5000000000 : ℝ)|=(2622343337/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s7_2 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337242139/2500000000 : ℝ)*x 0 + (209787467/400000000 : ℝ)*x 1 + (-2128664471/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337242139/2500000000 : ℝ)^4303 ≤ (43995819021099/100000000000000 : ℝ)^3279 := by
    have hnat : (1337242139 : ℕ)^4303*100000000000000^3279 ≤ 43995819021099^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337242139 2500000000 43995819021099 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209787467/400000000 : ℝ)^4303 ≤ (1071841778489/2500000000000 : ℝ)^3279 := by
    have hnat : (209787467 : ℕ)^4303*2500000000000^3279 ≤ 1071841778489^3279*400000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209787467 400000000 1071841778489 2500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2128664471/10000000000 : ℝ)^4303 ≤ (13130509833023/100000000000000 : ℝ)^3279 := by
    have hnat : (2128664471 : ℕ)^4303*100000000000000^3279 ≤ 13130509833023^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2128664471 10000000000 13130509833023 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337242139/2500000000 : ℝ), (209787467/400000000 : ℝ), (-2128664471/10000000000 : ℝ)] ![(43995819021099/100000000000000 : ℝ), (1071841778489/2500000000000 : ℝ), (13130509833023/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337242139/2500000000 : ℝ)|^4303 ≤ (43995819021099/100000000000000 : ℝ)^3279
        have hw : |(1337242139/2500000000 : ℝ)|=(1337242139/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209787467/400000000 : ℝ)|^4303 ≤ (1071841778489/2500000000000 : ℝ)^3279
        have hw : |(209787467/400000000 : ℝ)|=(209787467/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2128664471/10000000000 : ℝ)|^4303 ≤ (13130509833023/100000000000000 : ℝ)^3279
        have hw : |(-2128664471/10000000000 : ℝ)|=(2128664471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s7_3 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4326360713/10000000000 : ℝ)*x 0 + (519222093/1250000000 : ℝ)*x 1 + (2252813811/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4326360713/10000000000 : ℝ)^4303 ≤ (33303307807797/100000000000000 : ℝ)^3279 := by
    have hnat : (4326360713 : ℕ)^4303*100000000000000^3279 ≤ 33303307807797^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4326360713 10000000000 33303307807797 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (519222093/1250000000 : ℝ)^4303 ≤ (15785438096439/50000000000000 : ℝ)^3279 := by
    have hnat : (519222093 : ℕ)^4303*50000000000000^3279 ≤ 15785438096439^3279*1250000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      519222093 1250000000 15785438096439 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252813811/5000000000 : ℝ)^4303 ≤ (8781453994681/25000000000000 : ℝ)^3279 := by
    have hnat : (2252813811 : ℕ)^4303*25000000000000^3279 ≤ 8781453994681^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252813811 5000000000 8781453994681 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4326360713/10000000000 : ℝ), (519222093/1250000000 : ℝ), (2252813811/5000000000 : ℝ)] ![(33303307807797/100000000000000 : ℝ), (15785438096439/50000000000000 : ℝ), (8781453994681/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4326360713/10000000000 : ℝ)|^4303 ≤ (33303307807797/100000000000000 : ℝ)^3279
        have hw : |(4326360713/10000000000 : ℝ)|=(4326360713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(519222093/1250000000 : ℝ)|^4303 ≤ (15785438096439/50000000000000 : ℝ)^3279
        have hw : |(519222093/1250000000 : ℝ)|=(519222093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252813811/5000000000 : ℝ)|^4303 ≤ (8781453994681/25000000000000 : ℝ)^3279
        have hw : |(2252813811/5000000000 : ℝ)|=(2252813811/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s7_4 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-510780601/2500000000 : ℝ)*x 0 + (2622643781/5000000000 : ℝ)*x 1 + (541200173/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (510780601/2500000000 : ℝ)^4303 ≤ (1244245247731/10000000000000 : ℝ)^3279 := by
    have hnat : (510780601 : ℕ)^4303*10000000000000^3279 ≤ 1244245247731^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510780601 2500000000 1244245247731 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622643781/5000000000 : ℝ)^4303 ≤ (42880117307729/100000000000000 : ℝ)^3279 := by
    have hnat : (2622643781 : ℕ)^4303*100000000000000^3279 ≤ 42880117307729^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622643781 5000000000 42880117307729 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541200173/1000000000 : ℝ)^4303 ≤ (893548604149/2000000000000 : ℝ)^3279 := by
    have hnat : (541200173 : ℕ)^4303*2000000000000^3279 ≤ 893548604149^3279*1000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541200173 1000000000 893548604149 2000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-510780601/2500000000 : ℝ), (2622643781/5000000000 : ℝ), (541200173/1000000000 : ℝ)] ![(1244245247731/10000000000000 : ℝ), (42880117307729/100000000000000 : ℝ), (893548604149/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-510780601/2500000000 : ℝ)|^4303 ≤ (1244245247731/10000000000000 : ℝ)^3279
        have hw : |(-510780601/2500000000 : ℝ)|=(510780601/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622643781/5000000000 : ℝ)|^4303 ≤ (42880117307729/100000000000000 : ℝ)^3279
        have hw : |(2622643781/5000000000 : ℝ)|=(2622643781/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541200173/1000000000 : ℝ)|^4303 ≤ (893548604149/2000000000000 : ℝ)^3279
        have hw : |(541200173/1000000000 : ℝ)|=(541200173/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s7_5 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652855701/5000000000 : ℝ)*x 0 + (-392269881/2000000000 : ℝ)*x 1 + (84562527/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652855701/5000000000 : ℝ)^4303 ≤ (43529503939199/100000000000000 : ℝ)^3279 := by
    have hnat : (2652855701 : ℕ)^4303*100000000000000^3279 ≤ 43529503939199^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652855701 5000000000 43529503939199 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (392269881/2000000000 : ℝ)^4303 ≤ (11793065857807/100000000000000 : ℝ)^3279 := by
    have hnat : (392269881 : ℕ)^4303*100000000000000^3279 ≤ 11793065857807^3279*2000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      392269881 2000000000 11793065857807 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84562527/156250000 : ℝ)^4303 ≤ (44677430185783/100000000000000 : ℝ)^3279 := by
    have hnat : (84562527 : ℕ)^4303*100000000000000^3279 ≤ 44677430185783^3279*156250000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84562527 156250000 44677430185783 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652855701/5000000000 : ℝ), (-392269881/2000000000 : ℝ), (84562527/156250000 : ℝ)] ![(43529503939199/100000000000000 : ℝ), (11793065857807/100000000000000 : ℝ), (44677430185783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652855701/5000000000 : ℝ)|^4303 ≤ (43529503939199/100000000000000 : ℝ)^3279
        have hw : |(2652855701/5000000000 : ℝ)|=(2652855701/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-392269881/2000000000 : ℝ)|^4303 ≤ (11793065857807/100000000000000 : ℝ)^3279
        have hw : |(-392269881/2000000000 : ℝ)|=(392269881/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84562527/156250000 : ℝ)|^4303 ≤ (44677430185783/100000000000000 : ℝ)^3279
        have hw : |(84562527/156250000 : ℝ)|=(84562527/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s7_6 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305711403/10000000000 : ℝ)*x 0 + (2706000863/5000000000 : ℝ)*x 1 + (-61292169/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305711403/10000000000 : ℝ)^4303 ≤ (8705900789993/20000000000000 : ℝ)^3279 := by
    have hnat : (5305711403 : ℕ)^4303*20000000000000^3279 ≤ 8705900789993^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305711403 10000000000 8705900789993 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706000863/5000000000 : ℝ)^4303 ≤ (11169357541029/25000000000000 : ℝ)^3279 := by
    have hnat : (2706000863 : ℕ)^4303*25000000000000^3279 ≤ 11169357541029^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706000863 5000000000 11169357541029 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (61292169/312500000 : ℝ)^4303 ≤ (11793065881479/100000000000000 : ℝ)^3279 := by
    have hnat : (61292169 : ℕ)^4303*100000000000000^3279 ≤ 11793065881479^3279*312500000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61292169 312500000 11793065881479 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305711403/10000000000 : ℝ), (2706000863/5000000000 : ℝ), (-61292169/312500000 : ℝ)] ![(8705900789993/20000000000000 : ℝ), (11169357541029/25000000000000 : ℝ), (11793065881479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305711403/10000000000 : ℝ)|^4303 ≤ (8705900789993/20000000000000 : ℝ)^3279
        have hw : |(5305711403/10000000000 : ℝ)|=(5305711403/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706000863/5000000000 : ℝ)|^4303 ≤ (11169357541029/25000000000000 : ℝ)^3279
        have hw : |(2706000863/5000000000 : ℝ)|=(2706000863/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-61292169/312500000 : ℝ)|^4303 ≤ (11793065881479/100000000000000 : ℝ)^3279
        have hw : |(-61292169/312500000 : ℝ)|=(61292169/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_s7_7 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2163193089/5000000000 : ℝ)*x 0 + (2252184281/5000000000 : ℝ)*x 1 + (4155042277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163193089/5000000000 : ℝ)^4303 ≤ (2081472815493/6250000000000 : ℝ)^3279 := by
    have hnat : (2163193089 : ℕ)^4303*6250000000000^3279 ≤ 2081472815493^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163193089 5000000000 2081472815493 6250000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2252184281/5000000000 : ℝ)^4303 ≤ (2194558475189/6250000000000 : ℝ)^3279 := by
    have hnat : (2252184281 : ℕ)^4303*6250000000000^3279 ≤ 2194558475189^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252184281 5000000000 2194558475189 6250000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4155042277/10000000000 : ℝ)^4303 ≤ (986984354287/3125000000000 : ℝ)^3279 := by
    have hnat : (4155042277 : ℕ)^4303*3125000000000^3279 ≤ 986984354287^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4155042277 10000000000 986984354287 3125000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163193089/5000000000 : ℝ), (2252184281/5000000000 : ℝ), (4155042277/10000000000 : ℝ)] ![(2081472815493/6250000000000 : ℝ), (2194558475189/6250000000000 : ℝ), (986984354287/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163193089/5000000000 : ℝ)|^4303 ≤ (2081472815493/6250000000000 : ℝ)^3279
        have hw : |(2163193089/5000000000 : ℝ)|=(2163193089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2252184281/5000000000 : ℝ)|^4303 ≤ (2194558475189/6250000000000 : ℝ)^3279
        have hw : |(2252184281/5000000000 : ℝ)|=(2252184281/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4155042277/10000000000 : ℝ)|^4303 ≤ (986984354287/3125000000000 : ℝ)^3279
        have hw : |(4155042277/10000000000 : ℝ)|=(4155042277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1343_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (697/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14707/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11151/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3677/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11151/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11151/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3677/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11151/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11151/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3677/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11151/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11151/100000 : ℝ) ^ (2151/512 : ℝ) ≤ (621557934261017/6250000000000000000 : ℝ) := by
    have hpowers : (11151/100000 : ℝ)^2151 ≤ (621557934261017/6250000000000000000 : ℝ)^512 := by
      have hnat : (11151 : ℕ)^2151*6250000000000000000^512 ≤ 621557934261017^512*100000^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11151 100000 621557934261017 6250000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11151/100000 : ℝ)) (X := (621557934261017/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hpowhi : (3677/25000 : ℝ) ^ (2151/512 : ℝ) ≤ (159118138816743/500000000000000000 : ℝ) := by
    have hpowers : (3677/25000 : ℝ)^2151 ≤ (159118138816743/500000000000000000 : ℝ)^512 := by
      have hnat : (3677 : ℕ)^2151*500000000000000000^512 ≤ 159118138816743^512*25000^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3677 25000 159118138816743 500000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3677/25000 : ℝ)) (X := (159118138816743/500000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125621557934261017/3125000000000000000 : ℝ) ≤ (1250059174997659/1250000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (3125621557934261017/3125000000000000000 : ℝ)^512 ≤ (1250059174997659/1250000000000000 : ℝ)^2151 := by
      have hnat : (3125621557934261017 : ℕ)^512*1250000000000000^2151 ≤ 1250059174997659^2151*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125621557934261017 3125000000000000000 1250059174997659 1250000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250059174997659/1250000000000000 : ℝ)) (X := (3125621557934261017/3125000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (12505221069338940609/12500000000000000000 : ℝ) ≤ (5000497026911339/5000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (12505221069338940609/12500000000000000000 : ℝ)^512 ≤ (5000497026911339/5000000000000000 : ℝ)^2151 := by
      have hnat : (12505221069338940609 : ℕ)^512*5000000000000000^2151 ≤ 5000497026911339^2151*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12505221069338940609 12500000000000000000 5000497026911339 5000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000497026911339/5000000000000000 : ℝ)) (X := (12505221069338940609/12500000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (250159118138816743/250000000000000000 : ℝ) ≤ (2500378676916021/2500000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (250159118138816743/250000000000000000 : ℝ)^512 ≤ (2500378676916021/2500000000000000 : ℝ)^2151 := by
      have hnat : (250159118138816743 : ℕ)^512*2500000000000000^2151 ≤ 2500378676916021^2151*250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        250159118138816743 250000000000000000 2500378676916021 2500000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500378676916021/2500000000000000 : ℝ)) (X := (250159118138816743/250000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(621557934261017/6250000000000000000 : ℝ) ≤ ((8890018065440586973/8892500000000000000 : ℝ)+2*(260326920703/177850000000000 : ℝ)*(11151/100000 : ℝ))^(2151/512 : ℝ) := by
    rw [show (8890018065440586973/8892500000000000000 : ℝ)+2*(260326920703/177850000000000 : ℝ)*(11151/100000 : ℝ)=(1250059174997659/1250000000000000 : ℝ) by norm_num, show 1+2*(621557934261017/6250000000000000000 : ℝ)=(3125621557934261017/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(159118138816743/500000000000000000 : ℝ)+(621557934261017/6250000000000000000 : ℝ) ≤ ((8890018065440586973/8892500000000000000 : ℝ)+(260326920703/177850000000000 : ℝ)*((3677/25000 : ℝ)+(11151/100000 : ℝ)))^(2151/512 : ℝ) := by
    rw [show (8890018065440586973/8892500000000000000 : ℝ)+(260326920703/177850000000000 : ℝ)*((3677/25000 : ℝ)+(11151/100000 : ℝ))=(5000497026911339/5000000000000000 : ℝ) by norm_num, show 1+(159118138816743/500000000000000000 : ℝ)+(621557934261017/6250000000000000000 : ℝ)=(12505221069338940609/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(159118138816743/500000000000000000 : ℝ) ≤ ((8890018065440586973/8892500000000000000 : ℝ)+2*(260326920703/177850000000000 : ℝ)*(3677/25000 : ℝ))^(2151/512 : ℝ) := by
    rw [show (8890018065440586973/8892500000000000000 : ℝ)+2*(260326920703/177850000000000 : ℝ)*(3677/25000 : ℝ)=(2500378676916021/2500000000000000 : ℝ) by norm_num, show 1+2*(159118138816743/500000000000000000 : ℝ)=(250159118138816743/250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8890018065440586973/8892500000000000000 : ℝ)*(X 1 0+X 2 0)+(260326920703/177850000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (11151/100000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (8890018065440586973/8892500000000000000 : ℝ)) (alpha := (260326920703/177850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8890018065440586973/8892500000000000000 : ℝ)*(X 0 1+X 2 1)+(260326920703/177850000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (11151/100000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (8890018065440586973/8892500000000000000 : ℝ)) (alpha := (260326920703/177850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8890018065440586973/8892500000000000000 : ℝ)*(X 0 2+X 1 2)+(260326920703/177850000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (11151/100000 : ℝ)) (hi := (3677/25000 : ℝ)) (c := (8890018065440586973/8892500000000000000 : ℝ)) (alpha := (260326920703/177850000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2043110281/10000000000 : ℝ)*X 0 0+(541260569/1000000000 : ℝ)*X 0 1+(5244686681/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534896857/1000000000 : ℝ)*X 1 0+(-532166113/2500000000 : ℝ)*X 1 1+(2622343337/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337242139/2500000000 : ℝ)*X 2 0+(209787467/400000000 : ℝ)*X 2 1+(-2128664471/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4326360713/10000000000 : ℝ)*X 0 0+(519222093/1250000000 : ℝ)*X 0 1+(2252813811/5000000000 : ℝ)*X 0 2+(4326360713/10000000000 : ℝ)*X 1 0+(519222093/1250000000 : ℝ)*X 1 1+(2252813811/5000000000 : ℝ)*X 1 2+(4326360713/10000000000 : ℝ)*X 2 0+(519222093/1250000000 : ℝ)*X 2 1+(2252813811/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-510780601/2500000000 : ℝ)*X 0 0+(2622643781/5000000000 : ℝ)*X 0 1+(541200173/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652855701/5000000000 : ℝ)*X 1 0+(-392269881/2000000000 : ℝ)*X 1 1+(84562527/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305711403/10000000000 : ℝ)*X 2 0+(2706000863/5000000000 : ℝ)*X 2 1+(-61292169/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163193089/5000000000 : ℝ)*X 0 0+(2252184281/5000000000 : ℝ)*X 0 1+(4155042277/10000000000 : ℝ)*X 0 2+(2163193089/5000000000 : ℝ)*X 1 0+(2252184281/5000000000 : ℝ)*X 1 1+(4155042277/10000000000 : ℝ)*X 1 2+(2163193089/5000000000 : ℝ)*X 2 0+(2252184281/5000000000 : ℝ)*X 2 1+(4155042277/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3402064409321575507326039081/444625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1462488157/100000000000000 : ℝ)*(base19) + (1386912583/100000000000000 : ℝ)*(base23) + (32087701/100000000000000 : ℝ)*(lower2) + (4921299/2500000000000 : ℝ)*(upper3) + (7967589/6250000000000 : ℝ)*(upper5) + (68730121408913/1562500000000 : ℝ)*(major0) + (68730121408913/1562500000000 : ℝ)*(major1) + (4398727770170433/100000000000000 : ℝ)*(major2) + (2977641640622563/50000000000000 : ℝ)*(sp0) + (1488827842522357/25000000000000 : ℝ)*(sp1) + (2977655722832501/50000000000000 : ℝ)*(sp2) + (1421063569897871/50000000000000 : ℝ)*(sp3) + (29551332459/100000000000000 : ℝ)*(sp4) + (7656458157/50000000000000 : ℝ)*(sp7) + (355267806589007/12500000000000 : ℝ)*(f.failure) + (1191062566515517/20000000000000 : ℝ)*(f.sum) + (9259265435853/3557000000000000000000000000 : ℝ)*base66 + (593354503100035479/55578125000000000000000000000000 : ℝ)*base68 + (3481770017067869309/889250000000000000000000000000000 : ℝ)*base69 + (832211692984222979/55578125000000000000000000000000 : ℝ)*base72 + (7683482294801/3557000000000000000000000000 : ℝ)*base74 + (8925436967824869309/889250000000000000000000000000000 : ℝ)*base75 + (409465277490584927/27789062500000000000000000000000 : ℝ)*base78 + (105543198185102573/27789062500000000000000000000000 : ℝ)*base79 + (1143067741737/1111562500000000000000000000 : ℝ)*base81 + (3345091/625000000000000000000 : ℝ)*base89 + (3345091/625000000000000000000 : ℝ)*base91 + (2904909/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (859955516602911028391335587/111156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (682755701/50000000000000 : ℝ)*(base19) + (1477354927/100000000000000 : ℝ)*(base23) + (116699161/25000000000000 : ℝ)*(lower1) + (158500099/100000000000000 : ℝ)*(upper3) + (10107497/20000000000000 : ℝ)*(lower4) + (159852579/100000000000000 : ℝ)*(upper5) + (1107612640077177/25000000000000 : ℝ)*(major0) + (1107612640077177/25000000000000 : ℝ)*(major1) + (1107612640077177/25000000000000 : ℝ)*(major2) + (948242351/50000000000000 : ℝ)*(sp2) + (2999130708937257/50000000000000 : ℝ)*(sp4) + (749782506545389/12500000000000 : ℝ)*(sp5) + (1199651608806977/20000000000000 : ℝ)*(sp6) + (715659861215247/25000000000000 : ℝ)*(sp7) + (715659861215247/25000000000000 : ℝ)*(f.failure) + (2999130708937257/50000000000000 : ℝ)*(f.sum) + (190318080521/2223125000000000000000000000 : ℝ)*base65 + (5096192919230615221/222312500000000000000000000000000 : ℝ)*base67 + (518790822105365221/222312500000000000000000000000000 : ℝ)*base69 + (37162020424133865221/222312500000000000000000000000000 : ℝ)*base71 + (4793258315239/2223125000000000000000000000 : ℝ)*base74 + (532896924604615221/222312500000000000000000000000000 : ℝ)*base75 + (1303537850506822279/222312500000000000000000000000000 : ℝ)*base78 + (2636716742272134779/222312500000000000000000000000000 : ℝ)*base80 + (43335361291721/8892500000000000000000000000 : ℝ)*base82 + (19646211/1250000000000000000000 : ℝ)*base89 + (19646211/1250000000000000000000 : ℝ)*base91 + (19646211/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1343_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3677/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11151/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (697/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1343_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1343_box_0 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1875932299/10000000000 : ℝ)*x 0 + (2694949761/5000000000 : ℝ)*x 1 + (673737401/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1875932299/10000000000 : ℝ)^4303 ≤ (2224743272827/20000000000000 : ℝ)^3279 := by
    have hnat : (1875932299 : ℕ)^4303*20000000000000^3279 ≤ 2224743272827^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1875932299 10000000000 2224743272827 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2694949761/5000000000 : ℝ)^4303 ≤ (22219071754373/50000000000000 : ℝ)^3279 := by
    have hnat : (2694949761 : ℕ)^4303*50000000000000^3279 ≤ 22219071754373^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694949761 5000000000 22219071754373 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (673737401/1250000000 : ℝ)^4303 ≤ (44438140111439/100000000000000 : ℝ)^3279 := by
    have hnat : (673737401 : ℕ)^4303*100000000000000^3279 ≤ 44438140111439^3279*1250000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      673737401 1250000000 44438140111439 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1875932299/10000000000 : ℝ), (2694949761/5000000000 : ℝ), (673737401/1250000000 : ℝ)] ![(2224743272827/20000000000000 : ℝ), (22219071754373/50000000000000 : ℝ), (44438140111439/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1875932299/10000000000 : ℝ)|^4303 ≤ (2224743272827/20000000000000 : ℝ)^3279
        have hw : |(-1875932299/10000000000 : ℝ)|=(1875932299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2694949761/5000000000 : ℝ)|^4303 ≤ (22219071754373/50000000000000 : ℝ)^3279
        have hw : |(2694949761/5000000000 : ℝ)|=(2694949761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(673737401/1250000000 : ℝ)|^4303 ≤ (44438140111439/100000000000000 : ℝ)^3279
        have hw : |(673737401/1250000000 : ℝ)|=(673737401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_1 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2642588939/5000000000 : ℝ)*x 0 + (-1009704961/5000000000 : ℝ)*x 1 + (2694949667/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642588939/5000000000 : ℝ)^4303 ≤ (43308565765427/100000000000000 : ℝ)^3279 := by
    have hnat : (2642588939 : ℕ)^4303*100000000000000^3279 ≤ 43308565765427^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642588939 5000000000 43308565765427 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1009704961/5000000000 : ℝ)^4303 ≤ (1225329274597/10000000000000 : ℝ)^3279 := by
    have hnat : (1009704961 : ℕ)^4303*10000000000000^3279 ≤ 1225329274597^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1009704961 5000000000 1225329274597 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2694949667/5000000000 : ℝ)^4303 ≤ (44438141474689/100000000000000 : ℝ)^3279 := by
    have hnat : (2694949667 : ℕ)^4303*100000000000000^3279 ≤ 44438141474689^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2694949667 5000000000 44438141474689 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642588939/5000000000 : ℝ), (-1009704961/5000000000 : ℝ), (2694949667/5000000000 : ℝ)] ![(43308565765427/100000000000000 : ℝ), (1225329274597/10000000000000 : ℝ), (44438141474689/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642588939/5000000000 : ℝ)|^4303 ≤ (43308565765427/100000000000000 : ℝ)^3279
        have hw : |(2642588939/5000000000 : ℝ)|=(2642588939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1009704961/5000000000 : ℝ)|^4303 ≤ (1225329274597/10000000000000 : ℝ)^3279
        have hw : |(-1009704961/5000000000 : ℝ)|=(1009704961/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2694949667/5000000000 : ℝ)|^4303 ≤ (44438141474689/100000000000000 : ℝ)^3279
        have hw : |(2694949667/5000000000 : ℝ)|=(2694949667/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_2 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5285177467/10000000000 : ℝ)*x 0 + (5389899721/10000000000 : ℝ)*x 1 + (-40388199/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5285177467/10000000000 : ℝ)^4303 ≤ (10827140336449/25000000000000 : ℝ)^3279 := by
    have hnat : (5285177467 : ℕ)^4303*25000000000000^3279 ≤ 10827140336449^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5285177467 10000000000 10827140336449 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5389899721/10000000000 : ℝ)^4303 ≤ (5554768207727/12500000000000 : ℝ)^3279 := by
    have hnat : (5389899721 : ℕ)^4303*12500000000000^3279 ≤ 5554768207727^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5389899721 10000000000 5554768207727 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40388199/200000000 : ℝ)^4303 ≤ (490131718757/4000000000000 : ℝ)^3279 := by
    have hnat : (40388199 : ℕ)^4303*4000000000000^3279 ≤ 490131718757^3279*200000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40388199 200000000 490131718757 4000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5285177467/10000000000 : ℝ), (5389899721/10000000000 : ℝ), (-40388199/200000000 : ℝ)] ![(10827140336449/25000000000000 : ℝ), (5554768207727/12500000000000 : ℝ), (490131718757/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5285177467/10000000000 : ℝ)|^4303 ≤ (10827140336449/25000000000000 : ℝ)^3279
        have hw : |(5285177467/10000000000 : ℝ)|=(5285177467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5389899721/10000000000 : ℝ)|^4303 ≤ (5554768207727/12500000000000 : ℝ)^3279
        have hw : |(5389899721/10000000000 : ℝ)|=(5389899721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-40388199/200000000 : ℝ)|^4303 ≤ (490131718757/4000000000000 : ℝ)^3279
        have hw : |(-40388199/200000000 : ℝ)|=(40388199/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_3 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2237264111/5000000000 : ℝ)*x 0 + (1064040921/2500000000 : ℝ)*x 1 + (4256163971/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2237264111/5000000000 : ℝ)^4303 ≤ (696159878917/2000000000000 : ℝ)^3279 := by
    have hnat : (2237264111 : ℕ)^4303*2000000000000^3279 ≤ 696159878917^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2237264111 5000000000 696159878917 2000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1064040921/2500000000 : ℝ)^4303 ≤ (6519200315213/20000000000000 : ℝ)^3279 := by
    have hnat : (1064040921 : ℕ)^4303*20000000000000^3279 ≤ 6519200315213^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1064040921 2500000000 6519200315213 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4256163971/10000000000 : ℝ)^4303 ≤ (101862513939/312500000000 : ℝ)^3279 := by
    have hnat : (4256163971 : ℕ)^4303*312500000000^3279 ≤ 101862513939^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4256163971 10000000000 101862513939 312500000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2237264111/5000000000 : ℝ), (1064040921/2500000000 : ℝ), (4256163971/10000000000 : ℝ)] ![(696159878917/2000000000000 : ℝ), (6519200315213/20000000000000 : ℝ), (101862513939/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2237264111/5000000000 : ℝ)|^4303 ≤ (696159878917/2000000000000 : ℝ)^3279
        have hw : |(2237264111/5000000000 : ℝ)|=(2237264111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1064040921/2500000000 : ℝ)|^4303 ≤ (6519200315213/20000000000000 : ℝ)^3279
        have hw : |(1064040921/2500000000 : ℝ)|=(1064040921/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4256163971/10000000000 : ℝ)|^4303 ≤ (101862513939/312500000000 : ℝ)^3279
        have hw : |(4256163971/10000000000 : ℝ)|=(4256163971/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_4 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1106519557/5000000000 : ℝ)*x 0 + (1316236871/2500000000 : ℝ)*x 1 + (5264947979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1106519557/5000000000 : ℝ)^4303 ≤ (13817692225277/100000000000000 : ℝ)^3279 := by
    have hnat : (1106519557 : ℕ)^4303*100000000000000^3279 ≤ 13817692225277^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106519557 5000000000 13817692225277 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316236871/2500000000 : ℝ)^4303 ≤ (21545575612507/50000000000000 : ℝ)^3279 := by
    have hnat : (1316236871 : ℕ)^4303*50000000000000^3279 ≤ 21545575612507^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316236871 2500000000 21545575612507 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264947979/10000000000 : ℝ)^4303 ≤ (8618231308311/20000000000000 : ℝ)^3279 := by
    have hnat : (5264947979 : ℕ)^4303*20000000000000^3279 ≤ 8618231308311^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264947979 10000000000 8618231308311 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1106519557/5000000000 : ℝ), (1316236871/2500000000 : ℝ), (5264947979/10000000000 : ℝ)] ![(13817692225277/100000000000000 : ℝ), (21545575612507/50000000000000 : ℝ), (8618231308311/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1106519557/5000000000 : ℝ)|^4303 ≤ (13817692225277/100000000000000 : ℝ)^3279
        have hw : |(-1106519557/5000000000 : ℝ)|=(1106519557/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316236871/2500000000 : ℝ)|^4303 ≤ (21545575612507/50000000000000 : ℝ)^3279
        have hw : |(1316236871/2500000000 : ℝ)|=(1316236871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264947979/10000000000 : ℝ)|^4303 ≤ (8618231308311/20000000000000 : ℝ)^3279
        have hw : |(5264947979/10000000000 : ℝ)|=(5264947979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_5 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372937127/10000000000 : ℝ)*x 0 + (-517389067/2500000000 : ℝ)*x 1 + (5264948241/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372937127/10000000000 : ℝ)^4303 ≤ (11063677495001/25000000000000 : ℝ)^3279 := by
    have hnat : (5372937127 : ℕ)^4303*25000000000000^3279 ≤ 11063677495001^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372937127 10000000000 11063677495001 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (517389067/2500000000 : ℝ)^4303 ≤ (1581766331383/12500000000000 : ℝ)^3279 := by
    have hnat : (517389067 : ℕ)^4303*12500000000000^3279 ≤ 1581766331383^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517389067 2500000000 1581766331383 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264948241/10000000000 : ℝ)^4303 ≤ (43091159355563/100000000000000 : ℝ)^3279 := by
    have hnat : (5264948241 : ℕ)^4303*100000000000000^3279 ≤ 43091159355563^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264948241 10000000000 43091159355563 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372937127/10000000000 : ℝ), (-517389067/2500000000 : ℝ), (5264948241/10000000000 : ℝ)] ![(11063677495001/25000000000000 : ℝ), (1581766331383/12500000000000 : ℝ), (43091159355563/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372937127/10000000000 : ℝ)|^4303 ≤ (11063677495001/25000000000000 : ℝ)^3279
        have hw : |(5372937127/10000000000 : ℝ)|=(5372937127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-517389067/2500000000 : ℝ)|^4303 ≤ (1581766331383/12500000000000 : ℝ)^3279
        have hw : |(-517389067/2500000000 : ℝ)|=(517389067/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264948241/10000000000 : ℝ)|^4303 ≤ (43091159355563/100000000000000 : ℝ)^3279
        have hw : |(5264948241/10000000000 : ℝ)|=(5264948241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_6 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5372938097/10000000000 : ℝ)*x 0 + (2632473779/5000000000 : ℝ)*x 1 + (-16556447/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5372938097/10000000000 : ℝ)^4303 ≤ (8850944092909/20000000000000 : ℝ)^3279 := by
    have hnat : (5372938097 : ℕ)^4303*20000000000000^3279 ≤ 8850944092909^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5372938097 10000000000 8850944092909 20000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632473779/5000000000 : ℝ)^4303 ≤ (4309115201981/10000000000000 : ℝ)^3279 := by
    have hnat : (2632473779 : ℕ)^4303*10000000000000^3279 ≤ 4309115201981^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632473779 5000000000 4309115201981 10000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16556447/80000000 : ℝ)^4303 ≤ (506165099907/4000000000000 : ℝ)^3279 := by
    have hnat : (16556447 : ℕ)^4303*4000000000000^3279 ≤ 506165099907^3279*80000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16556447 80000000 506165099907 4000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5372938097/10000000000 : ℝ), (2632473779/5000000000 : ℝ), (-16556447/80000000 : ℝ)] ![(8850944092909/20000000000000 : ℝ), (4309115201981/10000000000000 : ℝ), (506165099907/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5372938097/10000000000 : ℝ)|^4303 ≤ (8850944092909/20000000000000 : ℝ)^3279
        have hw : |(5372938097/10000000000 : ℝ)|=(5372938097/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632473779/5000000000 : ℝ)|^4303 ≤ (4309115201981/10000000000000 : ℝ)^3279
        have hw : |(2632473779/5000000000 : ℝ)|=(2632473779/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-16556447/80000000 : ℝ)|^4303 ≤ (506165099907/4000000000000 : ℝ)^3279
        have hw : |(-16556447/80000000 : ℝ)|=(16556447/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_7 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4177265663/10000000000 : ℝ)*x 0 + (4404742211/10000000000 : ℝ)*x 1 + (4404740877/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4177265663/10000000000 : ℝ)^4303 ≤ (3975670431537/12500000000000 : ℝ)^3279 := by
    have hnat : (4177265663 : ℕ)^4303*12500000000000^3279 ≤ 3975670431537^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4177265663 10000000000 3975670431537 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4404742211/10000000000 : ℝ)^4303 ≤ (4262165630623/12500000000000 : ℝ)^3279 := by
    have hnat : (4404742211 : ℕ)^4303*12500000000000^3279 ≤ 4262165630623^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404742211 10000000000 4262165630623 12500000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4404740877/10000000000 : ℝ)^4303 ≤ (34097311493541/100000000000000 : ℝ)^3279 := by
    have hnat : (4404740877 : ℕ)^4303*100000000000000^3279 ≤ 34097311493541^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4404740877 10000000000 34097311493541 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4177265663/10000000000 : ℝ), (4404742211/10000000000 : ℝ), (4404740877/10000000000 : ℝ)] ![(3975670431537/12500000000000 : ℝ), (4262165630623/12500000000000 : ℝ), (34097311493541/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4177265663/10000000000 : ℝ)|^4303 ≤ (3975670431537/12500000000000 : ℝ)^3279
        have hw : |(4177265663/10000000000 : ℝ)|=(4177265663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4404742211/10000000000 : ℝ)|^4303 ≤ (4262165630623/12500000000000 : ℝ)^3279
        have hw : |(4404742211/10000000000 : ℝ)|=(4404742211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4404740877/10000000000 : ℝ)|^4303 ≤ (34097311493541/100000000000000 : ℝ)^3279
        have hw : |(4404740877/10000000000 : ℝ)|=(4404740877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_8 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2142242951/10000000000 : ℝ)*x 0 + (129473053/250000000 : ℝ)*x 1 + (1350980097/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2142242951/10000000000 : ℝ)^4303 ≤ (13240533771973/100000000000000 : ℝ)^3279 := by
    have hnat : (2142242951 : ℕ)^4303*100000000000000^3279 ≤ 13240533771973^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142242951 10000000000 13240533771973 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (129473053/250000000 : ℝ)^4303 ≤ (2635597692189/6250000000000 : ℝ)^3279 := by
    have hnat : (129473053 : ℕ)^4303*6250000000000^3279 ≤ 2635597692189^3279*250000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      129473053 250000000 2635597692189 6250000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350980097/2500000000 : ℝ)^4303 ≤ (44589903142099/100000000000000 : ℝ)^3279 := by
    have hnat : (1350980097 : ℕ)^4303*100000000000000^3279 ≤ 44589903142099^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350980097 2500000000 44589903142099 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2142242951/10000000000 : ℝ), (129473053/250000000 : ℝ), (1350980097/2500000000 : ℝ)] ![(13240533771973/100000000000000 : ℝ), (2635597692189/6250000000000 : ℝ), (44589903142099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2142242951/10000000000 : ℝ)|^4303 ≤ (13240533771973/100000000000000 : ℝ)^3279
        have hw : |(-2142242951/10000000000 : ℝ)|=(2142242951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(129473053/250000000 : ℝ)|^4303 ≤ (2635597692189/6250000000000 : ℝ)^3279
        have hw : |(129473053/250000000 : ℝ)|=(129473053/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350980097/2500000000 : ℝ)|^4303 ≤ (44589903142099/100000000000000 : ℝ)^3279
        have hw : |(1350980097/2500000000 : ℝ)|=(1350980097/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_9 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275325199/10000000000 : ℝ)*x 0 + (-100682589/500000000 : ℝ)*x 1 + (1350979787/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275325199/10000000000 : ℝ)^4303 ≤ (21601323615107/50000000000000 : ℝ)^3279 := by
    have hnat : (5275325199 : ℕ)^4303*50000000000000^3279 ≤ 21601323615107^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275325199 10000000000 21601323615107 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100682589/500000000 : ℝ)^4303 ≤ (762966439859/6250000000000 : ℝ)^3279 := by
    have hnat : (100682589 : ℕ)^4303*6250000000000^3279 ≤ 762966439859^3279*500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100682589 500000000 762966439859 6250000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1350979787/2500000000 : ℝ)^4303 ≤ (44589889715093/100000000000000 : ℝ)^3279 := by
    have hnat : (1350979787 : ℕ)^4303*100000000000000^3279 ≤ 44589889715093^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1350979787 2500000000 44589889715093 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275325199/10000000000 : ℝ), (-100682589/500000000 : ℝ), (1350979787/2500000000 : ℝ)] ![(21601323615107/50000000000000 : ℝ), (762966439859/6250000000000 : ℝ), (44589889715093/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275325199/10000000000 : ℝ)|^4303 ≤ (21601323615107/50000000000000 : ℝ)^3279
        have hw : |(5275325199/10000000000 : ℝ)|=(5275325199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100682589/500000000 : ℝ)|^4303 ≤ (762966439859/6250000000000 : ℝ)^3279
        have hw : |(-100682589/500000000 : ℝ)|=(100682589/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1350979787/2500000000 : ℝ)|^4303 ≤ (44589889715093/100000000000000 : ℝ)^3279
        have hw : |(1350979787/2500000000 : ℝ)|=(1350979787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_10 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5275325839/10000000000 : ℝ)*x 0 + (5403918941/10000000000 : ℝ)*x 1 + (-2013651197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5275325839/10000000000 : ℝ)^4303 ≤ (21601327054177/50000000000000 : ℝ)^3279 := by
    have hnat : (5275325839 : ℕ)^4303*50000000000000^3279 ≤ 21601327054177^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5275325839 10000000000 21601327054177 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5403918941/10000000000 : ℝ)^4303 ≤ (44589887473649/100000000000000 : ℝ)^3279 := by
    have hnat : (5403918941 : ℕ)^4303*100000000000000^3279 ≤ 44589887473649^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403918941 10000000000 44589887473649 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2013651197/10000000000 : ℝ)^4303 ≤ (12207458399651/100000000000000 : ℝ)^3279 := by
    have hnat : (2013651197 : ℕ)^4303*100000000000000^3279 ≤ 12207458399651^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013651197 10000000000 12207458399651 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5275325839/10000000000 : ℝ), (5403918941/10000000000 : ℝ), (-2013651197/10000000000 : ℝ)] ![(21601327054177/50000000000000 : ℝ), (44589887473649/100000000000000 : ℝ), (12207458399651/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5275325839/10000000000 : ℝ)|^4303 ≤ (21601327054177/50000000000000 : ℝ)^3279
        have hw : |(5275325839/10000000000 : ℝ)|=(5275325839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5403918941/10000000000 : ℝ)|^4303 ≤ (44589887473649/100000000000000 : ℝ)^3279
        have hw : |(5403918941/10000000000 : ℝ)|=(5403918941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2013651197/10000000000 : ℝ)|^4303 ≤ (12207458399651/100000000000000 : ℝ)^3279
        have hw : |(-2013651197/10000000000 : ℝ)|=(2013651197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_11 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (140853829/312500000 : ℝ)*x 0 + (4239478897/10000000000 : ℝ)*x 1 + (169579181/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (140853829/312500000 : ℝ)^4303 ≤ (17571578450253/50000000000000 : ℝ)^3279 := by
    have hnat : (140853829 : ℕ)^4303*50000000000000^3279 ≤ 17571578450253^3279*312500000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      140853829 312500000 17571578450253 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4239478897/10000000000 : ℝ)^4303 ≤ (32428418388467/100000000000000 : ℝ)^3279 := by
    have hnat : (4239478897 : ℕ)^4303*100000000000000^3279 ≤ 32428418388467^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239478897 10000000000 32428418388467 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169579181/400000000 : ℝ)^4303 ≤ (16214212346137/50000000000000 : ℝ)^3279 := by
    have hnat : (169579181 : ℕ)^4303*50000000000000^3279 ≤ 16214212346137^3279*400000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169579181 400000000 16214212346137 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(140853829/312500000 : ℝ), (4239478897/10000000000 : ℝ), (169579181/400000000 : ℝ)] ![(17571578450253/50000000000000 : ℝ), (32428418388467/100000000000000 : ℝ), (16214212346137/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(140853829/312500000 : ℝ)|^4303 ≤ (17571578450253/50000000000000 : ℝ)^3279
        have hw : |(140853829/312500000 : ℝ)|=(140853829/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4239478897/10000000000 : ℝ)|^4303 ≤ (32428418388467/100000000000000 : ℝ)^3279
        have hw : |(4239478897/10000000000 : ℝ)|=(4239478897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169579181/400000000 : ℝ)|^4303 ≤ (16214212346137/50000000000000 : ℝ)^3279
        have hw : |(169579181/400000000 : ℝ)|=(169579181/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_12 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1947062137/10000000000 : ℝ)*x 0 + (2736860773/5000000000 : ℝ)*x 1 + (525387743/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1947062137/10000000000 : ℝ)^4303 ≤ (11680461346637/100000000000000 : ℝ)^3279 := by
    have hnat : (1947062137 : ℕ)^4303*100000000000000^3279 ≤ 11680461346637^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1947062137 10000000000 11680461346637 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2736860773/5000000000 : ℝ)^4303 ≤ (45347246134801/100000000000000 : ℝ)^3279 := by
    have hnat : (2736860773 : ℕ)^4303*100000000000000^3279 ≤ 45347246134801^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736860773 5000000000 45347246134801 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (525387743/1000000000 : ℝ)^4303 ≤ (21486146252837/50000000000000 : ℝ)^3279 := by
    have hnat : (525387743 : ℕ)^4303*50000000000000^3279 ≤ 21486146252837^3279*1000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      525387743 1000000000 21486146252837 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1947062137/10000000000 : ℝ), (2736860773/5000000000 : ℝ), (525387743/1000000000 : ℝ)] ![(11680461346637/100000000000000 : ℝ), (45347246134801/100000000000000 : ℝ), (21486146252837/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1947062137/10000000000 : ℝ)|^4303 ≤ (11680461346637/100000000000000 : ℝ)^3279
        have hw : |(-1947062137/10000000000 : ℝ)|=(1947062137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2736860773/5000000000 : ℝ)|^4303 ≤ (45347246134801/100000000000000 : ℝ)^3279
        have hw : |(2736860773/5000000000 : ℝ)|=(2736860773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(525387743/1000000000 : ℝ)|^4303 ≤ (21486146252837/50000000000000 : ℝ)^3279
        have hw : |(525387743/1000000000 : ℝ)|=(525387743/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_13 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380710507/10000000000 : ℝ)*x 0 + (-2073894989/10000000000 : ℝ)*x 1 + (5253877627/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380710507/10000000000 : ℝ)^4303 ≤ (2216937495039/5000000000000 : ℝ)^3279 := by
    have hnat : (5380710507 : ℕ)^4303*5000000000000^3279 ≤ 2216937495039^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380710507 10000000000 2216937495039 5000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2073894989/10000000000 : ℝ)^4303 ≤ (12688955464921/100000000000000 : ℝ)^3279 := by
    have hnat : (2073894989 : ℕ)^4303*100000000000000^3279 ≤ 12688955464921^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2073894989 10000000000 12688955464921 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5253877627/10000000000 : ℝ)^4303 ≤ (8393026293/19531250000 : ℝ)^3279 := by
    have hnat : (5253877627 : ℕ)^4303*19531250000^3279 ≤ 8393026293^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253877627 10000000000 8393026293 19531250000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380710507/10000000000 : ℝ), (-2073894989/10000000000 : ℝ), (5253877627/10000000000 : ℝ)] ![(2216937495039/5000000000000 : ℝ), (12688955464921/100000000000000 : ℝ), (8393026293/19531250000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380710507/10000000000 : ℝ)|^4303 ≤ (2216937495039/5000000000000 : ℝ)^3279
        have hw : |(5380710507/10000000000 : ℝ)|=(5380710507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2073894989/10000000000 : ℝ)|^4303 ≤ (12688955464921/100000000000000 : ℝ)^3279
        have hw : |(-2073894989/10000000000 : ℝ)|=(2073894989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5253877627/10000000000 : ℝ)|^4303 ≤ (8393026293/19531250000 : ℝ)^3279
        have hw : |(5253877627/10000000000 : ℝ)|=(5253877627/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_14 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5380710249/10000000000 : ℝ)*x 0 + (164183673/312500000 : ℝ)*x 1 + (-1036947729/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5380710249/10000000000 : ℝ)^4303 ≤ (44338747110849/100000000000000 : ℝ)^3279 := by
    have hnat : (5380710249 : ℕ)^4303*100000000000000^3279 ≤ 44338747110849^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5380710249 10000000000 44338747110849 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164183673/312500000 : ℝ)^4303 ≤ (21486146821709/50000000000000 : ℝ)^3279 := by
    have hnat : (164183673 : ℕ)^4303*50000000000000^3279 ≤ 21486146821709^3279*312500000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164183673 312500000 21486146821709 50000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1036947729/5000000000 : ℝ)^4303 ≤ (3172239807647/25000000000000 : ℝ)^3279 := by
    have hnat : (1036947729 : ℕ)^4303*25000000000000^3279 ≤ 3172239807647^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036947729 5000000000 3172239807647 25000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5380710249/10000000000 : ℝ), (164183673/312500000 : ℝ), (-1036947729/5000000000 : ℝ)] ![(44338747110849/100000000000000 : ℝ), (21486146821709/50000000000000 : ℝ), (3172239807647/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5380710249/10000000000 : ℝ)|^4303 ≤ (44338747110849/100000000000000 : ℝ)^3279
        have hw : |(5380710249/10000000000 : ℝ)|=(5380710249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164183673/312500000 : ℝ)|^4303 ≤ (21486146821709/50000000000000 : ℝ)^3279
        have hw : |(164183673/312500000 : ℝ)|=(164183673/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1036947729/5000000000 : ℝ)|^4303 ≤ (3172239807647/25000000000000 : ℝ)^3279
        have hw : |(-1036947729/5000000000 : ℝ)|=(1036947729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1343_box_15 (p : ℝ) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4150480851/10000000000 : ℝ)*x 0 + (1104473691/2500000000 : ℝ)*x 1 + (2208947291/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4150480851/10000000000 : ℝ)^4303 ≤ (31538006723177/100000000000000 : ℝ)^3279 := by
    have hnat : (4150480851 : ℕ)^4303*100000000000000^3279 ≤ 31538006723177^3279*10000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150480851 10000000000 31538006723177 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1104473691/2500000000 : ℝ)^4303 ≤ (34230997556299/100000000000000 : ℝ)^3279 := by
    have hnat : (1104473691 : ℕ)^4303*100000000000000^3279 ≤ 34230997556299^3279*2500000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1104473691 2500000000 34230997556299 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2208947291/5000000000 : ℝ)^4303 ≤ (34230995705729/100000000000000 : ℝ)^3279 := by
    have hnat : (2208947291 : ℕ)^4303*100000000000000^3279 ≤ 34230995705729^3279*5000000000^4303 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2208947291 5000000000 34230995705729 100000000000000 4303 3279 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4303/1024 : ℝ)) 4303 3279 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4150480851/10000000000 : ℝ), (1104473691/2500000000 : ℝ), (2208947291/5000000000 : ℝ)] ![(31538006723177/100000000000000 : ℝ), (34230997556299/100000000000000 : ℝ), (34230995705729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4150480851/10000000000 : ℝ)|^4303 ≤ (31538006723177/100000000000000 : ℝ)^3279
        have hw : |(4150480851/10000000000 : ℝ)|=(4150480851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1104473691/2500000000 : ℝ)|^4303 ≤ (34230997556299/100000000000000 : ℝ)^3279
        have hw : |(1104473691/2500000000 : ℝ)|=(1104473691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2208947291/5000000000 : ℝ)|^4303 ≤ (34230995705729/100000000000000 : ℝ)^3279
        have hw : |(2208947291/5000000000 : ℝ)|=(2208947291/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1343_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (697/6250 : ℝ)*pair X i i ≤ pair X i h) :
    -(7857/12500 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58943/100000 : ℝ) ∧ (1999/2500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (21089/25000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14707/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (697/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14707/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (697/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14707/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (697/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14707/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (697/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14707/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (697/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14707/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (697/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (697/6250 : ℝ) ^ (2151/512 : ℝ) ≤ (4974337133169479/50000000000000000000 : ℝ) := by
    have hpowers : (697/6250 : ℝ)^2151 ≤ (4974337133169479/50000000000000000000 : ℝ)^512 := by
      have hnat : (697 : ℕ)^2151*50000000000000000000^512 ≤ 4974337133169479^512*6250^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        697 6250 4974337133169479 50000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (697/6250 : ℝ)) (X := (4974337133169479/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14707/100000 : ℝ) ^ (2151/512 : ℝ) ≤ (15907269348725179/50000000000000000000 : ℝ) := by
    have hpowers : (14707/100000 : ℝ)^2151 ≤ (15907269348725179/50000000000000000000 : ℝ)^512 := by
      have hnat : (14707 : ℕ)^2151*50000000000000000000^512 ≤ 15907269348725179^512*100000^2151 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14707 100000 15907269348725179 50000000000000000000 2151 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14707/100000 : ℝ)) (X := (15907269348725179/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004974337133169479/25000000000000000000 : ℝ) ≤ (10000473578348183/10000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (25004974337133169479/25000000000000000000 : ℝ)^512 ≤ (10000473578348183/10000000000000000 : ℝ)^2151 := by
      have hnat : (25004974337133169479 : ℕ)^512*10000000000000000^2151 ≤ 10000473578348183^2151*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004974337133169479 25000000000000000000 10000473578348183 10000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000473578348183/10000000000000000 : ℝ)) (X := (25004974337133169479/25000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25010440803240947329/25000000000000000000 : ℝ) ≤ (2000198785342827/2000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (25010440803240947329/25000000000000000000 : ℝ)^512 ≤ (2000198785342827/2000000000000000 : ℝ)^2151 := by
      have hnat : (25010440803240947329 : ℕ)^512*2000000000000000^2151 ≤ 2000198785342827^2151*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010440803240947329 25000000000000000000 2000198785342827 2000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000198785342827/2000000000000000 : ℝ)) (X := (25010440803240947329/25000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25015907269348725179/25000000000000000000 : ℝ) ≤ (10001514275080087/10000000000000000 : ℝ) ^ (2151/512 : ℝ) := by
    have hpowers : (25015907269348725179/25000000000000000000 : ℝ)^512 ≤ (10001514275080087/10000000000000000 : ℝ)^2151 := by
      have hnat : (25015907269348725179 : ℕ)^512*10000000000000000^2151 ≤ 10001514275080087^2151*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25015907269348725179 25000000000000000000 10001514275080087 10000000000000000 512 2151 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001514275080087/10000000000000000 : ℝ)) (X := (25015907269348725179/25000000000000000000 : ℝ)) (by norm_num) 2151 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4974337133169479/50000000000000000000 : ℝ) ≤ ((35540077721073597157/35550000000000000000 : ℝ)+2*(4065221609/2777343750000 : ℝ)*(697/6250 : ℝ))^(2151/512 : ℝ) := by
    rw [show (35540077721073597157/35550000000000000000 : ℝ)+2*(4065221609/2777343750000 : ℝ)*(697/6250 : ℝ)=(10000473578348183/10000000000000000 : ℝ) by norm_num, show 1+2*(4974337133169479/50000000000000000000 : ℝ)=(25004974337133169479/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15907269348725179/50000000000000000000 : ℝ)+(4974337133169479/50000000000000000000 : ℝ) ≤ ((35540077721073597157/35550000000000000000 : ℝ)+(4065221609/2777343750000 : ℝ)*((14707/100000 : ℝ)+(697/6250 : ℝ)))^(2151/512 : ℝ) := by
    rw [show (35540077721073597157/35550000000000000000 : ℝ)+(4065221609/2777343750000 : ℝ)*((14707/100000 : ℝ)+(697/6250 : ℝ))=(2000198785342827/2000000000000000 : ℝ) by norm_num, show 1+(15907269348725179/50000000000000000000 : ℝ)+(4974337133169479/50000000000000000000 : ℝ)=(25010440803240947329/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15907269348725179/50000000000000000000 : ℝ) ≤ ((35540077721073597157/35550000000000000000 : ℝ)+2*(4065221609/2777343750000 : ℝ)*(14707/100000 : ℝ))^(2151/512 : ℝ) := by
    rw [show (35540077721073597157/35550000000000000000 : ℝ)+2*(4065221609/2777343750000 : ℝ)*(14707/100000 : ℝ)=(10001514275080087/10000000000000000 : ℝ) by norm_num, show 1+2*(15907269348725179/50000000000000000000 : ℝ)=(25015907269348725179/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35540077721073597157/35550000000000000000 : ℝ)*(X 1 0+X 2 0)+(4065221609/2777343750000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (697/6250 : ℝ)) (hi := (14707/100000 : ℝ)) (c := (35540077721073597157/35550000000000000000 : ℝ)) (alpha := (4065221609/2777343750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35540077721073597157/35550000000000000000 : ℝ)*(X 0 1+X 2 1)+(4065221609/2777343750000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (697/6250 : ℝ)) (hi := (14707/100000 : ℝ)) (c := (35540077721073597157/35550000000000000000 : ℝ)) (alpha := (4065221609/2777343750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35540077721073597157/35550000000000000000 : ℝ)*(X 0 2+X 1 2)+(4065221609/2777343750000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2151/512 : ℝ)) (lo := (697/6250 : ℝ)) (hi := (14707/100000 : ℝ)) (c := (35540077721073597157/35550000000000000000 : ℝ)) (alpha := (4065221609/2777343750000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1875932299/10000000000 : ℝ)*X 0 0+(2694949761/5000000000 : ℝ)*X 0 1+(673737401/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2642588939/5000000000 : ℝ)*X 1 0+(-1009704961/5000000000 : ℝ)*X 1 1+(2694949667/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5285177467/10000000000 : ℝ)*X 2 0+(5389899721/10000000000 : ℝ)*X 2 1+(-40388199/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2237264111/5000000000 : ℝ)*X 0 0+(1064040921/2500000000 : ℝ)*X 0 1+(4256163971/10000000000 : ℝ)*X 0 2+(2237264111/5000000000 : ℝ)*X 1 0+(1064040921/2500000000 : ℝ)*X 1 1+(4256163971/10000000000 : ℝ)*X 1 2+(2237264111/5000000000 : ℝ)*X 2 0+(1064040921/2500000000 : ℝ)*X 2 1+(4256163971/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1106519557/5000000000 : ℝ)*X 0 0+(1316236871/2500000000 : ℝ)*X 0 1+(5264947979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5372937127/10000000000 : ℝ)*X 1 0+(-517389067/2500000000 : ℝ)*X 1 1+(5264948241/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5372938097/10000000000 : ℝ)*X 2 0+(2632473779/5000000000 : ℝ)*X 2 1+(-16556447/80000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4177265663/10000000000 : ℝ)*X 0 0+(4404742211/10000000000 : ℝ)*X 0 1+(4404740877/10000000000 : ℝ)*X 0 2+(4177265663/10000000000 : ℝ)*X 1 0+(4404742211/10000000000 : ℝ)*X 1 1+(4404740877/10000000000 : ℝ)*X 1 2+(4177265663/10000000000 : ℝ)*X 2 0+(4404742211/10000000000 : ℝ)*X 2 1+(4404740877/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2142242951/10000000000 : ℝ)*X 0 0+(129473053/250000000 : ℝ)*X 0 1+(1350980097/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5275325199/10000000000 : ℝ)*X 1 0+(-100682589/500000000 : ℝ)*X 1 1+(1350979787/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5275325839/10000000000 : ℝ)*X 2 0+(5403918941/10000000000 : ℝ)*X 2 1+(-2013651197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((140853829/312500000 : ℝ)*X 0 0+(4239478897/10000000000 : ℝ)*X 0 1+(169579181/400000000 : ℝ)*X 0 2+(140853829/312500000 : ℝ)*X 1 0+(4239478897/10000000000 : ℝ)*X 1 1+(169579181/400000000 : ℝ)*X 1 2+(140853829/312500000 : ℝ)*X 2 0+(4239478897/10000000000 : ℝ)*X 2 1+(169579181/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1947062137/10000000000 : ℝ)*X 0 0+(2736860773/5000000000 : ℝ)*X 0 1+(525387743/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5380710507/10000000000 : ℝ)*X 1 0+(-2073894989/10000000000 : ℝ)*X 1 1+(5253877627/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5380710249/10000000000 : ℝ)*X 2 0+(164183673/312500000 : ℝ)*X 2 1+(-1036947729/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4150480851/10000000000 : ℝ)*X 0 0+(1104473691/2500000000 : ℝ)*X 0 1+(2208947291/5000000000 : ℝ)*X 0 2+(4150480851/10000000000 : ℝ)*X 1 0+(1104473691/2500000000 : ℝ)*X 1 1+(2208947291/5000000000 : ℝ)*X 1 2+(4150480851/10000000000 : ℝ)*X 2 0+(1104473691/2500000000 : ℝ)*X 2 1+(2208947291/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1343_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-7857/12500 : ℝ) ≤ (-186202650896996543526301892227051/296250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74070007/100000000000000 : ℝ)*(upper1) + (169616121/50000000000000 : ℝ)*(lower2) + (798907/10000000000000 : ℝ)*(upper4) + (1460852509444943/50000000000000 : ℝ)*(major0) + (1460852509444943/50000000000000 : ℝ)*(major1) + (1460852509444943/50000000000000 : ℝ)*(major2) + (1715288611/100000000000000 : ℝ)*(sp3) + (397656066388109/10000000000000 : ℝ)*(sp4) + (397645626846621/10000000000000 : ℝ)*(sp5) + (1988252897093411/50000000000000 : ℝ)*(sp6) + (471948638178593/25000000000000 : ℝ)*(sp7) + (4177726577/100000000000000 : ℝ)*(sp8) + (54286570729/50000000000000 : ℝ)*(sp13) + (29523710423/50000000000000 : ℝ)*(sp14) + (1887796268002983/100000000000000 : ℝ)*(f.failure) + (3976564841607667/100000000000000 : ℝ)*(f.sum) + (192942887513947/17775000000000000000000000000 : ℝ)*base65 + (10973631410586427051/1777500000000000000000000000000000 : ℝ)*base67 + (6913648456276072949/1777500000000000000000000000000000 : ℝ)*base70 + (37927915255791427051/1777500000000000000000000000000000 : ℝ)*base71 + (17307140596811/8887500000000000000000000000 : ℝ)*base73 + (2235673353001072949/1777500000000000000000000000000000 : ℝ)*base76 + (2314404270711427051/1777500000000000000000000000000000 : ℝ)*base77 + (1705150357956427051/1777500000000000000000000000000000 : ℝ)*base79 + (89693306942047/17775000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (20510779/5000000000000000000000 : ℝ)*base89 + (20510779/5000000000000000000000 : ℝ)*base91 + (20510779/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (58943/100000 : ℝ) ≤ (3492525773484287115007206973/5925000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1528507/4000000000000 : ℝ)*(lower1) + (8011971/10000000000000 : ℝ)*(upper2) + (11855517/100000000000000 : ℝ)*(upper3) + (31022991/100000000000000 : ℝ)*(lower5) + (46725574440841/1562500000000 : ℝ)*(major0) + (46725574440841/1562500000000 : ℝ)*(major1) + (46725574440841/1562500000000 : ℝ)*(major2) + (4029018710359089/100000000000000 : ℝ)*(sp0) + (1007254801946329/25000000000000 : ℝ)*(sp1) + (201450473422733/5000000000000 : ℝ)*(sp2) + (38644102258663/2000000000000 : ℝ)*(sp3) + (304354083/3125000000000 : ℝ)*(sp6) + (680150897/100000000000000 : ℝ)*(sp7) + (497426227/100000000000000 : ℝ)*(sp8) + (1932205793084047/100000000000000 : ℝ)*(f.failure) + (1007254801946329/25000000000000 : ℝ)*(f.sum) + (75045780349123/17775000000000000000000000000 : ℝ)*base65 + (294265044872669/27773437500000000000000000000000 : ℝ)*base68 + (145716582935756647/13886718750000000000000000000000 : ℝ)*base70 + (60490420629243353/13886718750000000000000000000000 : ℝ)*base71 + (25281918633677/17775000000000000000000000000 : ℝ)*base74 + (55607250947526761/6943359375000000000000000000000 : ℝ)*base76 + (31987240829816989/6943359375000000000000000000000 : ℝ)*base77 + (43190567036535739/6943359375000000000000000000000 : ℝ)*base79 + (161199376949777/17775000000000000000000000000 : ℝ)*base82 + (3140611/5000000000000000000000 : ℝ)*base89 + (3140611/5000000000000000000000 : ℝ)*base91 + (3140611/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1999/2500 : ℝ) ≤ (947557993153634717377972559/1185000000000000000000000000 : ℝ) := by norm_num
    linear_combination (73741817/25000000000000 : ℝ)*(upper0) + (45062569/100000000000000 : ℝ)*(lower3) + (37520231/10000000000000 : ℝ)*(upper4) + (165126433854397/5000000000000 : ℝ)*(major0) + (165126433854397/5000000000000 : ℝ)*(major1) + (165126433854397/5000000000000 : ℝ)*(major2) + (39798170113/12500000000000 : ℝ)*(sp1) + (205268737149/50000000000000 : ℝ)*(sp2) + (171435880897/100000000000000 : ℝ)*(sp3) + (2141682937/3125000000000 : ℝ)*(sp4) + (2222238689970073/50000000000000 : ℝ)*(sp8) + (2222113764216613/50000000000000 : ℝ)*(sp9) + (555516922039979/12500000000000 : ℝ)*(sp10) + (2133685771219451/100000000000000 : ℝ)*(sp11) + (533464301775087/25000000000000 : ℝ)*(f.failure) + (444454591379413/10000000000000 : ℝ)*(f.sum) + (493273199393/111093750000000000000000000 : ℝ)*base65 + (1059219112804700671/177750000000000000000000000000000 : ℝ)*base68 + (563158301085950671/177750000000000000000000000000000 : ℝ)*base70 + (638713752258549329/177750000000000000000000000000000 : ℝ)*base71 + (88527888088709/3555000000000000000000000000 : ℝ)*base74 + (1080242720685950671/177750000000000000000000000000000 : ℝ)*base76 + (214702053906549329/177750000000000000000000000000000 : ℝ)*base77 + (83001855011799329/177750000000000000000000000000000 : ℝ)*base79 + (6846183539543/1777500000000000000000000000 : ℝ)*base81 + (5484131/1250000000000000000000 : ℝ)*base89 + (5484131/1250000000000000000000 : ℝ)*base91 + (5484131/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-21089/25000 : ℝ) ≤ (-499794445773938472020424324679817/592500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7240011/10000000000000 : ℝ)*(lower0) + (10118253/50000000000000 : ℝ)*(upper1) + (26846223/25000000000000 : ℝ)*(upper3) + (211534611/100000000000000 : ℝ)*(lower4) + (1669496016970309/50000000000000 : ℝ)*(major0) + (1669496016970309/50000000000000 : ℝ)*(major1) + (3338992033940619/100000000000000 : ℝ)*(major2) + (1111373443/50000000000000 : ℝ)*(sp4) + (121174348671/100000000000000 : ℝ)*(sp6) + (265072491/390625000000 : ℝ)*(sp7) + (1137170615651427/25000000000000 : ℝ)*(sp12) + (2274342342676297/50000000000000 : ℝ)*(sp13) + (4548563511003923/100000000000000 : ℝ)*(sp14) + (1078674677478409/50000000000000 : ℝ)*(sp15) + (1078708606757257/50000000000000 : ℝ)*(f.failure) + (2274342342676297/50000000000000 : ℝ)*(f.sum) + (45714314117831/8887500000000000000000000000 : ℝ)*base65 + (2231894277210211513/1777500000000000000000000000000000 : ℝ)*base67 + (24967399708711179817/3555000000000000000000000000000000 : ℝ)*base70 + (805255136699788487/1777500000000000000000000000000000 : ℝ)*base72 + (38211950758631/8887500000000000000000000000 : ℝ)*base73 + (6120213855931179817/3555000000000000000000000000000000 : ℝ)*base76 + (9375751948787388487/1777500000000000000000000000000000 : ℝ)*base78 + (3480611421177611513/1777500000000000000000000000000000 : ℝ)*base79 + (72959423338361/17775000000000000000000000000 : ℝ)*base81 + (13532341/2500000000000000000000 : ℝ)*base89 + (13532341/2500000000000000000000 : ℝ)*base91 + (11467659/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1343_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14707/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (697/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7857/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58943/100000 : ℝ) else (1999/2500 : ℝ) ≤ X j i ∧ X j i ≤ (21089/25000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1343_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1343_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7857/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58943/100000 : ℝ) else (1999/2500 : ℝ) ≤ X j i ∧ X j i ≤ (21089/25000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1343_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1343_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1343_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2151/512 : ℝ) ≤ p) (hpb : p ≤ (4303/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77384013/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3679/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1393/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(7857/12500 : ℝ) ≤ X j i ∧ X j i ≤ -(58943/100000 : ℝ) else (1999/2500 : ℝ) ≤ X j i ∧ X j i ≤ (21089/25000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1343_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
