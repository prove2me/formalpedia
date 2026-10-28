-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1237_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T16:17:19.38899+00:00
-- url     : https://prove2.me/submissions/0d7c82e1-944d-4db6-90aa-c0c07820e0b4

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
theorem support_rectangle_w1237_s3_0 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1059690273/5000000000 : ℝ)*x 0 + (542009657/1000000000 : ℝ)*x 1 + (52402337/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1059690273/5000000000 : ℝ)^4215 ≤ (3220532542381/25000000000000 : ℝ)^3191 := by
    have hnat : (1059690273 : ℕ)^4215*25000000000000^3191 ≤ 3220532542381^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1059690273 5000000000 3220532542381 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542009657/1000000000 : ℝ)^4215 ≤ (44529641979197/100000000000000 : ℝ)^3191 := by
    have hnat : (542009657 : ℕ)^4215*100000000000000^3191 ≤ 44529641979197^3191*1000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542009657 1000000000 44529641979197 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (52402337/100000000 : ℝ)^4215 ≤ (42588227838343/100000000000000 : ℝ)^3191 := by
    have hnat : (52402337 : ℕ)^4215*100000000000000^3191 ≤ 42588227838343^3191*100000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      52402337 100000000 42588227838343 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1059690273/5000000000 : ℝ), (542009657/1000000000 : ℝ), (52402337/100000000 : ℝ)] ![(3220532542381/25000000000000 : ℝ), (44529641979197/100000000000000 : ℝ), (42588227838343/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1059690273/5000000000 : ℝ)|^4215 ≤ (3220532542381/25000000000000 : ℝ)^3191
        have hw : |(-1059690273/5000000000 : ℝ)|=(1059690273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542009657/1000000000 : ℝ)|^4215 ≤ (44529641979197/100000000000000 : ℝ)^3191
        have hw : |(542009657/1000000000 : ℝ)|=(542009657/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(52402337/100000000 : ℝ)|^4215 ≤ (42588227838343/100000000000000 : ℝ)^3191
        have hw : |(52402337/100000000 : ℝ)|=(52402337/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s3_1 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351599977/10000000000 : ℝ)*x 0 + (-2211143979/10000000000 : ℝ)*x 1 + (2620116921/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351599977/10000000000 : ℝ)^4215 ≤ (43787823119477/100000000000000 : ℝ)^3191 := by
    have hnat : (5351599977 : ℕ)^4215*100000000000000^3191 ≤ 43787823119477^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351599977 10000000000 43787823119477 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2211143979/10000000000 : ℝ)^4215 ≤ (13623947506529/100000000000000 : ℝ)^3191 := by
    have hnat : (2211143979 : ℕ)^4215*100000000000000^3191 ≤ 13623947506529^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2211143979 10000000000 13623947506529 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620116921/5000000000 : ℝ)^4215 ≤ (2129411468137/5000000000000 : ℝ)^3191 := by
    have hnat : (2620116921 : ℕ)^4215*5000000000000^3191 ≤ 2129411468137^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620116921 5000000000 2129411468137 5000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351599977/10000000000 : ℝ), (-2211143979/10000000000 : ℝ), (2620116921/5000000000 : ℝ)] ![(43787823119477/100000000000000 : ℝ), (13623947506529/100000000000000 : ℝ), (2129411468137/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351599977/10000000000 : ℝ)|^4215 ≤ (43787823119477/100000000000000 : ℝ)^3191
        have hw : |(5351599977/10000000000 : ℝ)|=(5351599977/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2211143979/10000000000 : ℝ)|^4215 ≤ (13623947506529/100000000000000 : ℝ)^3191
        have hw : |(-2211143979/10000000000 : ℝ)|=(2211143979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620116921/5000000000 : ℝ)|^4215 ≤ (2129411468137/5000000000000 : ℝ)^3191
        have hw : |(2620116921/5000000000 : ℝ)|=(2620116921/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s3_2 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351599883/10000000000 : ℝ)*x 0 + (5240234263/10000000000 : ℝ)*x 1 + (-552785887/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351599883/10000000000 : ℝ)^4215 ≤ (2736738881471/6250000000000 : ℝ)^3191 := by
    have hnat : (5351599883 : ℕ)^4215*6250000000000^3191 ≤ 2736738881471^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351599883 10000000000 2736738881471 6250000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5240234263/10000000000 : ℝ)^4215 ≤ (21294116941127/50000000000000 : ℝ)^3191 := by
    have hnat : (5240234263 : ℕ)^4215*50000000000000^3191 ≤ 21294116941127^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5240234263 10000000000 21294116941127 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552785887/2500000000 : ℝ)^4215 ≤ (851496499921/6250000000000 : ℝ)^3191 := by
    have hnat : (552785887 : ℕ)^4215*6250000000000^3191 ≤ 851496499921^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552785887 2500000000 851496499921 6250000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351599883/10000000000 : ℝ), (5240234263/10000000000 : ℝ), (-552785887/2500000000 : ℝ)] ![(2736738881471/6250000000000 : ℝ), (21294116941127/50000000000000 : ℝ), (851496499921/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351599883/10000000000 : ℝ)|^4215 ≤ (2736738881471/6250000000000 : ℝ)^3191
        have hw : |(5351599883/10000000000 : ℝ)|=(5351599883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5240234263/10000000000 : ℝ)|^4215 ≤ (21294116941127/50000000000000 : ℝ)^3191
        have hw : |(5240234263/10000000000 : ℝ)|=(5240234263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-552785887/2500000000 : ℝ)|^4215 ≤ (851496499921/6250000000000 : ℝ)^3191
        have hw : |(-552785887/2500000000 : ℝ)|=(552785887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s3_3 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4349736499/10000000000 : ℝ)*x 0 + (4171193809/10000000000 : ℝ)*x 1 + (907140957/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4349736499/10000000000 : ℝ)^4215 ≤ (33300042772603/100000000000000 : ℝ)^3191 := by
    have hnat : (4349736499 : ℕ)^4215*100000000000000^3191 ≤ 33300042772603^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349736499 10000000000 33300042772603 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171193809/10000000000 : ℝ)^4215 ≤ (7876639453549/25000000000000 : ℝ)^3191 := by
    have hnat : (4171193809 : ℕ)^4215*25000000000000^3191 ≤ 7876639453549^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171193809 10000000000 7876639453549 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (907140957/2000000000 : ℝ)^4215 ≤ (17596699700129/50000000000000 : ℝ)^3191 := by
    have hnat : (907140957 : ℕ)^4215*50000000000000^3191 ≤ 17596699700129^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      907140957 2000000000 17596699700129 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4349736499/10000000000 : ℝ), (4171193809/10000000000 : ℝ), (907140957/2000000000 : ℝ)] ![(33300042772603/100000000000000 : ℝ), (7876639453549/25000000000000 : ℝ), (17596699700129/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4349736499/10000000000 : ℝ)|^4215 ≤ (33300042772603/100000000000000 : ℝ)^3191
        have hw : |(4349736499/10000000000 : ℝ)|=(4349736499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171193809/10000000000 : ℝ)|^4215 ≤ (7876639453549/25000000000000 : ℝ)^3191
        have hw : |(4171193809/10000000000 : ℝ)|=(4171193809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(907140957/2000000000 : ℝ)|^4215 ≤ (17596699700129/50000000000000 : ℝ)^3191
        have hw : |(907140957/2000000000 : ℝ)|=(907140957/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s3_4 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2119394719/10000000000 : ℝ)*x 0 + (524088943/1000000000 : ℝ)*x 1 + (5419437391/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2119394719/10000000000 : ℝ)^4215 ≤ (6441121980767/50000000000000 : ℝ)^3191 := by
    have hnat : (2119394719 : ℕ)^4215*50000000000000^3191 ≤ 6441121980767^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2119394719 10000000000 6441121980767 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (524088943/1000000000 : ℝ)^4215 ≤ (42595267365043/100000000000000 : ℝ)^3191 := by
    have hnat : (524088943 : ℕ)^4215*100000000000000^3191 ≤ 42595267365043^3191*1000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524088943 1000000000 42595267365043 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419437391/10000000000 : ℝ)^4215 ≤ (11130622164023/25000000000000 : ℝ)^3191 := by
    have hnat : (5419437391 : ℕ)^4215*25000000000000^3191 ≤ 11130622164023^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419437391 10000000000 11130622164023 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2119394719/10000000000 : ℝ), (524088943/1000000000 : ℝ), (5419437391/10000000000 : ℝ)] ![(6441121980767/50000000000000 : ℝ), (42595267365043/100000000000000 : ℝ), (11130622164023/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2119394719/10000000000 : ℝ)|^4215 ≤ (6441121980767/50000000000000 : ℝ)^3191
        have hw : |(-2119394719/10000000000 : ℝ)|=(2119394719/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(524088943/1000000000 : ℝ)|^4215 ≤ (42595267365043/100000000000000 : ℝ)^3191
        have hw : |(524088943/1000000000 : ℝ)|=(524088943/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419437391/10000000000 : ℝ)|^4215 ≤ (11130622164023/25000000000000 : ℝ)^3191
        have hw : |(5419437391/10000000000 : ℝ)|=(5419437391/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s3_5 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305727463/10000000000 : ℝ)*x 0 + (-2031941149/10000000000 : ℝ)*x 1 + (2709718677/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305727463/10000000000 : ℝ)^4215 ≤ (43292721727511/100000000000000 : ℝ)^3191 := by
    have hnat : (5305727463 : ℕ)^4215*100000000000000^3191 ≤ 43292721727511^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305727463 10000000000 43292721727511 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2031941149/10000000000 : ℝ)^4215 ≤ (3046197499907/25000000000000 : ℝ)^3191 := by
    have hnat : (2031941149 : ℕ)^4215*25000000000000^3191 ≤ 3046197499907^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2031941149 10000000000 3046197499907 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2709718677/5000000000 : ℝ)^4215 ≤ (44522488254581/100000000000000 : ℝ)^3191 := by
    have hnat : (2709718677 : ℕ)^4215*100000000000000^3191 ≤ 44522488254581^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709718677 5000000000 44522488254581 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305727463/10000000000 : ℝ), (-2031941149/10000000000 : ℝ), (2709718677/5000000000 : ℝ)] ![(43292721727511/100000000000000 : ℝ), (3046197499907/25000000000000 : ℝ), (44522488254581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305727463/10000000000 : ℝ)|^4215 ≤ (43292721727511/100000000000000 : ℝ)^3191
        have hw : |(5305727463/10000000000 : ℝ)|=(5305727463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2031941149/10000000000 : ℝ)|^4215 ≤ (3046197499907/25000000000000 : ℝ)^3191
        have hw : |(-2031941149/10000000000 : ℝ)|=(2031941149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2709718677/5000000000 : ℝ)|^4215 ≤ (44522488254581/100000000000000 : ℝ)^3191
        have hw : |(2709718677/5000000000 : ℝ)|=(2709718677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s3_6 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305728231/10000000000 : ℝ)*x 0 + (5419436923/10000000000 : ℝ)*x 1 + (-253992587/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305728231/10000000000 : ℝ)^4215 ≤ (5411591250633/12500000000000 : ℝ)^3191 := by
    have hnat : (5305728231 : ℕ)^4215*12500000000000^3191 ≤ 5411591250633^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305728231 10000000000 5411591250633 12500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419436923/10000000000 : ℝ)^4215 ≤ (44522483577517/100000000000000 : ℝ)^3191 := by
    have hnat : (5419436923 : ℕ)^4215*100000000000000^3191 ≤ 44522483577517^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419436923 10000000000 44522483577517 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253992587/1250000000 : ℝ)^4215 ≤ (6092393205717/50000000000000 : ℝ)^3191 := by
    have hnat : (253992587 : ℕ)^4215*50000000000000^3191 ≤ 6092393205717^3191*1250000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253992587 1250000000 6092393205717 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305728231/10000000000 : ℝ), (5419436923/10000000000 : ℝ), (-253992587/1250000000 : ℝ)] ![(5411591250633/12500000000000 : ℝ), (44522483577517/100000000000000 : ℝ), (6092393205717/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305728231/10000000000 : ℝ)|^4215 ≤ (5411591250633/12500000000000 : ℝ)^3191
        have hw : |(5305728231/10000000000 : ℝ)|=(5305728231/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419436923/10000000000 : ℝ)|^4215 ≤ (44522483577517/100000000000000 : ℝ)^3191
        have hw : |(5419436923/10000000000 : ℝ)|=(5419436923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-253992587/1250000000 : ℝ)|^4215 ≤ (6092393205717/50000000000000 : ℝ)^3191
        have hw : |(-253992587/1250000000 : ℝ)|=(253992587/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s3_7 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1087441381/2500000000 : ℝ)*x 0 + (2267188043/5000000000 : ℝ)*x 1 + (4172529163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1087441381/2500000000 : ℝ)^4215 ≤ (33300336284231/100000000000000 : ℝ)^3191 := by
    have hnat : (1087441381 : ℕ)^4215*100000000000000^3191 ≤ 33300336284231^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1087441381 2500000000 33300336284231 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2267188043/5000000000 : ℝ)^4215 ≤ (35179782024979/100000000000000 : ℝ)^3191 := by
    have hnat : (2267188043 : ℕ)^4215*100000000000000^3191 ≤ 35179782024979^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2267188043 5000000000 35179782024979 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172529163/10000000000 : ℝ)^4215 ≤ (31519881674817/100000000000000 : ℝ)^3191 := by
    have hnat : (4172529163 : ℕ)^4215*100000000000000^3191 ≤ 31519881674817^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172529163 10000000000 31519881674817 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1087441381/2500000000 : ℝ), (2267188043/5000000000 : ℝ), (4172529163/10000000000 : ℝ)] ![(33300336284231/100000000000000 : ℝ), (35179782024979/100000000000000 : ℝ), (31519881674817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1087441381/2500000000 : ℝ)|^4215 ≤ (33300336284231/100000000000000 : ℝ)^3191
        have hw : |(1087441381/2500000000 : ℝ)|=(1087441381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2267188043/5000000000 : ℝ)|^4215 ≤ (35179782024979/100000000000000 : ℝ)^3191
        have hw : |(2267188043/5000000000 : ℝ)|=(2267188043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172529163/10000000000 : ℝ)|^4215 ≤ (31519881674817/100000000000000 : ℝ)^3191
        have hw : |(4172529163/10000000000 : ℝ)|=(4172529163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1237_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4059/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9479/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5449/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2941/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4059/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9479/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4059/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9479/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4059/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9479/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4059/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9479/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4059/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9479/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4059/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9479/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9479/100000 : ℝ) ^ (8429/2048 : ℝ) ≤ (6146647875317613/100000000000000000000 : ℝ) := by
    have hpowers : (9479/100000 : ℝ)^8429 ≤ (6146647875317613/100000000000000000000 : ℝ)^2048 := by
      have hnat : (9479 : ℕ)^8429*100000000000000000000^2048 ≤ 6146647875317613^2048*100000^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9479 100000 6146647875317613 100000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9479/100000 : ℝ)) (X := (6146647875317613/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (4059/25000 : ℝ) ^ (8429/2048 : ℝ) ≤ (11261097117011901/20000000000000000000 : ℝ) := by
    have hpowers : (4059/25000 : ℝ)^8429 ≤ (11261097117011901/20000000000000000000 : ℝ)^2048 := by
      have hnat : (4059 : ℕ)^8429*20000000000000000000^2048 ≤ 11261097117011901^2048*25000^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4059 25000 11261097117011901 20000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4059/25000 : ℝ)) (X := (11261097117011901/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006146647875317613/50000000000000000000 : ℝ) ≤ (625018667322831/625000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (50006146647875317613/50000000000000000000 : ℝ)^2048 ≤ (625018667322831/625000000000000 : ℝ)^8429 := by
      have hnat : (50006146647875317613 : ℕ)^2048*625000000000000^8429 ≤ 625018667322831^8429*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006146647875317613 50000000000000000000 625018667322831 625000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625018667322831/625000000000000 : ℝ)) (X := (50006146647875317613/50000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (50031226066730188559/50000000000000000000 : ℝ) ≤ (10001517045267217/10000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (50031226066730188559/50000000000000000000 : ℝ)^2048 ≤ (10001517045267217/10000000000000000 : ℝ)^8429 := by
      have hnat : (50031226066730188559 : ℕ)^2048*10000000000000000^8429 ≤ 10001517045267217^8429*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50031226066730188559 50000000000000000000 10001517045267217 10000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001517045267217/10000000000000000 : ℝ)) (X := (50031226066730188559/50000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (10011261097117011901/10000000000000000000 : ℝ) ≤ (5001367706684569/5000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (10011261097117011901/10000000000000000000 : ℝ)^2048 ≤ (5001367706684569/5000000000000000 : ℝ)^8429 := by
      have hnat : (10011261097117011901 : ℕ)^2048*5000000000000000^8429 ≤ 5001367706684569^8429*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10011261097117011901 10000000000000000000 5001367706684569 5000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001367706684569/5000000000000000 : ℝ)) (X := (10011261097117011901/10000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6146647875317613/100000000000000000000 : ℝ) ≤ ((33774460169564843377/33785000000000000000 : ℝ)+2*(1218368101921/675700000000000 : ℝ)*(9479/100000 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (33774460169564843377/33785000000000000000 : ℝ)+2*(1218368101921/675700000000000 : ℝ)*(9479/100000 : ℝ)=(625018667322831/625000000000000 : ℝ) by norm_num, show 1+2*(6146647875317613/100000000000000000000 : ℝ)=(50006146647875317613/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(11261097117011901/20000000000000000000 : ℝ)+(6146647875317613/100000000000000000000 : ℝ) ≤ ((33774460169564843377/33785000000000000000 : ℝ)+(1218368101921/675700000000000 : ℝ)*((4059/25000 : ℝ)+(9479/100000 : ℝ)))^(8429/2048 : ℝ) := by
    rw [show (33774460169564843377/33785000000000000000 : ℝ)+(1218368101921/675700000000000 : ℝ)*((4059/25000 : ℝ)+(9479/100000 : ℝ))=(10001517045267217/10000000000000000 : ℝ) by norm_num, show 1+(11261097117011901/20000000000000000000 : ℝ)+(6146647875317613/100000000000000000000 : ℝ)=(50031226066730188559/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(11261097117011901/20000000000000000000 : ℝ) ≤ ((33774460169564843377/33785000000000000000 : ℝ)+2*(1218368101921/675700000000000 : ℝ)*(4059/25000 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (33774460169564843377/33785000000000000000 : ℝ)+2*(1218368101921/675700000000000 : ℝ)*(4059/25000 : ℝ)=(5001367706684569/5000000000000000 : ℝ) by norm_num, show 1+2*(11261097117011901/20000000000000000000 : ℝ)=(10011261097117011901/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (33774460169564843377/33785000000000000000 : ℝ)*(X 1 0+X 2 0)+(1218368101921/675700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (9479/100000 : ℝ)) (hi := (4059/25000 : ℝ)) (c := (33774460169564843377/33785000000000000000 : ℝ)) (alpha := (1218368101921/675700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (33774460169564843377/33785000000000000000 : ℝ)*(X 0 1+X 2 1)+(1218368101921/675700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (9479/100000 : ℝ)) (hi := (4059/25000 : ℝ)) (c := (33774460169564843377/33785000000000000000 : ℝ)) (alpha := (1218368101921/675700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (33774460169564843377/33785000000000000000 : ℝ)*(X 0 2+X 1 2)+(1218368101921/675700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (9479/100000 : ℝ)) (hi := (4059/25000 : ℝ)) (c := (33774460169564843377/33785000000000000000 : ℝ)) (alpha := (1218368101921/675700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1059690273/5000000000 : ℝ)*X 0 0+(542009657/1000000000 : ℝ)*X 0 1+(52402337/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351599977/10000000000 : ℝ)*X 1 0+(-2211143979/10000000000 : ℝ)*X 1 1+(2620116921/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351599883/10000000000 : ℝ)*X 2 0+(5240234263/10000000000 : ℝ)*X 2 1+(-552785887/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4349736499/10000000000 : ℝ)*X 0 0+(4171193809/10000000000 : ℝ)*X 0 1+(907140957/2000000000 : ℝ)*X 0 2+(4349736499/10000000000 : ℝ)*X 1 0+(4171193809/10000000000 : ℝ)*X 1 1+(907140957/2000000000 : ℝ)*X 1 2+(4349736499/10000000000 : ℝ)*X 2 0+(4171193809/10000000000 : ℝ)*X 2 1+(907140957/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2119394719/10000000000 : ℝ)*X 0 0+(524088943/1000000000 : ℝ)*X 0 1+(5419437391/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305727463/10000000000 : ℝ)*X 1 0+(-2031941149/10000000000 : ℝ)*X 1 1+(2709718677/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305728231/10000000000 : ℝ)*X 2 0+(5419436923/10000000000 : ℝ)*X 2 1+(-253992587/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1087441381/2500000000 : ℝ)*X 0 0+(2267188043/5000000000 : ℝ)*X 0 1+(4172529163/10000000000 : ℝ)*X 0 2+(1087441381/2500000000 : ℝ)*X 1 0+(2267188043/5000000000 : ℝ)*X 1 1+(4172529163/10000000000 : ℝ)*X 1 2+(1087441381/2500000000 : ℝ)*X 2 0+(2267188043/5000000000 : ℝ)*X 2 1+(4172529163/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1059417364920232932840173211/105578125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (959647/62500000000 : ℝ)*(base19) + (67092859/6250000000000 : ℝ)*(base23) + (39059627/20000000000000 : ℝ)*(lower2) + (199971809/100000000000000 : ℝ)*(upper5) + (259478203771569/6250000000000 : ℝ)*(major0) + (259478203771569/6250000000000 : ℝ)*(major1) + (259478203771569/6250000000000 : ℝ)*(major2) + (2779912859029153/50000000000000 : ℝ)*(sp0) + (5559869370387489/100000000000000 : ℝ)*(sp1) + (5559869907336339/100000000000000 : ℝ)*(sp2) + (548683446869877/20000000000000 : ℝ)*(sp3) + (45262763777/100000000000000 : ℝ)*(sp4) + (14999879/20000000000000 : ℝ)*(sp5) + (2794207479/20000000000000 : ℝ)*(sp7) + (137171560269339/5000000000000 : ℝ)*(f.failure) + (5559870980822083/100000000000000 : ℝ)*(f.sum) + (45883395269331/8446250000000000000000000000 : ℝ)*base65 + (2518899924232217263/211156250000000000000000000000000 : ℝ)*base67 + (1429909148495842263/211156250000000000000000000000000 : ℝ)*base69 + (1643805833185782737/211156250000000000000000000000000 : ℝ)*base72 + (98572904596319/33785000000000000000000000000 : ℝ)*base73 + (377864028869063987/211156250000000000000000000000000 : ℝ)*base76 + (2101963363747248513/211156250000000000000000000000000 : ℝ)*base77 + (1290816097618498513/211156250000000000000000000000000 : ℝ)*base79 + (2717934861477/16892500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (4025193/500000000000000000000 : ℝ)*base90 + (4025193/500000000000000000000 : ℝ)*base92 + (4025193/500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2464703539134607012363450527/422312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (44125509/12500000000000 : ℝ)*(base23) + (3213303/1250000000000 : ℝ)*(lower2) + (7074507/100000000000000 : ℝ)*(upper4) + (25041193/20000000000000 : ℝ)*(upper5) + (1045544894529317/25000000000000 : ℝ)*(major0) + (1045544894529317/25000000000000 : ℝ)*(major1) + (1045544894529317/25000000000000 : ℝ)*(major2) + (144547749/12500000000000 : ℝ)*(sp0) + (2321168929/50000000000000 : ℝ)*(sp2) + (828358433/100000000000000 : ℝ)*(sp3) + (2800376670044659/50000000000000 : ℝ)*(sp4) + (560075449647131/10000000000000 : ℝ)*(sp5) + (280037475056469/5000000000000 : ℝ)*(sp6) + (2763603636864521/100000000000000 : ℝ)*(sp7) + (1381802232611477/50000000000000 : ℝ)*(f.failure) + (560075449647131/10000000000000 : ℝ)*(f.sum) + (541476064345183/33785000000000000000000000000 : ℝ)*base65 + (15244566383641241491/844625000000000000000000000000000 : ℝ)*base68 + (7265466040795116491/844625000000000000000000000000000 : ℝ)*base70 + (16577656609268008509/844625000000000000000000000000000 : ℝ)*base71 + (110161249023877/33785000000000000000000000000 : ℝ)*base74 + (11322110387234366491/844625000000000000000000000000000 : ℝ)*base76 + (98844758262008509/844625000000000000000000000000000 : ℝ)*base77 + (11591267820640991491/844625000000000000000000000000000 : ℝ)*base80 + (1733355635489/4223125000000000000000000000 : ℝ)*base82 + (5245401/5000000000000000000000 : ℝ)*base89 + (5245401/5000000000000000000000 : ℝ)*base91 + (5245401/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1237_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4059/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9479/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5449/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1237_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1237_s4_0 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121705331/10000000000 : ℝ)*x 0 + (2698847651/5000000000 : ℝ)*x 1 + (2630555761/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121705331/10000000000 : ℝ)^4215 ≤ (12900798639263/100000000000000 : ℝ)^3191 := by
    have hnat : (2121705331 : ℕ)^4215*100000000000000^3191 ≤ 12900798639263^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121705331 10000000000 12900798639263 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2698847651/5000000000 : ℝ)^4215 ≤ (44286703007143/100000000000000 : ℝ)^3191 := by
    have hnat : (2698847651 : ℕ)^4215*100000000000000^3191 ≤ 44286703007143^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698847651 5000000000 44286703007143 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630555761/5000000000 : ℝ)^4215 ≤ (42812498346479/100000000000000 : ℝ)^3191 := by
    have hnat : (2630555761 : ℕ)^4215*100000000000000^3191 ≤ 42812498346479^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630555761 5000000000 42812498346479 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121705331/10000000000 : ℝ), (2698847651/5000000000 : ℝ), (2630555761/5000000000 : ℝ)] ![(12900798639263/100000000000000 : ℝ), (44286703007143/100000000000000 : ℝ), (42812498346479/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121705331/10000000000 : ℝ)|^4215 ≤ (12900798639263/100000000000000 : ℝ)^3191
        have hw : |(-2121705331/10000000000 : ℝ)|=(2121705331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2698847651/5000000000 : ℝ)|^4215 ≤ (44286703007143/100000000000000 : ℝ)^3191
        have hw : |(2698847651/5000000000 : ℝ)|=(2698847651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630555761/5000000000 : ℝ)|^4215 ≤ (42812498346479/100000000000000 : ℝ)^3191
        have hw : |(2630555761/5000000000 : ℝ)|=(2630555761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s4_1 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668244347/1250000000 : ℝ)*x 0 + (-109552709/500000000 : ℝ)*x 1 + (2630555759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668244347/1250000000 : ℝ)^4215 ≤ (8745364159489/20000000000000 : ℝ)^3191 := by
    have hnat : (668244347 : ℕ)^4215*20000000000000^3191 ≤ 8745364159489^3191*1250000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668244347 1250000000 8745364159489 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (109552709/500000000 : ℝ)^4215 ≤ (2692136176371/20000000000000 : ℝ)^3191 := by
    have hnat : (109552709 : ℕ)^4215*20000000000000^3191 ≤ 2692136176371^3191*500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      109552709 500000000 2692136176371 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2630555759/5000000000 : ℝ)^4215 ≤ (10703124575871/25000000000000 : ℝ)^3191 := by
    have hnat : (2630555759 : ℕ)^4215*25000000000000^3191 ≤ 10703124575871^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2630555759 5000000000 10703124575871 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668244347/1250000000 : ℝ), (-109552709/500000000 : ℝ), (2630555759/5000000000 : ℝ)] ![(8745364159489/20000000000000 : ℝ), (2692136176371/20000000000000 : ℝ), (10703124575871/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668244347/1250000000 : ℝ)|^4215 ≤ (8745364159489/20000000000000 : ℝ)^3191
        have hw : |(668244347/1250000000 : ℝ)|=(668244347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-109552709/500000000 : ℝ)|^4215 ≤ (2692136176371/20000000000000 : ℝ)^3191
        have hw : |(-109552709/500000000 : ℝ)|=(109552709/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2630555759/5000000000 : ℝ)|^4215 ≤ (10703124575871/25000000000000 : ℝ)^3191
        have hw : |(2630555759/5000000000 : ℝ)|=(2630555759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s4_2 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668244347/1250000000 : ℝ)*x 0 + (263055577/500000000 : ℝ)*x 1 + (-273881769/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668244347/1250000000 : ℝ)^4215 ≤ (8745364159489/20000000000000 : ℝ)^3191 := by
    have hnat : (668244347 : ℕ)^4215*20000000000000^3191 ≤ 8745364159489^3191*1250000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668244347 1250000000 8745364159489 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (263055577/500000000 : ℝ)^4215 ≤ (42812498539959/100000000000000 : ℝ)^3191 := by
    have hnat : (263055577 : ℕ)^4215*100000000000000^3191 ≤ 42812498539959^3191*500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      263055577 500000000 42812498539959 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (273881769/1250000000 : ℝ)^4215 ≤ (13460680654637/100000000000000 : ℝ)^3191 := by
    have hnat : (273881769 : ℕ)^4215*100000000000000^3191 ≤ 13460680654637^3191*1250000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      273881769 1250000000 13460680654637 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668244347/1250000000 : ℝ), (263055577/500000000 : ℝ), (-273881769/1250000000 : ℝ)] ![(8745364159489/20000000000000 : ℝ), (42812498539959/100000000000000 : ℝ), (13460680654637/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668244347/1250000000 : ℝ)|^4215 ≤ (8745364159489/20000000000000 : ℝ)^3191
        have hw : |(668244347/1250000000 : ℝ)|=(668244347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(263055577/500000000 : ℝ)|^4215 ≤ (42812498539959/100000000000000 : ℝ)^3191
        have hw : |(263055577/500000000 : ℝ)|=(263055577/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-273881769/1250000000 : ℝ)|^4215 ≤ (13460680654637/100000000000000 : ℝ)^3191
        have hw : |(-273881769/1250000000 : ℝ)|=(273881769/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s4_3 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4351129371/10000000000 : ℝ)*x 0 + (4214870247/10000000000 : ℝ)*x 1 + (449167257/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351129371/10000000000 : ℝ)^4215 ≤ (33314128722431/100000000000000 : ℝ)^3191 := by
    have hnat : (4351129371 : ℕ)^4215*100000000000000^3191 ≤ 33314128722431^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351129371 10000000000 33314128722431 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4214870247/10000000000 : ℝ)^4215 ≤ (15971529734341/50000000000000 : ℝ)^3191 := by
    have hnat : (4214870247 : ℕ)^4215*50000000000000^3191 ≤ 15971529734341^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4214870247 10000000000 15971529734341 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (449167257/1000000000 : ℝ)^4215 ≤ (34742811789639/100000000000000 : ℝ)^3191 := by
    have hnat : (449167257 : ℕ)^4215*100000000000000^3191 ≤ 34742811789639^3191*1000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449167257 1000000000 34742811789639 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351129371/10000000000 : ℝ), (4214870247/10000000000 : ℝ), (449167257/1000000000 : ℝ)] ![(33314128722431/100000000000000 : ℝ), (15971529734341/50000000000000 : ℝ), (34742811789639/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351129371/10000000000 : ℝ)|^4215 ≤ (33314128722431/100000000000000 : ℝ)^3191
        have hw : |(4351129371/10000000000 : ℝ)|=(4351129371/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4214870247/10000000000 : ℝ)|^4215 ≤ (15971529734341/50000000000000 : ℝ)^3191
        have hw : |(4214870247/10000000000 : ℝ)|=(4214870247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(449167257/1000000000 : ℝ)|^4215 ≤ (34742811789639/100000000000000 : ℝ)^3191
        have hw : |(449167257/1000000000 : ℝ)|=(449167257/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s4_4 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2121711573/10000000000 : ℝ)*x 0 + (1052298053/2000000000 : ℝ)*x 1 + (2698657513/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2121711573/10000000000 : ℝ)^4215 ≤ (161260609657/1250000000000 : ℝ)^3191 := by
    have hnat : (2121711573 : ℕ)^4215*1250000000000^3191 ≤ 161260609657^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2121711573 10000000000 161260609657 1250000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1052298053/2000000000 : ℝ)^4215 ≤ (8563313892483/20000000000000 : ℝ)^3191 := by
    have hnat : (1052298053 : ℕ)^4215*20000000000000^3191 ≤ 8563313892483^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052298053 2000000000 8563313892483 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698657513/5000000000 : ℝ)^4215 ≤ (22141290874743/50000000000000 : ℝ)^3191 := by
    have hnat : (2698657513 : ℕ)^4215*50000000000000^3191 ≤ 22141290874743^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698657513 5000000000 22141290874743 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2121711573/10000000000 : ℝ), (1052298053/2000000000 : ℝ), (2698657513/5000000000 : ℝ)] ![(161260609657/1250000000000 : ℝ), (8563313892483/20000000000000 : ℝ), (22141290874743/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2121711573/10000000000 : ℝ)|^4215 ≤ (161260609657/1250000000000 : ℝ)^3191
        have hw : |(-2121711573/10000000000 : ℝ)|=(2121711573/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1052298053/2000000000 : ℝ)|^4215 ≤ (8563313892483/20000000000000 : ℝ)^3191
        have hw : |(1052298053/2000000000 : ℝ)|=(1052298053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698657513/5000000000 : ℝ)|^4215 ≤ (22141290874743/50000000000000 : ℝ)^3191
        have hw : |(2698657513/5000000000 : ℝ)|=(2698657513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s4_5 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1062223683/2000000000 : ℝ)*x 0 + (-8026761/39062500 : ℝ)*x 1 + (269865747/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062223683/2000000000 : ℝ)^4215 ≤ (2167541760971/5000000000000 : ℝ)^3191 := by
    have hnat : (1062223683 : ℕ)^4215*5000000000000^3191 ≤ 2167541760971^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062223683 2000000000 2167541760971 5000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (8026761/39062500 : ℝ)^4215 ≤ (12366583952801/100000000000000 : ℝ)^3191 := by
    have hnat : (8026761 : ℕ)^4215*100000000000000^3191 ≤ 12366583952801^3191*39062500^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      8026761 39062500 12366583952801 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (269865747/500000000 : ℝ)^4215 ≤ (11070645204367/25000000000000 : ℝ)^3191 := by
    have hnat : (269865747 : ℕ)^4215*25000000000000^3191 ≤ 11070645204367^3191*500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269865747 500000000 11070645204367 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062223683/2000000000 : ℝ), (-8026761/39062500 : ℝ), (269865747/500000000 : ℝ)] ![(2167541760971/5000000000000 : ℝ), (12366583952801/100000000000000 : ℝ), (11070645204367/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062223683/2000000000 : ℝ)|^4215 ≤ (2167541760971/5000000000000 : ℝ)^3191
        have hw : |(1062223683/2000000000 : ℝ)|=(1062223683/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-8026761/39062500 : ℝ)|^4215 ≤ (12366583952801/100000000000000 : ℝ)^3191
        have hw : |(-8026761/39062500 : ℝ)|=(8026761/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(269865747/500000000 : ℝ)|^4215 ≤ (11070645204367/25000000000000 : ℝ)^3191
        have hw : |(269865747/500000000 : ℝ)|=(269865747/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s4_6 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1327779553/2500000000 : ℝ)*x 0 + (269865763/500000000 : ℝ)*x 1 + (-410970131/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1327779553/2500000000 : ℝ)^4215 ≤ (1083770825769/2500000000000 : ℝ)^3191 := by
    have hnat : (1327779553 : ℕ)^4215*2500000000000^3191 ≤ 1083770825769^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1327779553 2500000000 1083770825769 2500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (269865763/500000000 : ℝ)^4215 ≤ (44282584285443/100000000000000 : ℝ)^3191 := by
    have hnat : (269865763 : ℕ)^4215*100000000000000^3191 ≤ 44282584285443^3191*500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      269865763 500000000 44282584285443 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410970131/2000000000 : ℝ)^4215 ≤ (12366582672931/100000000000000 : ℝ)^3191 := by
    have hnat : (410970131 : ℕ)^4215*100000000000000^3191 ≤ 12366582672931^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410970131 2000000000 12366582672931 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1327779553/2500000000 : ℝ), (269865763/500000000 : ℝ), (-410970131/2000000000 : ℝ)] ![(1083770825769/2500000000000 : ℝ), (44282584285443/100000000000000 : ℝ), (12366582672931/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1327779553/2500000000 : ℝ)|^4215 ≤ (1083770825769/2500000000000 : ℝ)^3191
        have hw : |(1327779553/2500000000 : ℝ)|=(1327779553/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(269865763/500000000 : ℝ)|^4215 ≤ (44282584285443/100000000000000 : ℝ)^3191
        have hw : |(269865763/500000000 : ℝ)|=(269865763/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410970131/2000000000 : ℝ)|^4215 ≤ (12366582672931/100000000000000 : ℝ)^3191
        have hw : |(-410970131/2000000000 : ℝ)|=(410970131/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s4_7 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4351142061/10000000000 : ℝ)*x 0 + (4490905233/10000000000 : ℝ)*x 1 + (131738767/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351142061/10000000000 : ℝ)^4215 ≤ (33314257061553/100000000000000 : ℝ)^3191 := by
    have hnat : (4351142061 : ℕ)^4215*100000000000000^3191 ≤ 33314257061553^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351142061 10000000000 33314257061553 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490905233/10000000000 : ℝ)^4215 ≤ (8683743011401/25000000000000 : ℝ)^3191 := by
    have hnat : (4490905233 : ℕ)^4215*25000000000000^3191 ≤ 8683743011401^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490905233 10000000000 8683743011401 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131738767/312500000 : ℝ)^4215 ≤ (31950770882619/100000000000000 : ℝ)^3191 := by
    have hnat : (131738767 : ℕ)^4215*100000000000000^3191 ≤ 31950770882619^3191*312500000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131738767 312500000 31950770882619 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351142061/10000000000 : ℝ), (4490905233/10000000000 : ℝ), (131738767/312500000 : ℝ)] ![(33314257061553/100000000000000 : ℝ), (8683743011401/25000000000000 : ℝ), (31950770882619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351142061/10000000000 : ℝ)|^4215 ≤ (33314257061553/100000000000000 : ℝ)^3191
        have hw : |(4351142061/10000000000 : ℝ)|=(4351142061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490905233/10000000000 : ℝ)|^4215 ≤ (8683743011401/25000000000000 : ℝ)^3191
        have hw : |(4490905233/10000000000 : ℝ)|=(4490905233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131738767/312500000 : ℝ)|^4215 ≤ (31950770882619/100000000000000 : ℝ)^3191
        have hw : |(131738767/312500000 : ℝ)|=(131738767/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1237_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5449/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (709/6250 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3559/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5449/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5449/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5449/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2941/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5449/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5449/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2941/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5449/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5449/50000 : ℝ) ^ (8429/2048 : ℝ) ≤ (1364257790094201/12500000000000000000 : ℝ) := by
    have hpowers : (5449/50000 : ℝ)^8429 ≤ (1364257790094201/12500000000000000000 : ℝ)^2048 := by
      have hnat : (5449 : ℕ)^8429*12500000000000000000^2048 ≤ 1364257790094201^2048*50000^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5449 50000 1364257790094201 12500000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5449/50000 : ℝ)) (X := (1364257790094201/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2941/20000 : ℝ) ^ (8429/2048 : ℝ) ≤ (18727808567446231/50000000000000000000 : ℝ) := by
    have hpowers : (2941/20000 : ℝ)^8429 ≤ (18727808567446231/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2941 : ℕ)^8429*50000000000000000000^2048 ≤ 18727808567446231^2048*20000^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2941 20000 18727808567446231 50000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2941/20000 : ℝ)) (X := (18727808567446231/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251364257790094201/6250000000000000000 : ℝ) ≤ (5000265157825217/5000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (6251364257790094201/6250000000000000000 : ℝ)^2048 ≤ (5000265157825217/5000000000000000 : ℝ)^8429 := by
      have hnat : (6251364257790094201 : ℕ)^2048*5000000000000000^8429 ≤ 5000265157825217^8429*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251364257790094201 6250000000000000000 5000265157825217 5000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000265157825217/5000000000000000 : ℝ)) (X := (6251364257790094201/6250000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004836967945564607/10000000000000000000 : ℝ) ≤ (10001175026360519/10000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (10004836967945564607/10000000000000000000 : ℝ)^2048 ≤ (10001175026360519/10000000000000000 : ℝ)^8429 := by
      have hnat : (10004836967945564607 : ℕ)^2048*10000000000000000^8429 ≤ 10001175026360519^8429*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004836967945564607 10000000000000000000 10001175026360519 10000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001175026360519/10000000000000000 : ℝ)) (X := (10004836967945564607/10000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018727808567446231/25000000000000000000 : ℝ) ≤ (2500454934267651/2500000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (25018727808567446231/25000000000000000000 : ℝ)^2048 ≤ (2500454934267651/2500000000000000 : ℝ)^8429 := by
      have hnat : (25018727808567446231 : ℕ)^2048*2500000000000000^8429 ≤ 2500454934267651^8429*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018727808567446231 25000000000000000000 2500454934267651 2500000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500454934267651/2500000000000000 : ℝ)) (X := (25018727808567446231/25000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1364257790094201/12500000000000000000 : ℝ) ≤ ((19028983398522094789/19035000000000000000 : ℝ)+2*(128942142017/76140000000000 : ℝ)*(5449/50000 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (19028983398522094789/19035000000000000000 : ℝ)+2*(128942142017/76140000000000 : ℝ)*(5449/50000 : ℝ)=(5000265157825217/5000000000000000 : ℝ) by norm_num, show 1+2*(1364257790094201/12500000000000000000 : ℝ)=(6251364257790094201/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18727808567446231/50000000000000000000 : ℝ)+(1364257790094201/12500000000000000000 : ℝ) ≤ ((19028983398522094789/19035000000000000000 : ℝ)+(128942142017/76140000000000 : ℝ)*((2941/20000 : ℝ)+(5449/50000 : ℝ)))^(8429/2048 : ℝ) := by
    rw [show (19028983398522094789/19035000000000000000 : ℝ)+(128942142017/76140000000000 : ℝ)*((2941/20000 : ℝ)+(5449/50000 : ℝ))=(10001175026360519/10000000000000000 : ℝ) by norm_num, show 1+(18727808567446231/50000000000000000000 : ℝ)+(1364257790094201/12500000000000000000 : ℝ)=(10004836967945564607/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18727808567446231/50000000000000000000 : ℝ) ≤ ((19028983398522094789/19035000000000000000 : ℝ)+2*(128942142017/76140000000000 : ℝ)*(2941/20000 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (19028983398522094789/19035000000000000000 : ℝ)+2*(128942142017/76140000000000 : ℝ)*(2941/20000 : ℝ)=(2500454934267651/2500000000000000 : ℝ) by norm_num, show 1+2*(18727808567446231/50000000000000000000 : ℝ)=(25018727808567446231/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (19028983398522094789/19035000000000000000 : ℝ)*(X 1 0+X 2 0)+(128942142017/76140000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (5449/50000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (19028983398522094789/19035000000000000000 : ℝ)) (alpha := (128942142017/76140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (19028983398522094789/19035000000000000000 : ℝ)*(X 0 1+X 2 1)+(128942142017/76140000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (5449/50000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (19028983398522094789/19035000000000000000 : ℝ)) (alpha := (128942142017/76140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (19028983398522094789/19035000000000000000 : ℝ)*(X 0 2+X 1 2)+(128942142017/76140000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (5449/50000 : ℝ)) (hi := (2941/20000 : ℝ)) (c := (19028983398522094789/19035000000000000000 : ℝ)) (alpha := (128942142017/76140000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2121705331/10000000000 : ℝ)*X 0 0+(2698847651/5000000000 : ℝ)*X 0 1+(2630555761/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668244347/1250000000 : ℝ)*X 1 0+(-109552709/500000000 : ℝ)*X 1 1+(2630555759/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668244347/1250000000 : ℝ)*X 2 0+(263055577/500000000 : ℝ)*X 2 1+(-273881769/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351129371/10000000000 : ℝ)*X 0 0+(4214870247/10000000000 : ℝ)*X 0 1+(449167257/1000000000 : ℝ)*X 0 2+(4351129371/10000000000 : ℝ)*X 1 0+(4214870247/10000000000 : ℝ)*X 1 1+(449167257/1000000000 : ℝ)*X 1 2+(4351129371/10000000000 : ℝ)*X 2 0+(4214870247/10000000000 : ℝ)*X 2 1+(449167257/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2121711573/10000000000 : ℝ)*X 0 0+(1052298053/2000000000 : ℝ)*X 0 1+(2698657513/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062223683/2000000000 : ℝ)*X 1 0+(-8026761/39062500 : ℝ)*X 1 1+(269865747/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1327779553/2500000000 : ℝ)*X 2 0+(269865763/500000000 : ℝ)*X 2 1+(-410970131/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351142061/10000000000 : ℝ)*X 0 0+(4490905233/10000000000 : ℝ)*X 0 1+(131738767/312500000 : ℝ)*X 0 2+(4351142061/10000000000 : ℝ)*X 1 0+(4490905233/10000000000 : ℝ)*X 1 1+(131738767/312500000 : ℝ)*X 1 2+(4351142061/10000000000 : ℝ)*X 2 0+(4490905233/10000000000 : ℝ)*X 2 1+(131738767/312500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10829156099223321067676333/4230000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (239528183/50000000000000 : ℝ)*(base19) + (84537859/20000000000000 : ℝ)*(base23) + (1506679/5000000000000 : ℝ)*(lower2) + (40864801/100000000000000 : ℝ)*(upper3) + (20918711/50000000000000 : ℝ)*(upper5) + (218684768621109/4000000000000 : ℝ)*(major0) + (218684768621109/4000000000000 : ℝ)*(major1) + (218684768621109/4000000000000 : ℝ)*(major2) + (1464305221887883/20000000000000 : ℝ)*(sp0) + (1830384770689361/25000000000000 : ℝ)*(sp1) + (1464307827824903/20000000000000 : ℝ)*(sp2) + (1806346233406933/50000000000000 : ℝ)*(sp3) + (2690474879/20000000000000 : ℝ)*(sp4) + (3158545813/50000000000000 : ℝ)*(sp7) + (3612698783905491/100000000000000 : ℝ)*(f.failure) + (732153956181381/10000000000000 : ℝ)*(f.sum) + (1552014141893/1269000000000000000000000000 : ℝ)*base66 + (76022189827827889/8460000000000000000000000000000 : ℝ)*base67 + (74844369178287889/8460000000000000000000000000000 : ℝ)*base69 + (57212448795632111/8460000000000000000000000000000 : ℝ)*base72 + (238499804963/253800000000000000000000000 : ℝ)*base73 + (99378021539967889/8460000000000000000000000000000 : ℝ)*base75 + (162299024867792111/8460000000000000000000000000000 : ℝ)*base78 + (137471314424127889/8460000000000000000000000000000 : ℝ)*base79 + (6181450644979/1269000000000000000000000000 : ℝ)*base81 + (12904017/10000000000000000000000 : ℝ)*base90 + (12904017/10000000000000000000000 : ℝ)*base92 + (12904017/10000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (893140866457191459624789659/317250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (385188227/100000000000000 : ℝ)*(base19) + (66983377/100000000000000 : ℝ)*(base23) + (9298631/20000000000000 : ℝ)*(lower2) + (7123323/6250000000000 : ℝ)*(upper3) + (1983991/5000000000000 : ℝ)*(upper5) + (5497647998310277/100000000000000 : ℝ)*(major0) + (5497647998310277/100000000000000 : ℝ)*(major1) + (5497647998310277/100000000000000 : ℝ)*(major2) + (7735546957/100000000000000 : ℝ)*(sp2) + (455404633/20000000000000 : ℝ)*(sp3) + (7362423551755803/100000000000000 : ℝ)*(sp4) + (7362423166567577/100000000000000 : ℝ)*(sp5) + (736241574922547/10000000000000 : ℝ)*(sp6) + (3632870073999611/100000000000000 : ℝ)*(sp7) + (454109043877847/12500000000000 : ℝ)*(f.failure) + (7362423551755803/100000000000000 : ℝ)*(f.sum) + (1137003812573/190350000000000000000000000 : ℝ)*base66 + (4246299696263801149/634500000000000000000000000000000 : ℝ)*base68 + (5944611532429301149/634500000000000000000000000000000 : ℝ)*base70 + (13167594327029801149/634500000000000000000000000000000 : ℝ)*base72 + (12486346318907/3807000000000000000000000000 : ℝ)*base73 + (4451699338948301149/634500000000000000000000000000000 : ℝ)*base76 + (11778702897916301149/634500000000000000000000000000000 : ℝ)*base78 + (13734928794646301149/634500000000000000000000000000000 : ℝ)*base80 + (26757621446131/3807000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (21130211/1250000000000000000000 : ℝ)*base89 + (21130211/1250000000000000000000 : ℝ)*base91 + (21130211/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1237_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2941/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5449/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1237_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1237_s5_0 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-265270143/1250000000 : ℝ)*x 0 + (5392524721/10000000000 : ℝ)*x 1 + (5265982683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265270143/1250000000 : ℝ)^4215 ≤ (6452229837551/50000000000000 : ℝ)^3191 := by
    have hnat : (265270143 : ℕ)^4215*50000000000000^3191 ≤ 6452229837551^3191*1250000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265270143 1250000000 6452229837551 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392524721/10000000000 : ℝ)^4215 ≤ (2211533729621/5000000000000 : ℝ)^3191 := by
    have hnat : (5392524721 : ℕ)^4215*5000000000000^3191 ≤ 2211533729621^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392524721 10000000000 2211533729621 5000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265982683/10000000000 : ℝ)^4215 ≤ (42864865723671/100000000000000 : ℝ)^3191 := by
    have hnat : (5265982683 : ℕ)^4215*100000000000000^3191 ≤ 42864865723671^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265982683 10000000000 42864865723671 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-265270143/1250000000 : ℝ), (5392524721/10000000000 : ℝ), (5265982683/10000000000 : ℝ)] ![(6452229837551/50000000000000 : ℝ), (2211533729621/5000000000000 : ℝ), (42864865723671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-265270143/1250000000 : ℝ)|^4215 ≤ (6452229837551/50000000000000 : ℝ)^3191
        have hw : |(-265270143/1250000000 : ℝ)|=(265270143/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392524721/10000000000 : ℝ)|^4215 ≤ (2211533729621/5000000000000 : ℝ)^3191
        have hw : |(5392524721/10000000000 : ℝ)|=(5392524721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265982683/10000000000 : ℝ)|^4215 ≤ (42864865723671/100000000000000 : ℝ)^3191
        have hw : |(5265982683/10000000000 : ℝ)|=(5265982683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s5_1 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344647733/10000000000 : ℝ)*x 0 + (-2186339499/10000000000 : ℝ)*x 1 + (2632991327/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344647733/10000000000 : ℝ)^4215 ≤ (8742539954409/20000000000000 : ℝ)^3191 := by
    have hnat : (5344647733 : ℕ)^4215*20000000000000^3191 ≤ 8742539954409^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344647733 10000000000 8742539954409 20000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2186339499/10000000000 : ℝ)^4215 ≤ (13422434799367/100000000000000 : ℝ)^3191 := by
    have hnat : (2186339499 : ℕ)^4215*100000000000000^3191 ≤ 13422434799367^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186339499 10000000000 13422434799367 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632991327/5000000000 : ℝ)^4215 ≤ (2143243270593/5000000000000 : ℝ)^3191 := by
    have hnat : (2632991327 : ℕ)^4215*5000000000000^3191 ≤ 2143243270593^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632991327 5000000000 2143243270593 5000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344647733/10000000000 : ℝ), (-2186339499/10000000000 : ℝ), (2632991327/5000000000 : ℝ)] ![(8742539954409/20000000000000 : ℝ), (13422434799367/100000000000000 : ℝ), (2143243270593/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344647733/10000000000 : ℝ)|^4215 ≤ (8742539954409/20000000000000 : ℝ)^3191
        have hw : |(5344647733/10000000000 : ℝ)|=(5344647733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2186339499/10000000000 : ℝ)|^4215 ≤ (13422434799367/100000000000000 : ℝ)^3191
        have hw : |(-2186339499/10000000000 : ℝ)|=(2186339499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632991327/5000000000 : ℝ)|^4215 ≤ (2143243270593/5000000000000 : ℝ)^3191
        have hw : |(2632991327/5000000000 : ℝ)|=(2632991327/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s5_2 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5344647583/10000000000 : ℝ)*x 0 + (526598263/1000000000 : ℝ)*x 1 + (-2186339731/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344647583/10000000000 : ℝ)^4215 ≤ (43712698151539/100000000000000 : ℝ)^3191 := by
    have hnat : (5344647583 : ℕ)^4215*100000000000000^3191 ≤ 43712698151539^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344647583 10000000000 43712698151539 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526598263/1000000000 : ℝ)^4215 ≤ (4286486515381/10000000000000 : ℝ)^3191 := by
    have hnat : (526598263 : ℕ)^4215*10000000000000^3191 ≤ 4286486515381^3191*1000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526598263 1000000000 4286486515381 10000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2186339731/10000000000 : ℝ)^4215 ≤ (13422436680729/100000000000000 : ℝ)^3191 := by
    have hnat : (2186339731 : ℕ)^4215*100000000000000^3191 ≤ 13422436680729^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2186339731 10000000000 13422436680729 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344647583/10000000000 : ℝ), (526598263/1000000000 : ℝ), (-2186339731/10000000000 : ℝ)] ![(43712698151539/100000000000000 : ℝ), (4286486515381/10000000000000 : ℝ), (13422436680729/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344647583/10000000000 : ℝ)|^4215 ≤ (43712698151539/100000000000000 : ℝ)^3191
        have hw : |(5344647583/10000000000 : ℝ)|=(5344647583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526598263/1000000000 : ℝ)|^4215 ≤ (4286486515381/10000000000000 : ℝ)^3191
        have hw : |(526598263/1000000000 : ℝ)|=(526598263/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2186339731/10000000000 : ℝ)|^4215 ≤ (13422436680729/100000000000000 : ℝ)^3191
        have hw : |(-2186339731/10000000000 : ℝ)|=(2186339731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s5_3 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4351398207/10000000000 : ℝ)*x 0 + (845002173/2000000000 : ℝ)*x 1 + (448146317/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351398207/10000000000 : ℝ)^4215 ≤ (33316847595721/100000000000000 : ℝ)^3191 := by
    have hnat : (4351398207 : ℕ)^4215*100000000000000^3191 ≤ 33316847595721^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351398207 10000000000 33316847595721 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (845002173/2000000000 : ℝ)^4215 ≤ (8011153249799/25000000000000 : ℝ)^3191 := by
    have hnat : (845002173 : ℕ)^4215*25000000000000^3191 ≤ 8011153249799^3191*2000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845002173 2000000000 8011153249799 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (448146317/1000000000 : ℝ)^4215 ≤ (34638539389409/100000000000000 : ℝ)^3191 := by
    have hnat : (448146317 : ℕ)^4215*100000000000000^3191 ≤ 34638539389409^3191*1000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448146317 1000000000 34638539389409 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351398207/10000000000 : ℝ), (845002173/2000000000 : ℝ), (448146317/1000000000 : ℝ)] ![(33316847595721/100000000000000 : ℝ), (8011153249799/25000000000000 : ℝ), (34638539389409/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351398207/10000000000 : ℝ)|^4215 ≤ (33316847595721/100000000000000 : ℝ)^3191
        have hw : |(4351398207/10000000000 : ℝ)|=(4351398207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(845002173/2000000000 : ℝ)|^4215 ≤ (8011153249799/25000000000000 : ℝ)^3191
        have hw : |(845002173/2000000000 : ℝ)|=(845002173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(448146317/1000000000 : ℝ)|^4215 ≤ (34638539389409/100000000000000 : ℝ)^3191
        have hw : |(448146317/1000000000 : ℝ)|=(448146317/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s5_4 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-530541657/2500000000 : ℝ)*x 0 + (2633153689/5000000000 : ℝ)*x 1 + (2696099209/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530541657/2500000000 : ℝ)^4215 ≤ (516180148939/4000000000000 : ℝ)^3191 := by
    have hnat : (530541657 : ℕ)^4215*4000000000000^3191 ≤ 516180148939^3191*2500000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530541657 2500000000 516180148939 4000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633153689/5000000000 : ℝ)^4215 ≤ (42868356907467/100000000000000 : ℝ)^3191 := by
    have hnat : (2633153689 : ℕ)^4215*100000000000000^3191 ≤ 42868356907467^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633153689 5000000000 42868356907467 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696099209/5000000000 : ℝ)^4215 ≤ (22113569675637/50000000000000 : ℝ)^3191 := by
    have hnat : (2696099209 : ℕ)^4215*50000000000000^3191 ≤ 22113569675637^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696099209 5000000000 22113569675637 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-530541657/2500000000 : ℝ), (2633153689/5000000000 : ℝ), (2696099209/5000000000 : ℝ)] ![(516180148939/4000000000000 : ℝ), (42868356907467/100000000000000 : ℝ), (22113569675637/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-530541657/2500000000 : ℝ)|^4215 ≤ (516180148939/4000000000000 : ℝ)^3191
        have hw : |(-530541657/2500000000 : ℝ)|=(530541657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633153689/5000000000 : ℝ)|^4215 ≤ (42868356907467/100000000000000 : ℝ)^3191
        have hw : |(2633153689/5000000000 : ℝ)|=(2633153689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696099209/5000000000 : ℝ)|^4215 ≤ (22113569675637/50000000000000 : ℝ)^3191
        have hw : |(2696099209/5000000000 : ℝ)|=(2696099209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s5_5 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312371459/10000000000 : ℝ)*x 0 + (-2060123779/10000000000 : ℝ)*x 1 + (5392198091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312371459/10000000000 : ℝ)^4215 ≤ (5420543190033/12500000000000 : ℝ)^3191 := by
    have hnat : (5312371459 : ℕ)^4215*12500000000000^3191 ≤ 5420543190033^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312371459 10000000000 5420543190033 12500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2060123779/10000000000 : ℝ)^4215 ≤ (6204259330497/50000000000000 : ℝ)^3191 := by
    have hnat : (2060123779 : ℕ)^4215*50000000000000^3191 ≤ 6204259330497^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060123779 10000000000 6204259330497 50000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392198091/10000000000 : ℝ)^4215 ≤ (11056783952129/25000000000000 : ℝ)^3191 := by
    have hnat : (5392198091 : ℕ)^4215*25000000000000^3191 ≤ 11056783952129^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392198091 10000000000 11056783952129 25000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312371459/10000000000 : ℝ), (-2060123779/10000000000 : ℝ), (5392198091/10000000000 : ℝ)] ![(5420543190033/12500000000000 : ℝ), (6204259330497/50000000000000 : ℝ), (11056783952129/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312371459/10000000000 : ℝ)|^4215 ≤ (5420543190033/12500000000000 : ℝ)^3191
        have hw : |(5312371459/10000000000 : ℝ)|=(5312371459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2060123779/10000000000 : ℝ)|^4215 ≤ (6204259330497/50000000000000 : ℝ)^3191
        have hw : |(-2060123779/10000000000 : ℝ)|=(2060123779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392198091/10000000000 : ℝ)|^4215 ≤ (11056783952129/25000000000000 : ℝ)^3191
        have hw : |(5392198091/10000000000 : ℝ)|=(5392198091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s5_6 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5312371501/10000000000 : ℝ)*x 0 + (2696098999/5000000000 : ℝ)*x 1 + (-2060123849/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312371501/10000000000 : ℝ)^4215 ≤ (69382953557/160000000000 : ℝ)^3191 := by
    have hnat : (5312371501 : ℕ)^4215*160000000000^3191 ≤ 69382953557^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312371501 10000000000 69382953557 160000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696098999/5000000000 : ℝ)^4215 ≤ (44227134800943/100000000000000 : ℝ)^3191 := by
    have hnat : (2696098999 : ℕ)^4215*100000000000000^3191 ≤ 44227134800943^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696098999 5000000000 44227134800943 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2060123849/10000000000 : ℝ)^4215 ≤ (12408519217917/100000000000000 : ℝ)^3191 := by
    have hnat : (2060123849 : ℕ)^4215*100000000000000^3191 ≤ 12408519217917^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060123849 10000000000 12408519217917 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312371501/10000000000 : ℝ), (2696098999/5000000000 : ℝ), (-2060123849/10000000000 : ℝ)] ![(69382953557/160000000000 : ℝ), (44227134800943/100000000000000 : ℝ), (12408519217917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312371501/10000000000 : ℝ)|^4215 ≤ (69382953557/160000000000 : ℝ)^3191
        have hw : |(5312371501/10000000000 : ℝ)|=(5312371501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696098999/5000000000 : ℝ)|^4215 ≤ (44227134800943/100000000000000 : ℝ)^3191
        have hw : |(2696098999/5000000000 : ℝ)|=(2696098999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2060123849/10000000000 : ℝ)|^4215 ≤ (12408519217917/100000000000000 : ℝ)^3191
        have hw : |(-2060123849/10000000000 : ℝ)|=(2060123849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1237_s5_7 (p : ℝ) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4351408451/10000000000 : ℝ)*x 0 + (2240401997/5000000000 : ℝ)*x 1 + (16902689/40000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4351408451/10000000000 : ℝ)^4215 ≤ (4164618899937/12500000000000 : ℝ)^3191 := by
    have hnat : (4351408451 : ℕ)^4215*12500000000000^3191 ≤ 4164618899937^3191*10000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4351408451 10000000000 4164618899937 12500000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2240401997/5000000000 : ℝ)^4215 ≤ (34631809597271/100000000000000 : ℝ)^3191 := by
    have hnat : (2240401997 : ℕ)^4215*100000000000000^3191 ≤ 34631809597271^3191*5000000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2240401997 5000000000 34631809597271 100000000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (16902689/40000000 : ℝ)^4215 ≤ (400640489739/1250000000000 : ℝ)^3191 := by
    have hnat : (16902689 : ℕ)^4215*1250000000000^3191 ≤ 400640489739^3191*40000000^4215 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      16902689 40000000 400640489739 1250000000000 4215 3191 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4215/1024 : ℝ)) 4215 3191 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4351408451/10000000000 : ℝ), (2240401997/5000000000 : ℝ), (16902689/40000000 : ℝ)] ![(4164618899937/12500000000000 : ℝ), (34631809597271/100000000000000 : ℝ), (400640489739/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4351408451/10000000000 : ℝ)|^4215 ≤ (4164618899937/12500000000000 : ℝ)^3191
        have hw : |(4351408451/10000000000 : ℝ)|=(4351408451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2240401997/5000000000 : ℝ)|^4215 ≤ (34631809597271/100000000000000 : ℝ)^3191
        have hw : |(2240401997/5000000000 : ℝ)|=(2240401997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(16902689/40000000 : ℝ)|^4215 ≤ (400640489739/1250000000000 : ℝ)^3191
        have hw : |(16902689/40000000 : ℝ)|=(16902689/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1237_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h) :
    (11447/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (883/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (709/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (709/6250 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (709/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3559/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (709/6250 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (709/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3559/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (709/6250 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (709/6250 : ℝ) ^ (8429/2048 : ℝ) ≤ (12873004092105321/100000000000000000000 : ℝ) := by
    have hpowers : (709/6250 : ℝ)^8429 ≤ (12873004092105321/100000000000000000000 : ℝ)^2048 := by
      have hnat : (709 : ℕ)^8429*100000000000000000000^2048 ≤ 12873004092105321^2048*6250^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        709 6250 12873004092105321 100000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (709/6250 : ℝ)) (X := (12873004092105321/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (3559/25000 : ℝ) ^ (8429/2048 : ℝ) ≤ (32777794302240407/100000000000000000000 : ℝ) := by
    have hpowers : (3559/25000 : ℝ)^8429 ≤ (32777794302240407/100000000000000000000 : ℝ)^2048 := by
      have hnat : (3559 : ℕ)^8429*100000000000000000000^2048 ≤ 32777794302240407^2048*25000^8429 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3559 25000 32777794302240407 100000000000000000000 8429 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3559/25000 : ℝ)) (X := (32777794302240407/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50012873004092105321/50000000000000000000 : ℝ) ≤ (10000625491601403/10000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (50012873004092105321/50000000000000000000 : ℝ)^2048 ≤ (10000625491601403/10000000000000000 : ℝ)^8429 := by
      have hnat : (50012873004092105321 : ℕ)^2048*10000000000000000^8429 ≤ 10000625491601403^8429*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012873004092105321 50000000000000000000 10000625491601403 10000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000625491601403/10000000000000000 : ℝ)) (X := (50012873004092105321/50000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (390803323431227913/390625000000000000 : ℝ) ≤ (5000554494509069/5000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (390803323431227913/390625000000000000 : ℝ)^2048 ≤ (5000554494509069/5000000000000000 : ℝ)^8429 := by
      have hnat : (390803323431227913 : ℕ)^2048*5000000000000000^8429 ≤ 5000554494509069^8429*390625000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        390803323431227913 390625000000000000 5000554494509069 5000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000554494509069/5000000000000000 : ℝ)) (X := (390803323431227913/390625000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032777794302240407/50000000000000000000 : ℝ) ≤ (10001592486434873/10000000000000000 : ℝ) ^ (8429/2048 : ℝ) := by
    have hpowers : (50032777794302240407/50000000000000000000 : ℝ)^2048 ≤ (10001592486434873/10000000000000000 : ℝ)^8429 := by
      have hnat : (50032777794302240407 : ℕ)^2048*10000000000000000^8429 ≤ 10001592486434873^8429*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032777794302240407 50000000000000000000 10001592486434873 10000000000000000 2048 8429 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001592486434873/10000000000000000 : ℝ)) (X := (50032777794302240407/50000000000000000000 : ℝ)) (by norm_num) 8429 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(12873004092105321/100000000000000000000 : ℝ) ≤ ((7227709833080093449/7230000000000000000 : ℝ)+2*(96699483347/57840000000000 : ℝ)*(709/6250 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (7227709833080093449/7230000000000000000 : ℝ)+2*(96699483347/57840000000000 : ℝ)*(709/6250 : ℝ)=(10000625491601403/10000000000000000 : ℝ) by norm_num, show 1+2*(12873004092105321/100000000000000000000 : ℝ)=(50012873004092105321/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32777794302240407/100000000000000000000 : ℝ)+(12873004092105321/100000000000000000000 : ℝ) ≤ ((7227709833080093449/7230000000000000000 : ℝ)+(96699483347/57840000000000 : ℝ)*((3559/25000 : ℝ)+(709/6250 : ℝ)))^(8429/2048 : ℝ) := by
    rw [show (7227709833080093449/7230000000000000000 : ℝ)+(96699483347/57840000000000 : ℝ)*((3559/25000 : ℝ)+(709/6250 : ℝ))=(5000554494509069/5000000000000000 : ℝ) by norm_num, show 1+(32777794302240407/100000000000000000000 : ℝ)+(12873004092105321/100000000000000000000 : ℝ)=(390803323431227913/390625000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32777794302240407/100000000000000000000 : ℝ) ≤ ((7227709833080093449/7230000000000000000 : ℝ)+2*(96699483347/57840000000000 : ℝ)*(3559/25000 : ℝ))^(8429/2048 : ℝ) := by
    rw [show (7227709833080093449/7230000000000000000 : ℝ)+2*(96699483347/57840000000000 : ℝ)*(3559/25000 : ℝ)=(10001592486434873/10000000000000000 : ℝ) by norm_num, show 1+2*(32777794302240407/100000000000000000000 : ℝ)=(50032777794302240407/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7227709833080093449/7230000000000000000 : ℝ)*(X 1 0+X 2 0)+(96699483347/57840000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7227709833080093449/7230000000000000000 : ℝ)) (alpha := (96699483347/57840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7227709833080093449/7230000000000000000 : ℝ)*(X 0 1+X 2 1)+(96699483347/57840000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7227709833080093449/7230000000000000000 : ℝ)) (alpha := (96699483347/57840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7227709833080093449/7230000000000000000 : ℝ)*(X 0 2+X 1 2)+(96699483347/57840000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8429/2048 : ℝ)) (lo := (709/6250 : ℝ)) (hi := (3559/25000 : ℝ)) (c := (7227709833080093449/7230000000000000000 : ℝ)) (alpha := (96699483347/57840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-265270143/1250000000 : ℝ)*X 0 0+(5392524721/10000000000 : ℝ)*X 0 1+(5265982683/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344647733/10000000000 : ℝ)*X 1 0+(-2186339499/10000000000 : ℝ)*X 1 1+(2632991327/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344647583/10000000000 : ℝ)*X 2 0+(526598263/1000000000 : ℝ)*X 2 1+(-2186339731/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4351398207/10000000000 : ℝ)*X 0 0+(845002173/2000000000 : ℝ)*X 0 1+(448146317/1000000000 : ℝ)*X 0 2+(4351398207/10000000000 : ℝ)*X 1 0+(845002173/2000000000 : ℝ)*X 1 1+(448146317/1000000000 : ℝ)*X 1 2+(4351398207/10000000000 : ℝ)*X 2 0+(845002173/2000000000 : ℝ)*X 2 1+(448146317/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-530541657/2500000000 : ℝ)*X 0 0+(2633153689/5000000000 : ℝ)*X 0 1+(2696099209/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312371459/10000000000 : ℝ)*X 1 0+(-2060123779/10000000000 : ℝ)*X 1 1+(5392198091/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312371501/10000000000 : ℝ)*X 2 0+(2696098999/5000000000 : ℝ)*X 2 1+(-2060123849/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4351408451/10000000000 : ℝ)*X 0 0+(2240401997/5000000000 : ℝ)*X 0 1+(16902689/40000000 : ℝ)*X 0 2+(4351408451/10000000000 : ℝ)*X 1 0+(2240401997/5000000000 : ℝ)*X 1 1+(16902689/40000000 : ℝ)*X 1 2+(4351408451/10000000000 : ℝ)*X 2 0+(2240401997/5000000000 : ℝ)*X 2 1+(16902689/40000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1237_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (30616909923686991226989547/3012500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1917220033/100000000000000 : ℝ)*(base19) + (1728847727/100000000000000 : ℝ)*(base23) + (11861769/20000000000000 : ℝ)*(lower2) + (78049841/20000000000000 : ℝ)*(upper3) + (38584823/50000000000000 : ℝ)*(lower4) + (147525416099197/2500000000000 : ℝ)*(major0) + (147525416099197/2500000000000 : ℝ)*(major1) + (147525416099197/2500000000000 : ℝ)*(major2) + (98782168424221/1250000000000 : ℝ)*(sp0) + (987826341448527/12500000000000 : ℝ)*(sp1) + (3951305459980261/50000000000000 : ℝ)*(sp2) + (389938710653017/10000000000000 : ℝ)*(sp3) + (4896858821/12500000000000 : ℝ)*(sp4) + (2074613813/6250000000000 : ℝ)*(sp7) + (1949710150175589/50000000000000 : ℝ)*(f.failure) + (987826581101031/12500000000000 : ℝ)*(f.sum) + (782416384697/180750000000000000000000000 : ℝ)*base65 + (114676456536785453/18075000000000000000000000000000 : ℝ)*base67 + (232077507824435453/18075000000000000000000000000000 : ℝ)*base69 + (192439793268714547/18075000000000000000000000000000 : ℝ)*base72 + (299326306811/45187500000000000000000000 : ℝ)*base73 + (259167442994435453/18075000000000000000000000000000 : ℝ)*base75 + (15825425532564547/18075000000000000000000000000000 : ℝ)*base78 + (4945031653085453/18075000000000000000000000000000 : ℝ)*base79 + (782066788169/180750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (58993943/5000000000000000000000 : ℝ)*base90 + (58993943/5000000000000000000000 : ℝ)*base92 + (58993943/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (101869036971230159103548991/120500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2326289173/100000000000000 : ℝ)*(base19) + (2901338843/100000000000000 : ℝ)*(base23) + (33761419/12500000000000 : ℝ)*(upper2) + (157057067/100000000000000 : ℝ)*(upper3) + (77956299/20000000000000 : ℝ)*(upper5) + (5931458842829853/100000000000000 : ℝ)*(major0) + (5931458842829853/100000000000000 : ℝ)*(major1) + (5931458842829853/100000000000000 : ℝ)*(major2) + (3243969003/6250000000000 : ℝ)*(sp1) + (1050681289/2000000000000 : ℝ)*(sp2) + (1985845251271153/25000000000000 : ℝ)*(sp4) + (7943326775291391/100000000000000 : ℝ)*(sp5) + (7943325569681319/100000000000000 : ℝ)*(sp6) + (3919536652395543/100000000000000 : ℝ)*(sp7) + (3919536652395543/100000000000000 : ℝ)*(f.failure) + (1985845251271153/25000000000000 : ℝ)*(f.sum) + (1756849829049/964000000000000000000000000 : ℝ)*base65 + (518978746266064001/241000000000000000000000000000000 : ℝ)*base68 + (6166972682874064001/241000000000000000000000000000000 : ℝ)*base70 + (1704120459054064001/241000000000000000000000000000000 : ℝ)*base72 + (7022107312233/964000000000000000000000000 : ℝ)*base73 + (3352857654711064001/241000000000000000000000000000000 : ℝ)*base76 + (1634250104410064001/241000000000000000000000000000000 : ℝ)*base78 + (7055003708032064001/241000000000000000000000000000000 : ℝ)*base80 + (2316278072119/964000000000000000000000000 : ℝ)*base82 + (140657859/10000000000000000000000 : ℝ)*base89 + (140657859/10000000000000000000000 : ℝ)*base91 + (140657859/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1237_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3559/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (709/6250 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (883/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1237_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1237_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4059/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9479/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (883/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1237_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1237_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1237_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8429/2048 : ℝ) ≤ p) (hpb : p ≤ (4215/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (151330613/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4059/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9479/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11447/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (883/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1237_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
