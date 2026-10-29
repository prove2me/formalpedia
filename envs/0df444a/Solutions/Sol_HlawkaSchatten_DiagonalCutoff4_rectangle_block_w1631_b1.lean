-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1631_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:59:59.135865+00:00
-- url     : https://prove2.me/submissions/15f79828-99db-4331-9e2c-c10de3c03f5b

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
theorem support_rectangle_w1631_s3_0 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-826378567/5000000000 : ℝ)*x 0 + (5453377691/10000000000 : ℝ)*x 1 + (1295596269/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (826378567/5000000000 : ℝ)^4843 ≤ (2039929064743/20000000000000 : ℝ)^3819 := by
    have hnat : (826378567 : ℕ)^4843*20000000000000^3819 ≤ 2039929064743^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826378567 5000000000 2039929064743 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5453377691/10000000000 : ℝ)^4843 ≤ (23175383404757/50000000000000 : ℝ)^3819 := by
    have hnat : (5453377691 : ℕ)^4843*50000000000000^3819 ≤ 23175383404757^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5453377691 10000000000 23175383404757 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295596269/2500000000 : ℝ)^4843 ≤ (10862396963097/25000000000000 : ℝ)^3819 := by
    have hnat : (1295596269 : ℕ)^4843*25000000000000^3819 ≤ 10862396963097^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295596269 2500000000 10862396963097 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-826378567/5000000000 : ℝ), (5453377691/10000000000 : ℝ), (1295596269/2500000000 : ℝ)] ![(2039929064743/20000000000000 : ℝ), (23175383404757/50000000000000 : ℝ), (10862396963097/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-826378567/5000000000 : ℝ)|^4843 ≤ (2039929064743/20000000000000 : ℝ)^3819
        have hw : |(-826378567/5000000000 : ℝ)|=(826378567/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5453377691/10000000000 : ℝ)|^4843 ≤ (23175383404757/50000000000000 : ℝ)^3819
        have hw : |(5453377691/10000000000 : ℝ)|=(5453377691/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295596269/2500000000 : ℝ)|^4843 ≤ (10862396963097/25000000000000 : ℝ)^3819
        have hw : |(1295596269/2500000000 : ℝ)|=(1295596269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s3_1 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675308933/5000000000 : ℝ)*x 0 + (-896187377/5000000000 : ℝ)*x 1 + (5182385233/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675308933/5000000000 : ℝ)^4843 ≤ (22622993300103/50000000000000 : ℝ)^3819 := by
    have hnat : (2675308933 : ℕ)^4843*50000000000000^3819 ≤ 22622993300103^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675308933 5000000000 22622993300103 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (896187377/5000000000 : ℝ)^4843 ≤ (5652211931739/50000000000000 : ℝ)^3819 := by
    have hnat : (896187377 : ℕ)^4843*50000000000000^3819 ≤ 5652211931739^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      896187377 5000000000 5652211931739 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182385233/10000000000 : ℝ)^4843 ≤ (21724794760817/50000000000000 : ℝ)^3819 := by
    have hnat : (5182385233 : ℕ)^4843*50000000000000^3819 ≤ 21724794760817^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182385233 10000000000 21724794760817 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675308933/5000000000 : ℝ), (-896187377/5000000000 : ℝ), (5182385233/10000000000 : ℝ)] ![(22622993300103/50000000000000 : ℝ), (5652211931739/50000000000000 : ℝ), (21724794760817/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675308933/5000000000 : ℝ)|^4843 ≤ (22622993300103/50000000000000 : ℝ)^3819
        have hw : |(2675308933/5000000000 : ℝ)|=(2675308933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-896187377/5000000000 : ℝ)|^4843 ≤ (5652211931739/50000000000000 : ℝ)^3819
        have hw : |(-896187377/5000000000 : ℝ)|=(896187377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182385233/10000000000 : ℝ)|^4843 ≤ (21724794760817/50000000000000 : ℝ)^3819
        have hw : |(5182385233/10000000000 : ℝ)|=(5182385233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s3_2 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (107012363/200000000 : ℝ)*x 0 + (2591192381/5000000000 : ℝ)*x 1 + (-1792374999/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107012363/200000000 : ℝ)^4843 ≤ (4524598964571/10000000000000 : ℝ)^3819 := by
    have hnat : (107012363 : ℕ)^4843*10000000000000^3819 ≤ 4524598964571^3819*200000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107012363 200000000 4524598964571 10000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591192381/5000000000 : ℝ)^4843 ≤ (8689916902779/20000000000000 : ℝ)^3819 := by
    have hnat : (2591192381 : ℕ)^4843*20000000000000^3819 ≤ 8689916902779^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591192381 5000000000 8689916902779 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1792374999/10000000000 : ℝ)^4843 ≤ (11304425823001/100000000000000 : ℝ)^3819 := by
    have hnat : (1792374999 : ℕ)^4843*100000000000000^3819 ≤ 11304425823001^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792374999 10000000000 11304425823001 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107012363/200000000 : ℝ), (2591192381/5000000000 : ℝ), (-1792374999/10000000000 : ℝ)] ![(4524598964571/10000000000000 : ℝ), (8689916902779/20000000000000 : ℝ), (11304425823001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107012363/200000000 : ℝ)|^4843 ≤ (4524598964571/10000000000000 : ℝ)^3819
        have hw : |(107012363/200000000 : ℝ)|=(107012363/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591192381/5000000000 : ℝ)|^4843 ≤ (8689916902779/20000000000000 : ℝ)^3819
        have hw : |(2591192381/5000000000 : ℝ)|=(2591192381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1792374999/10000000000 : ℝ)|^4843 ≤ (11304425823001/100000000000000 : ℝ)^3819
        have hw : |(-1792374999/10000000000 : ℝ)|=(1792374999/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s3_3 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1048879999/2500000000 : ℝ)*x 0 + (1931871619/5000000000 : ℝ)*x 1 + (1137028667/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048879999/2500000000 : ℝ)^4843 ≤ (33238560859613/100000000000000 : ℝ)^3819 := by
    have hnat : (1048879999 : ℕ)^4843*100000000000000^3819 ≤ 33238560859613^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048879999 2500000000 33238560859613 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1931871619/5000000000 : ℝ)^4843 ≤ (29941360849743/100000000000000 : ℝ)^3819 := by
    have hnat : (1931871619 : ℕ)^4843*100000000000000^3819 ≤ 29941360849743^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931871619 5000000000 29941360849743 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1137028667/2500000000 : ℝ)^4843 ≤ (36820078275557/100000000000000 : ℝ)^3819 := by
    have hnat : (1137028667 : ℕ)^4843*100000000000000^3819 ≤ 36820078275557^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1137028667 2500000000 36820078275557 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048879999/2500000000 : ℝ), (1931871619/5000000000 : ℝ), (1137028667/2500000000 : ℝ)] ![(33238560859613/100000000000000 : ℝ), (29941360849743/100000000000000 : ℝ), (36820078275557/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048879999/2500000000 : ℝ)|^4843 ≤ (33238560859613/100000000000000 : ℝ)^3819
        have hw : |(1048879999/2500000000 : ℝ)|=(1048879999/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1931871619/5000000000 : ℝ)|^4843 ≤ (29941360849743/100000000000000 : ℝ)^3819
        have hw : |(1931871619/5000000000 : ℝ)|=(1931871619/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1137028667/2500000000 : ℝ)|^4843 ≤ (36820078275557/100000000000000 : ℝ)^3819
        have hw : |(1137028667/2500000000 : ℝ)|=(1137028667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s3_4 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1652824367/10000000000 : ℝ)*x 0 + (2592210973/5000000000 : ℝ)*x 1 + (2725659721/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1652824367/10000000000 : ℝ)^4843 ≤ (40800685973/400000000000 : ℝ)^3819 := by
    have hnat : (1652824367 : ℕ)^4843*400000000000^3819 ≤ 40800685973^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1652824367 10000000000 40800685973 400000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592210973/5000000000 : ℝ)^4843 ≤ (43471245285669/100000000000000 : ℝ)^3819 := by
    have hnat : (2592210973 : ℕ)^4843*100000000000000^3819 ≤ 43471245285669^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592210973 5000000000 43471245285669 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2725659721/5000000000 : ℝ)^4843 ≤ (11582145801533/25000000000000 : ℝ)^3819 := by
    have hnat : (2725659721 : ℕ)^4843*25000000000000^3819 ≤ 11582145801533^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2725659721 5000000000 11582145801533 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1652824367/10000000000 : ℝ), (2592210973/5000000000 : ℝ), (2725659721/5000000000 : ℝ)] ![(40800685973/400000000000 : ℝ), (43471245285669/100000000000000 : ℝ), (11582145801533/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1652824367/10000000000 : ℝ)|^4843 ≤ (40800685973/400000000000 : ℝ)^3819
        have hw : |(-1652824367/10000000000 : ℝ)|=(1652824367/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592210973/5000000000 : ℝ)|^4843 ≤ (43471245285669/100000000000000 : ℝ)^3819
        have hw : |(2592210973/5000000000 : ℝ)|=(2592210973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2725659721/5000000000 : ℝ)|^4843 ≤ (11582145801533/25000000000000 : ℝ)^3819
        have hw : |(2725659721/5000000000 : ℝ)|=(2725659721/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s3_5 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055680411/2000000000 : ℝ)*x 0 + (-76172027/500000000 : ℝ)*x 1 + (5451319553/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055680411/2000000000 : ℝ)^4843 ≤ (44472978448841/100000000000000 : ℝ)^3819 := by
    have hnat : (1055680411 : ℕ)^4843*100000000000000^3819 ≤ 44472978448841^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055680411 2000000000 44472978448841 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (76172027/500000000 : ℝ)^4843 ≤ (9198437138303/100000000000000 : ℝ)^3819 := by
    have hnat : (76172027 : ℕ)^4843*100000000000000^3819 ≤ 9198437138303^3819*500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      76172027 500000000 9198437138303 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5451319553/10000000000 : ℝ)^4843 ≤ (46328584402419/100000000000000 : ℝ)^3819 := by
    have hnat : (5451319553 : ℕ)^4843*100000000000000^3819 ≤ 46328584402419^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5451319553 10000000000 46328584402419 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055680411/2000000000 : ℝ), (-76172027/500000000 : ℝ), (5451319553/10000000000 : ℝ)] ![(44472978448841/100000000000000 : ℝ), (9198437138303/100000000000000 : ℝ), (46328584402419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055680411/2000000000 : ℝ)|^4843 ≤ (44472978448841/100000000000000 : ℝ)^3819
        have hw : |(1055680411/2000000000 : ℝ)|=(1055680411/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-76172027/500000000 : ℝ)|^4843 ≤ (9198437138303/100000000000000 : ℝ)^3819
        have hw : |(-76172027/500000000 : ℝ)|=(76172027/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5451319553/10000000000 : ℝ)|^4843 ≤ (46328584402419/100000000000000 : ℝ)^3819
        have hw : |(5451319553/10000000000 : ℝ)|=(5451319553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s3_6 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278402111/10000000000 : ℝ)*x 0 + (1090263907/2000000000 : ℝ)*x 1 + (-1523440487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278402111/10000000000 : ℝ)^4843 ≤ (44472979047179/100000000000000 : ℝ)^3819 := by
    have hnat : (5278402111 : ℕ)^4843*100000000000000^3819 ≤ 44472979047179^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278402111 10000000000 44472979047179 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090263907/2000000000 : ℝ)^4843 ≤ (23164292104213/50000000000000 : ℝ)^3819 := by
    have hnat : (1090263907 : ℕ)^4843*50000000000000^3819 ≤ 23164292104213^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090263907 2000000000 23164292104213 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1523440487/10000000000 : ℝ)^4843 ≤ (9198436732487/100000000000000 : ℝ)^3819 := by
    have hnat : (1523440487 : ℕ)^4843*100000000000000^3819 ≤ 9198436732487^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1523440487 10000000000 9198436732487 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278402111/10000000000 : ℝ), (1090263907/2000000000 : ℝ), (-1523440487/10000000000 : ℝ)] ![(44472979047179/100000000000000 : ℝ), (23164292104213/50000000000000 : ℝ), (9198436732487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278402111/10000000000 : ℝ)|^4843 ≤ (44472979047179/100000000000000 : ℝ)^3819
        have hw : |(5278402111/10000000000 : ℝ)|=(5278402111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090263907/2000000000 : ℝ)|^4843 ≤ (23164292104213/50000000000000 : ℝ)^3819
        have hw : |(1090263907/2000000000 : ℝ)|=(1090263907/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1523440487/10000000000 : ℝ)|^4843 ≤ (9198436732487/100000000000000 : ℝ)^3819
        have hw : |(-1523440487/10000000000 : ℝ)|=(1523440487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s3_7 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4195690247/10000000000 : ℝ)*x 0 + (4542971141/10000000000 : ℝ)*x 1 + (773788171/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4195690247/10000000000 : ℝ)^4843 ≤ (8310067830237/25000000000000 : ℝ)^3819 := by
    have hnat : (4195690247 : ℕ)^4843*25000000000000^3819 ≤ 8310067830237^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195690247 10000000000 8310067830237 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4542971141/10000000000 : ℝ)^4843 ≤ (4595910098349/12500000000000 : ℝ)^3819 := by
    have hnat : (4542971141 : ℕ)^4843*12500000000000^3819 ≤ 4595910098349^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542971141 10000000000 4595910098349 12500000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (773788171/2000000000 : ℝ)^4843 ≤ (29992447879661/100000000000000 : ℝ)^3819 := by
    have hnat : (773788171 : ℕ)^4843*100000000000000^3819 ≤ 29992447879661^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773788171 2000000000 29992447879661 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4195690247/10000000000 : ℝ), (4542971141/10000000000 : ℝ), (773788171/2000000000 : ℝ)] ![(8310067830237/25000000000000 : ℝ), (4595910098349/12500000000000 : ℝ), (29992447879661/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4195690247/10000000000 : ℝ)|^4843 ≤ (8310067830237/25000000000000 : ℝ)^3819
        have hw : |(4195690247/10000000000 : ℝ)|=(4195690247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4542971141/10000000000 : ℝ)|^4843 ≤ (4595910098349/12500000000000 : ℝ)^3819
        have hw : |(4542971141/10000000000 : ℝ)|=(4542971141/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(773788171/2000000000 : ℝ)|^4843 ≤ (29992447879661/100000000000000 : ℝ)^3819
        have hw : |(773788171/2000000000 : ℝ)|=(773788171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1631_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16411/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10469/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10559/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2039/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16411/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10469/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16411/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10469/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16411/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10469/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16411/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10469/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16411/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10469/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16411/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10469/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10469/100000 : ℝ) ^ (4839/1024 : ℝ) ≤ (2336026659502951/100000000000000000000 : ℝ) := by
    have hpowers : (10469/100000 : ℝ)^4839 ≤ (2336026659502951/100000000000000000000 : ℝ)^1024 := by
      have hnat : (10469 : ℕ)^4839*100000000000000000000^1024 ≤ 2336026659502951^1024*100000^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10469 100000 2336026659502951 100000000000000000000 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10469/100000 : ℝ)) (X := (2336026659502951/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16411/100000 : ℝ) ^ (4839/1024 : ℝ) ≤ (9772894542880881/50000000000000000000 : ℝ) := by
    have hpowers : (16411/100000 : ℝ)^4839 ≤ (9772894542880881/50000000000000000000 : ℝ)^1024 := by
      have hnat : (16411 : ℕ)^4839*50000000000000000000^1024 ≤ 9772894542880881^1024*100000^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16411 100000 9772894542880881 50000000000000000000 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16411/100000 : ℝ)) (X := (9772894542880881/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002336026659502951/50000000000000000000 : ℝ) ≤ (1250012358169279/1250000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (50002336026659502951/50000000000000000000 : ℝ)^1024 ≤ (1250012358169279/1250000000000000 : ℝ)^4839 := by
      have hnat : (50002336026659502951 : ℕ)^1024*1250000000000000^4839 ≤ 1250012358169279^4839*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002336026659502951 50000000000000000000 1250012358169279 1250000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250012358169279/1250000000000000 : ℝ)) (X := (50002336026659502951/50000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100021881815745264713/100000000000000000000 : ℝ) ≤ (2000092601970761/2000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (100021881815745264713/100000000000000000000 : ℝ)^1024 ≤ (2000092601970761/2000000000000000 : ℝ)^4839 := by
      have hnat : (100021881815745264713 : ℕ)^1024*2000000000000000^4839 ≤ 2000092601970761^4839*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100021881815745264713 100000000000000000000 2000092601970761 2000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000092601970761/2000000000000000 : ℝ)) (X := (100021881815745264713/100000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009772894542880881/25000000000000000000 : ℝ) ≤ (5000413577176689/5000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (25009772894542880881/25000000000000000000 : ℝ)^1024 ≤ (5000413577176689/5000000000000000 : ℝ)^4839 := by
      have hnat : (25009772894542880881 : ℕ)^1024*5000000000000000^4839 ≤ 5000413577176689^4839*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009772894542880881 25000000000000000000 5000413577176689 5000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000413577176689/5000000000000000 : ℝ)) (X := (25009772894542880881/25000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2336026659502951/100000000000000000000 : ℝ) ≤ ((5941296300040278707/5942000000000000000 : ℝ)+2*(364144499573/594200000000000 : ℝ)*(10469/100000 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (5941296300040278707/5942000000000000000 : ℝ)+2*(364144499573/594200000000000 : ℝ)*(10469/100000 : ℝ)=(1250012358169279/1250000000000000 : ℝ) by norm_num, show 1+2*(2336026659502951/100000000000000000000 : ℝ)=(50002336026659502951/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9772894542880881/50000000000000000000 : ℝ)+(2336026659502951/100000000000000000000 : ℝ) ≤ ((5941296300040278707/5942000000000000000 : ℝ)+(364144499573/594200000000000 : ℝ)*((16411/100000 : ℝ)+(10469/100000 : ℝ)))^(4839/1024 : ℝ) := by
    rw [show (5941296300040278707/5942000000000000000 : ℝ)+(364144499573/594200000000000 : ℝ)*((16411/100000 : ℝ)+(10469/100000 : ℝ))=(2000092601970761/2000000000000000 : ℝ) by norm_num, show 1+(9772894542880881/50000000000000000000 : ℝ)+(2336026659502951/100000000000000000000 : ℝ)=(100021881815745264713/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9772894542880881/50000000000000000000 : ℝ) ≤ ((5941296300040278707/5942000000000000000 : ℝ)+2*(364144499573/594200000000000 : ℝ)*(16411/100000 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (5941296300040278707/5942000000000000000 : ℝ)+2*(364144499573/594200000000000 : ℝ)*(16411/100000 : ℝ)=(5000413577176689/5000000000000000 : ℝ) by norm_num, show 1+2*(9772894542880881/50000000000000000000 : ℝ)=(25009772894542880881/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (5941296300040278707/5942000000000000000 : ℝ)*(X 1 0+X 2 0)+(364144499573/594200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (10469/100000 : ℝ)) (hi := (16411/100000 : ℝ)) (c := (5941296300040278707/5942000000000000000 : ℝ)) (alpha := (364144499573/594200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (5941296300040278707/5942000000000000000 : ℝ)*(X 0 1+X 2 1)+(364144499573/594200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (10469/100000 : ℝ)) (hi := (16411/100000 : ℝ)) (c := (5941296300040278707/5942000000000000000 : ℝ)) (alpha := (364144499573/594200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (5941296300040278707/5942000000000000000 : ℝ)*(X 0 2+X 1 2)+(364144499573/594200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (10469/100000 : ℝ)) (hi := (16411/100000 : ℝ)) (c := (5941296300040278707/5942000000000000000 : ℝ)) (alpha := (364144499573/594200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-826378567/5000000000 : ℝ)*X 0 0+(5453377691/10000000000 : ℝ)*X 0 1+(1295596269/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675308933/5000000000 : ℝ)*X 1 0+(-896187377/5000000000 : ℝ)*X 1 1+(5182385233/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((107012363/200000000 : ℝ)*X 2 0+(2591192381/5000000000 : ℝ)*X 2 1+(-1792374999/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1048879999/2500000000 : ℝ)*X 0 0+(1931871619/5000000000 : ℝ)*X 0 1+(1137028667/2500000000 : ℝ)*X 0 2+(1048879999/2500000000 : ℝ)*X 1 0+(1931871619/5000000000 : ℝ)*X 1 1+(1137028667/2500000000 : ℝ)*X 1 2+(1048879999/2500000000 : ℝ)*X 2 0+(1931871619/5000000000 : ℝ)*X 2 1+(1137028667/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1652824367/10000000000 : ℝ)*X 0 0+(2592210973/5000000000 : ℝ)*X 0 1+(2725659721/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1055680411/2000000000 : ℝ)*X 1 0+(-76172027/500000000 : ℝ)*X 1 1+(5451319553/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278402111/10000000000 : ℝ)*X 2 0+(1090263907/2000000000 : ℝ)*X 2 1+(-1523440487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4195690247/10000000000 : ℝ)*X 0 0+(4542971141/10000000000 : ℝ)*X 0 1+(773788171/2000000000 : ℝ)*X 0 2+(4195690247/10000000000 : ℝ)*X 1 0+(4542971141/10000000000 : ℝ)*X 1 1+(773788171/2000000000 : ℝ)*X 1 2+(4195690247/10000000000 : ℝ)*X 2 0+(4542971141/10000000000 : ℝ)*X 2 1+(773788171/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (126446620735615331273977053/59420000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (510933221/100000000000000 : ℝ)*(base19) + (741899699/100000000000000 : ℝ)*(base23) + (9991377/25000000000000 : ℝ)*(upper2) + (68566691/50000000000000 : ℝ)*(upper3) + (10592241/50000000000000 : ℝ)*(upper4) + (1287838187840267/50000000000000 : ℝ)*(major0) + (1287838187840267/50000000000000 : ℝ)*(major1) + (515135275136107/20000000000000 : ℝ)*(major2) + (14414634089101/390625000000 : ℝ)*(sp0) + (3690152023709347/100000000000000 : ℝ)*(sp1) + (922537948185717/25000000000000 : ℝ)*(sp2) + (365299205596221/25000000000000 : ℝ)*(sp3) + (775979089/12500000000000 : ℝ)*(sp4) + (3323399793/100000000000000 : ℝ)*(sp7) + (730600072892339/50000000000000 : ℝ)*(f.failure) + (461269066830321/12500000000000 : ℝ)*(f.sum) + (535720726633197/59420000000000000000000000000 : ℝ)*base65 + (1759767923331230231/297100000000000000000000000000000 : ℝ)*base68 + (482600704075857649/118840000000000000000000000000000 : ℝ)*base69 + (1110561350762369769/297100000000000000000000000000000 : ℝ)*base71 + (107129659592397/59420000000000000000000000000 : ℝ)*base73 + (37714002581417649/118840000000000000000000000000000 : ℝ)*base75 + (1062850354888704769/297100000000000000000000000000000 : ℝ)*base77 + (1229351039861895231/297100000000000000000000000000000 : ℝ)*base80 + (7920742190867/7427500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (18107997/1250000000000000000000 : ℝ)*base89 + (18107997/1250000000000000000000 : ℝ)*base91 + (5607997/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1722665905159717651412005113/148550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (427147413/25000000000000 : ℝ)*(base19) + (1903080637/100000000000000 : ℝ)*(base23) + (70476521/25000000000000 : ℝ)*(upper3) + (56629/97656250000 : ℝ)*(lower4) + (22052919/10000000000000 : ℝ)*(upper5) + (2615184147848247/100000000000000 : ℝ)*(major0) + (2615184147848247/100000000000000 : ℝ)*(major1) + (2615184147848247/100000000000000 : ℝ)*(major2) + (9981353981/50000000000000 : ℝ)*(sp1) + (1452694633/6250000000000 : ℝ)*(sp2) + (374675471372579/10000000000000 : ℝ)*(sp4) + (234170815151761/6250000000000 : ℝ)*(sp5) + (1873364783765513/50000000000000 : ℝ)*(sp6) + (5795364044607/390625000000 : ℝ)*(sp7) + (5795364044607/390625000000 : ℝ)*(f.failure) + (374675471372579/10000000000000 : ℝ)*(f.sum) + (3702229497791/29710000000000000000000000000 : ℝ)*base65 + (312987570956286629/594200000000000000000000000000000 : ℝ)*base67 + (844345114621313371/594200000000000000000000000000000 : ℝ)*base70 + (433332689063486629/594200000000000000000000000000000 : ℝ)*base71 + (64832055455109/29710000000000000000000000000 : ℝ)*base74 + (8601390068483886629/594200000000000000000000000000000 : ℝ)*base75 + (1093685976884686629/594200000000000000000000000000000 : ℝ)*base77 + (892734781371086629/594200000000000000000000000000000 : ℝ)*base79 + (114525142339929/29710000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (37869/39062500000000000000 : ℝ)*base89 + (37869/39062500000000000000 : ℝ)*base91 + (37869/39062500000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1631_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16411/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10469/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10559/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2039/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1631_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1631_s4_0 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-826413251/5000000000 : ℝ)*x 0 + (2726510209/5000000000 : ℝ)*x 1 + (5182696199/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (826413251/5000000000 : ℝ)^4843 ≤ (9961121291/97656250000 : ℝ)^3819 := by
    have hnat : (826413251 : ℕ)^4843*97656250000^3819 ≤ 9961121291^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826413251 5000000000 9961121291 97656250000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726510209/5000000000 : ℝ)^4843 ≤ (46346915995541/100000000000000 : ℝ)^3819 := by
    have hnat : (2726510209 : ℕ)^4843*100000000000000^3819 ≤ 46346915995541^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726510209 5000000000 46346915995541 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182696199/10000000000 : ℝ)^4843 ≤ (43452895783107/100000000000000 : ℝ)^3819 := by
    have hnat : (5182696199 : ℕ)^4843*100000000000000^3819 ≤ 43452895783107^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182696199 10000000000 43452895783107 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-826413251/5000000000 : ℝ), (2726510209/5000000000 : ℝ), (5182696199/10000000000 : ℝ)] ![(9961121291/97656250000 : ℝ), (46346915995541/100000000000000 : ℝ), (43452895783107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-826413251/5000000000 : ℝ)|^4843 ≤ (9961121291/97656250000 : ℝ)^3819
        have hw : |(-826413251/5000000000 : ℝ)|=(826413251/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726510209/5000000000 : ℝ)|^4843 ≤ (46346915995541/100000000000000 : ℝ)^3819
        have hw : |(2726510209/5000000000 : ℝ)|=(2726510209/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182696199/10000000000 : ℝ)|^4843 ≤ (43452895783107/100000000000000 : ℝ)^3819
        have hw : |(5182696199/10000000000 : ℝ)|=(5182696199/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s4_1 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350522003/10000000000 : ℝ)*x 0 + (-35841807/200000000 : ℝ)*x 1 + (5182695857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350522003/10000000000 : ℝ)^4843 ≤ (45244958605423/100000000000000 : ℝ)^3819 := by
    have hnat : (5350522003 : ℕ)^4843*100000000000000^3819 ≤ 45244958605423^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350522003 10000000000 45244958605423 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (35841807/200000000 : ℝ)^4843 ≤ (2825537308207/25000000000000 : ℝ)^3819 := by
    have hnat : (35841807 : ℕ)^4843*25000000000000^3819 ≤ 2825537308207^3819*200000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      35841807 200000000 2825537308207 25000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182695857/10000000000 : ℝ)^4843 ≤ (5431611518357/12500000000000 : ℝ)^3819 := by
    have hnat : (5182695857 : ℕ)^4843*12500000000000^3819 ≤ 5431611518357^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182695857 10000000000 5431611518357 12500000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350522003/10000000000 : ℝ), (-35841807/200000000 : ℝ), (5182695857/10000000000 : ℝ)] ![(45244958605423/100000000000000 : ℝ), (2825537308207/25000000000000 : ℝ), (5431611518357/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350522003/10000000000 : ℝ)|^4843 ≤ (45244958605423/100000000000000 : ℝ)^3819
        have hw : |(5350522003/10000000000 : ℝ)|=(5350522003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-35841807/200000000 : ℝ)|^4843 ≤ (2825537308207/25000000000000 : ℝ)^3819
        have hw : |(-35841807/200000000 : ℝ)|=(35841807/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182695857/10000000000 : ℝ)|^4843 ≤ (5431611518357/12500000000000 : ℝ)^3819
        have hw : |(5182695857/10000000000 : ℝ)|=(5182695857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s4_2 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070104383/2000000000 : ℝ)*x 0 + (5182695963/10000000000 : ℝ)*x 1 + (-1792090327/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070104383/2000000000 : ℝ)^4843 ≤ (180979830647/400000000000 : ℝ)^3819 := by
    have hnat : (1070104383 : ℕ)^4843*400000000000^3819 ≤ 180979830647^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070104383 2000000000 180979830647 400000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182695963/10000000000 : ℝ)^4843 ≤ (43452893273881/100000000000000 : ℝ)^3819 := by
    have hnat : (5182695963 : ℕ)^4843*100000000000000^3819 ≤ 43452893273881^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182695963 10000000000 43452893273881 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1792090327/10000000000 : ℝ)^4843 ≤ (11302149048881/100000000000000 : ℝ)^3819 := by
    have hnat : (1792090327 : ℕ)^4843*100000000000000^3819 ≤ 11302149048881^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792090327 10000000000 11302149048881 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070104383/2000000000 : ℝ), (5182695963/10000000000 : ℝ), (-1792090327/10000000000 : ℝ)] ![(180979830647/400000000000 : ℝ), (43452893273881/100000000000000 : ℝ), (11302149048881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070104383/2000000000 : ℝ)|^4843 ≤ (180979830647/400000000000 : ℝ)^3819
        have hw : |(1070104383/2000000000 : ℝ)|=(1070104383/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182695963/10000000000 : ℝ)|^4843 ≤ (43452893273881/100000000000000 : ℝ)^3819
        have hw : |(5182695963/10000000000 : ℝ)|=(5182695963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1792090327/10000000000 : ℝ)|^4843 ≤ (11302149048881/100000000000000 : ℝ)^3819
        have hw : |(-1792090327/10000000000 : ℝ)|=(1792090327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s4_3 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1048891667/2500000000 : ℝ)*x 0 + (1932290473/5000000000 : ℝ)*x 1 + (4547267083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1048891667/2500000000 : ℝ)^4843 ≤ (4154878719689/12500000000000 : ℝ)^3819 := by
    have hnat : (1048891667 : ℕ)^4843*12500000000000^3819 ≤ 4154878719689^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1048891667 2500000000 4154878719689 12500000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1932290473/5000000000 : ℝ)^4843 ≤ (29949593380727/100000000000000 : ℝ)^3819 := by
    have hnat : (1932290473 : ℕ)^4843*100000000000000^3819 ≤ 29949593380727^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1932290473 5000000000 29949593380727 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4547267083/10000000000 : ℝ)^4843 ≤ (36811376847709/100000000000000 : ℝ)^3819 := by
    have hnat : (4547267083 : ℕ)^4843*100000000000000^3819 ≤ 36811376847709^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547267083 10000000000 36811376847709 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1048891667/2500000000 : ℝ), (1932290473/5000000000 : ℝ), (4547267083/10000000000 : ℝ)] ![(4154878719689/12500000000000 : ℝ), (29949593380727/100000000000000 : ℝ), (36811376847709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1048891667/2500000000 : ℝ)|^4843 ≤ (4154878719689/12500000000000 : ℝ)^3819
        have hw : |(1048891667/2500000000 : ℝ)|=(1048891667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1932290473/5000000000 : ℝ)|^4843 ≤ (29949593380727/100000000000000 : ℝ)^3819
        have hw : |(1932290473/5000000000 : ℝ)|=(1932290473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4547267083/10000000000 : ℝ)|^4843 ≤ (36811376847709/100000000000000 : ℝ)^3819
        have hw : |(4547267083/10000000000 : ℝ)|=(4547267083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s4_4 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-826446787/5000000000 : ℝ)*x 0 + (2592361287/5000000000 : ℝ)*x 1 + (1362743143/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (826446787/5000000000 : ℝ)^4843 ≤ (637544569839/6250000000000 : ℝ)^3819 := by
    have hnat : (826446787 : ℕ)^4843*6250000000000^3819 ≤ 637544569839^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826446787 5000000000 637544569839 6250000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592361287/5000000000 : ℝ)^4843 ≤ (43474441967079/100000000000000 : ℝ)^3819 := by
    have hnat : (2592361287 : ℕ)^4843*100000000000000^3819 ≤ 43474441967079^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592361287 5000000000 43474441967079 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362743143/2500000000 : ℝ)^4843 ≤ (9264968979363/20000000000000 : ℝ)^3819 := by
    have hnat : (1362743143 : ℕ)^4843*20000000000000^3819 ≤ 9264968979363^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362743143 2500000000 9264968979363 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-826446787/5000000000 : ℝ), (2592361287/5000000000 : ℝ), (1362743143/2500000000 : ℝ)] ![(637544569839/6250000000000 : ℝ), (43474441967079/100000000000000 : ℝ), (9264968979363/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-826446787/5000000000 : ℝ)|^4843 ≤ (637544569839/6250000000000 : ℝ)^3819
        have hw : |(-826446787/5000000000 : ℝ)|=(826446787/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592361287/5000000000 : ℝ)|^4843 ≤ (43474441967079/100000000000000 : ℝ)^3819
        have hw : |(2592361287/5000000000 : ℝ)|=(2592361287/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362743143/2500000000 : ℝ)|^4843 ≤ (9264968979363/20000000000000 : ℝ)^3819
        have hw : |(1362743143/2500000000 : ℝ)|=(1362743143/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s4_5 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (527848461/1000000000 : ℝ)*x 0 + (-15238137/100000000 : ℝ)*x 1 + (272548629/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527848461/1000000000 : ℝ)^4843 ≤ (8894772103687/20000000000000 : ℝ)^3819 := by
    have hnat : (527848461 : ℕ)^4843*20000000000000^3819 ≤ 8894772103687^3819*1000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527848461 1000000000 8894772103687 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15238137/100000000 : ℝ)^4843 ≤ (9201294483377/100000000000000 : ℝ)^3819 := by
    have hnat : (15238137 : ℕ)^4843*100000000000000^3819 ≤ 9201294483377^3819*100000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15238137 100000000 9201294483377 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272548629/500000000 : ℝ)^4843 ≤ (5790605622879/12500000000000 : ℝ)^3819 := by
    have hnat : (272548629 : ℕ)^4843*12500000000000^3819 ≤ 5790605622879^3819*500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272548629 500000000 5790605622879 12500000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527848461/1000000000 : ℝ), (-15238137/100000000 : ℝ), (272548629/500000000 : ℝ)] ![(8894772103687/20000000000000 : ℝ), (9201294483377/100000000000000 : ℝ), (5790605622879/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527848461/1000000000 : ℝ)|^4843 ≤ (8894772103687/20000000000000 : ℝ)^3819
        have hw : |(527848461/1000000000 : ℝ)|=(527848461/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15238137/100000000 : ℝ)|^4843 ≤ (9201294483377/100000000000000 : ℝ)^3819
        have hw : |(-15238137/100000000 : ℝ)|=(15238137/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272548629/500000000 : ℝ)|^4843 ≤ (5790605622879/12500000000000 : ℝ)^3819
        have hw : |(272548629/500000000 : ℝ)|=(272548629/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s4_6 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639242299/5000000000 : ℝ)*x 0 + (5450972609/10000000000 : ℝ)*x 1 + (-60952547/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639242299/5000000000 : ℝ)^4843 ≤ (44473860390219/100000000000000 : ℝ)^3819 := by
    have hnat : (2639242299 : ℕ)^4843*100000000000000^3819 ≤ 44473860390219^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639242299 5000000000 44473860390219 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450972609/10000000000 : ℝ)^4843 ≤ (4632484529557/10000000000000 : ℝ)^3819 := by
    have hnat : (5450972609 : ℕ)^4843*10000000000000^3819 ≤ 4632484529557^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450972609 10000000000 4632484529557 10000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (60952547/400000000 : ℝ)^4843 ≤ (4600647145971/50000000000000 : ℝ)^3819 := by
    have hnat : (60952547 : ℕ)^4843*50000000000000^3819 ≤ 4600647145971^3819*400000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      60952547 400000000 4600647145971 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639242299/5000000000 : ℝ), (5450972609/10000000000 : ℝ), (-60952547/400000000 : ℝ)] ![(44473860390219/100000000000000 : ℝ), (4632484529557/10000000000000 : ℝ), (4600647145971/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639242299/5000000000 : ℝ)|^4843 ≤ (44473860390219/100000000000000 : ℝ)^3819
        have hw : |(2639242299/5000000000 : ℝ)|=(2639242299/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450972609/10000000000 : ℝ)|^4843 ≤ (4632484529557/10000000000000 : ℝ)^3819
        have hw : |(5450972609/10000000000 : ℝ)|=(5450972609/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-60952547/400000000 : ℝ)|^4843 ≤ (4600647145971/50000000000000 : ℝ)^3819
        have hw : |(-60952547/400000000 : ℝ)|=(60952547/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s4_7 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4195735343/10000000000 : ℝ)*x 0 + (4542148413/10000000000 : ℝ)*x 1 + (773950731/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4195735343/10000000000 : ℝ)^4843 ≤ (33240724390211/100000000000000 : ℝ)^3819 := by
    have hnat : (4195735343 : ℕ)^4843*100000000000000^3819 ≤ 33240724390211^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4195735343 10000000000 33240724390211 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4542148413/10000000000 : ℝ)^4843 ≤ (574356829699/1562500000000 : ℝ)^3819 := by
    have hnat : (4542148413 : ℕ)^4843*1562500000000^3819 ≤ 574356829699^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542148413 10000000000 574356829699 1562500000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (773950731/2000000000 : ℝ)^4843 ≤ (30000438501151/100000000000000 : ℝ)^3819 := by
    have hnat : (773950731 : ℕ)^4843*100000000000000^3819 ≤ 30000438501151^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      773950731 2000000000 30000438501151 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4195735343/10000000000 : ℝ), (4542148413/10000000000 : ℝ), (773950731/2000000000 : ℝ)] ![(33240724390211/100000000000000 : ℝ), (574356829699/1562500000000 : ℝ), (30000438501151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4195735343/10000000000 : ℝ)|^4843 ≤ (33240724390211/100000000000000 : ℝ)^3819
        have hw : |(4195735343/10000000000 : ℝ)|=(4195735343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4542148413/10000000000 : ℝ)|^4843 ≤ (574356829699/1562500000000 : ℝ)^3819
        have hw : |(4542148413/10000000000 : ℝ)|=(4542148413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(773950731/2000000000 : ℝ)|^4843 ≤ (30000438501151/100000000000000 : ℝ)^3819
        have hw : |(773950731/2000000000 : ℝ)|=(773950731/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1631_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2039/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10559/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2113/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1019/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2039/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10559/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2039/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10559/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2039/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10559/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2039/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10559/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2039/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10559/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2039/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10559/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10559/100000 : ℝ) ^ (4839/1024 : ℝ) ≤ (1216229660605633/50000000000000000000 : ℝ) := by
    have hpowers : (10559/100000 : ℝ)^4839 ≤ (1216229660605633/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10559 : ℕ)^4839*50000000000000000000^1024 ≤ 1216229660605633^1024*100000^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10559 100000 1216229660605633 50000000000000000000 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10559/100000 : ℝ)) (X := (1216229660605633/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2039/12500 : ℝ) ^ (4839/1024 : ℝ) ≤ (2374352370779447/12500000000000000000 : ℝ) := by
    have hpowers : (2039/12500 : ℝ)^4839 ≤ (2374352370779447/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2039 : ℕ)^4839*12500000000000000000^1024 ≤ 2374352370779447^1024*12500^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2039 12500 2374352370779447 12500000000000000000 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2039/12500 : ℝ)) (X := (2374352370779447/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001216229660605633/25000000000000000000 : ℝ) ≤ (10000102946500479/10000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (25001216229660605633/25000000000000000000 : ℝ)^1024 ≤ (10000102946500479/10000000000000000 : ℝ)^4839 := by
      have hnat : (25001216229660605633 : ℕ)^1024*10000000000000000^4839 ≤ 10000102946500479^4839*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001216229660605633 25000000000000000000 10000102946500479 10000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000102946500479/10000000000000000 : ℝ)) (X := (25001216229660605633/25000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50010713639143723421/50000000000000000000 : ℝ) ≤ (1250056674106001/1250000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (50010713639143723421/50000000000000000000 : ℝ)^1024 ≤ (1250056674106001/1250000000000000 : ℝ)^4839 := by
      have hnat : (50010713639143723421 : ℕ)^1024*1250000000000000^4839 ≤ 1250056674106001^4839*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010713639143723421 50000000000000000000 1250056674106001 1250000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250056674106001/1250000000000000 : ℝ)) (X := (50010713639143723421/50000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6252374352370779447/6250000000000000000 : ℝ) ≤ (10000803839195537/10000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (6252374352370779447/6250000000000000000 : ℝ)^1024 ≤ (10000803839195537/10000000000000000 : ℝ)^4839 := by
      have hnat : (6252374352370779447 : ℕ)^1024*10000000000000000^4839 ≤ 10000803839195537^4839*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252374352370779447 6250000000000000000 10000803839195537 10000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000803839195537/10000000000000000 : ℝ)) (X := (6252374352370779447/6250000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1216229660605633/50000000000000000000 : ℝ) ≤ ((11504638305050027653/11506000000000000000 : ℝ)+2*(350446347529/575300000000000 : ℝ)*(10559/100000 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (11504638305050027653/11506000000000000000 : ℝ)+2*(350446347529/575300000000000 : ℝ)*(10559/100000 : ℝ)=(10000102946500479/10000000000000000 : ℝ) by norm_num, show 1+2*(1216229660605633/50000000000000000000 : ℝ)=(25001216229660605633/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2374352370779447/12500000000000000000 : ℝ)+(1216229660605633/50000000000000000000 : ℝ) ≤ ((11504638305050027653/11506000000000000000 : ℝ)+(350446347529/575300000000000 : ℝ)*((2039/12500 : ℝ)+(10559/100000 : ℝ)))^(4839/1024 : ℝ) := by
    rw [show (11504638305050027653/11506000000000000000 : ℝ)+(350446347529/575300000000000 : ℝ)*((2039/12500 : ℝ)+(10559/100000 : ℝ))=(1250056674106001/1250000000000000 : ℝ) by norm_num, show 1+(2374352370779447/12500000000000000000 : ℝ)+(1216229660605633/50000000000000000000 : ℝ)=(50010713639143723421/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2374352370779447/12500000000000000000 : ℝ) ≤ ((11504638305050027653/11506000000000000000 : ℝ)+2*(350446347529/575300000000000 : ℝ)*(2039/12500 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (11504638305050027653/11506000000000000000 : ℝ)+2*(350446347529/575300000000000 : ℝ)*(2039/12500 : ℝ)=(10000803839195537/10000000000000000 : ℝ) by norm_num, show 1+2*(2374352370779447/12500000000000000000 : ℝ)=(6252374352370779447/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (11504638305050027653/11506000000000000000 : ℝ)*(X 1 0+X 2 0)+(350446347529/575300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (10559/100000 : ℝ)) (hi := (2039/12500 : ℝ)) (c := (11504638305050027653/11506000000000000000 : ℝ)) (alpha := (350446347529/575300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (11504638305050027653/11506000000000000000 : ℝ)*(X 0 1+X 2 1)+(350446347529/575300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (10559/100000 : ℝ)) (hi := (2039/12500 : ℝ)) (c := (11504638305050027653/11506000000000000000 : ℝ)) (alpha := (350446347529/575300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (11504638305050027653/11506000000000000000 : ℝ)*(X 0 2+X 1 2)+(350446347529/575300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (10559/100000 : ℝ)) (hi := (2039/12500 : ℝ)) (c := (11504638305050027653/11506000000000000000 : ℝ)) (alpha := (350446347529/575300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-826413251/5000000000 : ℝ)*X 0 0+(2726510209/5000000000 : ℝ)*X 0 1+(5182696199/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350522003/10000000000 : ℝ)*X 1 0+(-35841807/200000000 : ℝ)*X 1 1+(5182695857/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070104383/2000000000 : ℝ)*X 2 0+(5182695963/10000000000 : ℝ)*X 2 1+(-1792090327/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1048891667/2500000000 : ℝ)*X 0 0+(1932290473/5000000000 : ℝ)*X 0 1+(4547267083/10000000000 : ℝ)*X 0 2+(1048891667/2500000000 : ℝ)*X 1 0+(1932290473/5000000000 : ℝ)*X 1 1+(4547267083/10000000000 : ℝ)*X 1 2+(1048891667/2500000000 : ℝ)*X 2 0+(1932290473/5000000000 : ℝ)*X 2 1+(4547267083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-826446787/5000000000 : ℝ)*X 0 0+(2592361287/5000000000 : ℝ)*X 0 1+(1362743143/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((527848461/1000000000 : ℝ)*X 1 0+(-15238137/100000000 : ℝ)*X 1 1+(272548629/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2639242299/5000000000 : ℝ)*X 2 0+(5450972609/10000000000 : ℝ)*X 2 1+(-60952547/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4195735343/10000000000 : ℝ)*X 0 0+(4542148413/10000000000 : ℝ)*X 0 1+(773950731/2000000000 : ℝ)*X 0 2+(4195735343/10000000000 : ℝ)*X 1 0+(4542148413/10000000000 : ℝ)*X 1 1+(773950731/2000000000 : ℝ)*X 1 2+(4195735343/10000000000 : ℝ)*X 2 0+(4542148413/10000000000 : ℝ)*X 2 1+(773950731/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (599481418575358440418390791/57530000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1725191669/100000000000000 : ℝ)*(base19) + (691517913/50000000000000 : ℝ)*(base23) + (75258729/50000000000000 : ℝ)*(lower2) + (295772103/100000000000000 : ℝ)*(upper3) + (12695291/12500000000000 : ℝ)*(upper5) + (258205744713751/10000000000000 : ℝ)*(major0) + (258205744713751/10000000000000 : ℝ)*(major1) + (258205744713751/10000000000000 : ℝ)*(major2) + (3699279134771807/100000000000000 : ℝ)*(sp0) + (3699292647199563/100000000000000 : ℝ)*(sp1) + (1849646494677703/50000000000000 : ℝ)*(sp2) + (366202490214751/25000000000000 : ℝ)*(sp3) + (609504777/4000000000000 : ℝ)*(sp4) + (10213680541/100000000000000 : ℝ)*(sp7) + (183102521817443/12500000000000 : ℝ)*(f.failure) + (57801474568613/1562500000000 : ℝ)*(f.sum) + (6434567799241/1150600000000000000000000000 : ℝ)*base66 + (450833298380356403/115060000000000000000000000000000 : ℝ)*base67 + (357548448077863597/115060000000000000000000000000000 : ℝ)*base70 + (279762155849496403/115060000000000000000000000000000 : ℝ)*base71 + (1241932274193/5753000000000000000000000000 : ℝ)*base74 + (23111706884256403/115060000000000000000000000000000 : ℝ)*base75 + (107211985533563597/115060000000000000000000000000000 : ℝ)*base78 + (394652871408236403/115060000000000000000000000000000 : ℝ)*base79 + (20262401680967/5753000000000000000000000000 : ℝ)*base82 + (2313411/312500000000000000000 : ℝ)*base90 + (2313411/312500000000000000000 : ℝ)*base92 + (2313411/312500000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (79381721908013703547917/14382500000000000000000000000 : ℝ) := by norm_num
    linear_combination (832379983/100000000000000 : ℝ)*(base19) + (875750107/100000000000000 : ℝ)*(base23) + (126281207/50000000000000 : ℝ)*(lower1) + (129094211/100000000000000 : ℝ)*(upper3) + (9611611/50000000000000 : ℝ)*(lower4) + (54801311/50000000000000 : ℝ)*(upper5) + (655384554943883/25000000000000 : ℝ)*(major0) + (655384554943883/25000000000000 : ℝ)*(major1) + (655384554943883/25000000000000 : ℝ)*(major2) + (141882357/12500000000000 : ℝ)*(sp2) + (469482293553867/12500000000000 : ℝ)*(sp4) + (469482189506369/12500000000000 : ℝ)*(sp5) + (938964084405493/25000000000000 : ℝ)*(sp6) + (29744358142851/2000000000000 : ℝ)*(sp7) + (29744358142851/2000000000000 : ℝ)*(f.failure) + (469482293553867/12500000000000 : ℝ)*(f.sum) + (7262240711069/14382500000000000000000000000 : ℝ)*base65 + (243612893928236599/287650000000000000000000000000000 : ℝ)*base67 + (2264978506905963401/287650000000000000000000000000000 : ℝ)*base70 + (2920931461565163401/287650000000000000000000000000000 : ℝ)*base72 + (24590557831661/14382500000000000000000000000 : ℝ)*base74 + (4102842080978836599/287650000000000000000000000000000 : ℝ)*base75 + (873832202331563401/287650000000000000000000000000000 : ℝ)*base78 + (1691063663376436599/287650000000000000000000000000000 : ℝ)*base79 + (94339016370321/14382500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (583373/50000000000000000000 : ℝ)*base89 + (583373/50000000000000000000 : ℝ)*base91 + (583373/50000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1631_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2039/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10559/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2113/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1631_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1631_s5_0 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-66113331/400000000 : ℝ)*x 0 + (545299371/1000000000 : ℝ)*x 1 + (323919893/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66113331/400000000 : ℝ)^4843 ≤ (10200241208229/100000000000000 : ℝ)^3819 := by
    have hnat : (66113331 : ℕ)^4843*100000000000000^3819 ≤ 10200241208229^3819*400000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66113331 400000000 10200241208229 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (545299371/1000000000 : ℝ)^4843 ≤ (46346628130047/100000000000000 : ℝ)^3819 := by
    have hnat : (545299371 : ℕ)^4843*100000000000000^3819 ≤ 46346628130047^3819*1000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      545299371 1000000000 46346628130047 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323919893/625000000 : ℝ)^4843 ≤ (43453130640419/100000000000000 : ℝ)^3819 := by
    have hnat : (323919893 : ℕ)^4843*100000000000000^3819 ≤ 43453130640419^3819*625000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323919893 625000000 43453130640419 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-66113331/400000000 : ℝ), (545299371/1000000000 : ℝ), (323919893/625000000 : ℝ)] ![(10200241208229/100000000000000 : ℝ), (46346628130047/100000000000000 : ℝ), (43453130640419/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-66113331/400000000 : ℝ)|^4843 ≤ (10200241208229/100000000000000 : ℝ)^3819
        have hw : |(-66113331/400000000 : ℝ)|=(66113331/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(545299371/1000000000 : ℝ)|^4843 ≤ (46346628130047/100000000000000 : ℝ)^3819
        have hw : |(545299371/1000000000 : ℝ)|=(545299371/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323919893/625000000 : ℝ)|^4843 ≤ (43453130640419/100000000000000 : ℝ)^3819
        have hw : |(323919893/625000000 : ℝ)|=(323919893/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s5_1 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675257177/5000000000 : ℝ)*x 0 + (-1792070813/10000000000 : ℝ)*x 1 + (1295679567/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675257177/5000000000 : ℝ)^4843 ≤ (45244876580953/100000000000000 : ℝ)^3819 := by
    have hnat : (2675257177 : ℕ)^4843*100000000000000^3819 ≤ 45244876580953^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675257177 5000000000 45244876580953 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1792070813/10000000000 : ℝ)^4843 ≤ (1130199298169/10000000000000 : ℝ)^3819 := by
    have hnat : (1792070813 : ℕ)^4843*10000000000000^3819 ≤ 1130199298169^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792070813 10000000000 1130199298169 10000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1295679567/2500000000 : ℝ)^4843 ≤ (43453130427773/100000000000000 : ℝ)^3819 := by
    have hnat : (1295679567 : ℕ)^4843*100000000000000^3819 ≤ 43453130427773^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295679567 2500000000 43453130427773 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675257177/5000000000 : ℝ), (-1792070813/10000000000 : ℝ), (1295679567/2500000000 : ℝ)] ![(45244876580953/100000000000000 : ℝ), (1130199298169/10000000000000 : ℝ), (43453130427773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675257177/5000000000 : ℝ)|^4843 ≤ (45244876580953/100000000000000 : ℝ)^3819
        have hw : |(2675257177/5000000000 : ℝ)|=(2675257177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1792070813/10000000000 : ℝ)|^4843 ≤ (1130199298169/10000000000000 : ℝ)^3819
        have hw : |(-1792070813/10000000000 : ℝ)|=(1792070813/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1295679567/2500000000 : ℝ)|^4843 ≤ (43453130427773/100000000000000 : ℝ)^3819
        have hw : |(1295679567/2500000000 : ℝ)|=(1295679567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s5_2 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337628577/2500000000 : ℝ)*x 0 + (1295679557/2500000000 : ℝ)*x 1 + (-1792070927/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337628577/2500000000 : ℝ)^4843 ≤ (4524487608767/10000000000000 : ℝ)^3819 := by
    have hnat : (1337628577 : ℕ)^4843*10000000000000^3819 ≤ 4524487608767^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337628577 2500000000 4524487608767 10000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1295679557/2500000000 : ℝ)^4843 ≤ (543164125031/1250000000000 : ℝ)^3819 := by
    have hnat : (1295679557 : ℕ)^4843*1250000000000^3819 ≤ 543164125031^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1295679557 2500000000 543164125031 1250000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1792070927/10000000000 : ℝ)^4843 ≤ (11301993893427/100000000000000 : ℝ)^3819 := by
    have hnat : (1792070927 : ℕ)^4843*100000000000000^3819 ≤ 11301993893427^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1792070927 10000000000 11301993893427 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337628577/2500000000 : ℝ), (1295679557/2500000000 : ℝ), (-1792070927/10000000000 : ℝ)] ![(4524487608767/10000000000000 : ℝ), (543164125031/1250000000000 : ℝ), (11301993893427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337628577/2500000000 : ℝ)|^4843 ≤ (4524487608767/10000000000000 : ℝ)^3819
        have hw : |(1337628577/2500000000 : ℝ)|=(1337628577/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1295679557/2500000000 : ℝ)|^4843 ≤ (543164125031/1250000000000 : ℝ)^3819
        have hw : |(1295679557/2500000000 : ℝ)|=(1295679557/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1792070927/10000000000 : ℝ)|^4843 ≤ (11301993893427/100000000000000 : ℝ)^3819
        have hw : |(-1792070927/10000000000 : ℝ)|=(1792070927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s5_3 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2097784923/5000000000 : ℝ)*x 0 + (966160881/2500000000 : ℝ)*x 1 + (2273602033/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097784923/5000000000 : ℝ)^4843 ≤ (33239061685861/100000000000000 : ℝ)^3819 := by
    have hnat : (2097784923 : ℕ)^4843*100000000000000^3819 ≤ 33239061685861^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097784923 5000000000 33239061685861 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (966160881/2500000000 : ℝ)^4843 ≤ (14975104190957/50000000000000 : ℝ)^3819 := by
    have hnat : (966160881 : ℕ)^4843*50000000000000^3819 ≤ 14975104190957^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966160881 2500000000 14975104190957 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2273602033/5000000000 : ℝ)^4843 ≤ (7362145984723/20000000000000 : ℝ)^3819 := by
    have hnat : (2273602033 : ℕ)^4843*20000000000000^3819 ≤ 7362145984723^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2273602033 5000000000 7362145984723 20000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097784923/5000000000 : ℝ), (966160881/2500000000 : ℝ), (2273602033/5000000000 : ℝ)] ![(33239061685861/100000000000000 : ℝ), (14975104190957/50000000000000 : ℝ), (7362145984723/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097784923/5000000000 : ℝ)|^4843 ≤ (33239061685861/100000000000000 : ℝ)^3819
        have hw : |(2097784923/5000000000 : ℝ)|=(2097784923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(966160881/2500000000 : ℝ)|^4843 ≤ (14975104190957/50000000000000 : ℝ)^3819
        have hw : |(966160881/2500000000 : ℝ)|=(966160881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2273602033/5000000000 : ℝ)|^4843 ≤ (7362145984723/20000000000000 : ℝ)^3819
        have hw : |(2273602033/5000000000 : ℝ)|=(2273602033/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s5_4 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-330580023/2000000000 : ℝ)*x 0 + (5184744273/10000000000 : ℝ)*x 1 + (5450946413/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (330580023/2000000000 : ℝ)^4843 ≤ (10200764308567/100000000000000 : ℝ)^3819 := by
    have hnat : (330580023 : ℕ)^4843*100000000000000^3819 ≤ 10200764308567^3819*2000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      330580023 2000000000 10200764308567 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184744273/10000000000 : ℝ)^4843 ≤ (43474672701967/100000000000000 : ℝ)^3819 := by
    have hnat : (5184744273 : ℕ)^4843*100000000000000^3819 ≤ 43474672701967^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184744273 10000000000 43474672701967 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450946413/10000000000 : ℝ)^4843 ≤ (46324562976971/100000000000000 : ℝ)^3819 := by
    have hnat : (5450946413 : ℕ)^4843*100000000000000^3819 ≤ 46324562976971^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450946413 10000000000 46324562976971 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-330580023/2000000000 : ℝ), (5184744273/10000000000 : ℝ), (5450946413/10000000000 : ℝ)] ![(10200764308567/100000000000000 : ℝ), (43474672701967/100000000000000 : ℝ), (46324562976971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-330580023/2000000000 : ℝ)|^4843 ≤ (10200764308567/100000000000000 : ℝ)^3819
        have hw : |(-330580023/2000000000 : ℝ)|=(330580023/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184744273/10000000000 : ℝ)|^4843 ≤ (43474672701967/100000000000000 : ℝ)^3819
        have hw : |(5184744273/10000000000 : ℝ)|=(5184744273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450946413/10000000000 : ℝ)|^4843 ≤ (46324562976971/100000000000000 : ℝ)^3819
        have hw : |(5450946413/10000000000 : ℝ)|=(5450946413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1631_s5_5 (p : ℝ) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2097869361/5000000000 : ℝ)*x 0 + (4542087499/10000000000 : ℝ)*x 1 + (967453447/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097869361/5000000000 : ℝ)^4843 ≤ (33240758338309/100000000000000 : ℝ)^3819 := by
    have hnat : (2097869361 : ℕ)^4843*100000000000000^3819 ≤ 33240758338309^3819*5000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097869361 5000000000 33240758338309 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4542087499/10000000000 : ℝ)^4843 ≤ (18379105977271/50000000000000 : ℝ)^3819 := by
    have hnat : (4542087499 : ℕ)^4843*50000000000000^3819 ≤ 18379105977271^3819*10000000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542087499 10000000000 18379105977271 50000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967453447/2500000000 : ℝ)^4843 ≤ (30001029685421/100000000000000 : ℝ)^3819 := by
    have hnat : (967453447 : ℕ)^4843*100000000000000^3819 ≤ 30001029685421^3819*2500000000^4843 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967453447 2500000000 30001029685421 100000000000000 4843 3819 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4843/1024 : ℝ)) 4843 3819 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097869361/5000000000 : ℝ), (4542087499/10000000000 : ℝ), (967453447/2500000000 : ℝ)] ![(33240758338309/100000000000000 : ℝ), (18379105977271/50000000000000 : ℝ), (30001029685421/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097869361/5000000000 : ℝ)|^4843 ≤ (33240758338309/100000000000000 : ℝ)^3819
        have hw : |(2097869361/5000000000 : ℝ)|=(2097869361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4542087499/10000000000 : ℝ)|^4843 ≤ (18379105977271/50000000000000 : ℝ)^3819
        have hw : |(4542087499/10000000000 : ℝ)|=(4542087499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(967453447/2500000000 : ℝ)|^4843 ≤ (30001029685421/100000000000000 : ℝ)^3819
        have hw : |(967453447/2500000000 : ℝ)|=(967453447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1631_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2113/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (5283/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1019/6250 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1019/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2113/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1019/6250 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2113/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1019/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2113/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1019/6250 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2113/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1019/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2113/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1019/6250 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2113/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2113/20000 : ℝ) ^ (4839/1024 : ℝ) ≤ (1219498995527673/50000000000000000000 : ℝ) := by
    have hpowers : (2113/20000 : ℝ)^4839 ≤ (1219498995527673/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2113 : ℕ)^4839*50000000000000000000^1024 ≤ 1219498995527673^1024*20000^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2113 20000 1219498995527673 50000000000000000000 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2113/20000 : ℝ)) (X := (1219498995527673/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1019/6250 : ℝ) ^ (4839/1024 : ℝ) ≤ (18950836778237221/100000000000000000000 : ℝ) := by
    have hpowers : (1019/6250 : ℝ)^4839 ≤ (18950836778237221/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1019 : ℕ)^4839*100000000000000000000^1024 ≤ 18950836778237221^1024*6250^4839 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1019 6250 18950836778237221 100000000000000000000 4839 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1019/6250 : ℝ)) (X := (18950836778237221/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001219498995527673/25000000000000000000 : ℝ) ≤ (2500025805806157/2500000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (25001219498995527673/25000000000000000000 : ℝ)^1024 ≤ (2500025805806157/2500000000000000 : ℝ)^4839 := by
      have hnat : (25001219498995527673 : ℕ)^1024*2500000000000000^4839 ≤ 2500025805806157^4839*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001219498995527673 25000000000000000000 2500025805806157 2500000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500025805806157/2500000000000000 : ℝ)) (X := (25001219498995527673/25000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100021389834769292567/100000000000000000000 : ℝ) ≤ (5000226300312283/5000000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (100021389834769292567/100000000000000000000 : ℝ)^1024 ≤ (5000226300312283/5000000000000000 : ℝ)^4839 := by
      have hnat : (100021389834769292567 : ℕ)^1024*5000000000000000^4839 ≤ 5000226300312283^4839*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100021389834769292567 100000000000000000000 5000226300312283 5000000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000226300312283/5000000000000000 : ℝ)) (X := (100021389834769292567/100000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018950836778237221/50000000000000000000 : ℝ) ≤ (1250100247253063/1250000000000000 : ℝ) ^ (4839/1024 : ℝ) := by
    have hpowers : (50018950836778237221/50000000000000000000 : ℝ)^1024 ≤ (1250100247253063/1250000000000000 : ℝ)^4839 := by
      have hnat : (50018950836778237221 : ℕ)^1024*1250000000000000^4839 ≤ 1250100247253063^4839*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018950836778237221 50000000000000000000 1250100247253063 1250000000000000 1024 4839 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250100247253063/1250000000000000 : ℝ)) (X := (50018950836778237221/50000000000000000000 : ℝ)) (by norm_num) 4839 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1219498995527673/50000000000000000000 : ℝ) ≤ ((7172901256703181269/7173750000000000000 : ℝ)+2*(174688699969/286950000000000 : ℝ)*(2113/20000 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (7172901256703181269/7173750000000000000 : ℝ)+2*(174688699969/286950000000000 : ℝ)*(2113/20000 : ℝ)=(2500025805806157/2500000000000000 : ℝ) by norm_num, show 1+2*(1219498995527673/50000000000000000000 : ℝ)=(25001219498995527673/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18950836778237221/100000000000000000000 : ℝ)+(1219498995527673/50000000000000000000 : ℝ) ≤ ((7172901256703181269/7173750000000000000 : ℝ)+(174688699969/286950000000000 : ℝ)*((1019/6250 : ℝ)+(2113/20000 : ℝ)))^(4839/1024 : ℝ) := by
    rw [show (7172901256703181269/7173750000000000000 : ℝ)+(174688699969/286950000000000 : ℝ)*((1019/6250 : ℝ)+(2113/20000 : ℝ))=(5000226300312283/5000000000000000 : ℝ) by norm_num, show 1+(18950836778237221/100000000000000000000 : ℝ)+(1219498995527673/50000000000000000000 : ℝ)=(100021389834769292567/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18950836778237221/100000000000000000000 : ℝ) ≤ ((7172901256703181269/7173750000000000000 : ℝ)+2*(174688699969/286950000000000 : ℝ)*(1019/6250 : ℝ))^(4839/1024 : ℝ) := by
    rw [show (7172901256703181269/7173750000000000000 : ℝ)+2*(174688699969/286950000000000 : ℝ)*(1019/6250 : ℝ)=(1250100247253063/1250000000000000 : ℝ) by norm_num, show 1+2*(18950836778237221/100000000000000000000 : ℝ)=(50018950836778237221/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7172901256703181269/7173750000000000000 : ℝ)*(X 1 0+X 2 0)+(174688699969/286950000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (2113/20000 : ℝ)) (hi := (1019/6250 : ℝ)) (c := (7172901256703181269/7173750000000000000 : ℝ)) (alpha := (174688699969/286950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7172901256703181269/7173750000000000000 : ℝ)*(X 0 1+X 2 1)+(174688699969/286950000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (2113/20000 : ℝ)) (hi := (1019/6250 : ℝ)) (c := (7172901256703181269/7173750000000000000 : ℝ)) (alpha := (174688699969/286950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7172901256703181269/7173750000000000000 : ℝ)*(X 0 2+X 1 2)+(174688699969/286950000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4839/1024 : ℝ)) (lo := (2113/20000 : ℝ)) (hi := (1019/6250 : ℝ)) (c := (7172901256703181269/7173750000000000000 : ℝ)) (alpha := (174688699969/286950000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-66113331/400000000 : ℝ)*X 0 0+(545299371/1000000000 : ℝ)*X 0 1+(323919893/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2675257177/5000000000 : ℝ)*X 1 0+(-1792070813/10000000000 : ℝ)*X 1 1+(1295679567/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337628577/2500000000 : ℝ)*X 2 0+(1295679557/2500000000 : ℝ)*X 2 1+(-1792070927/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2097784923/5000000000 : ℝ)*X 0 0+(966160881/2500000000 : ℝ)*X 0 1+(2273602033/5000000000 : ℝ)*X 0 2+(2097784923/5000000000 : ℝ)*X 1 0+(966160881/2500000000 : ℝ)*X 1 1+(2273602033/5000000000 : ℝ)*X 1 2+(2097784923/5000000000 : ℝ)*X 2 0+(966160881/2500000000 : ℝ)*X 2 1+(2273602033/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-330580023/2000000000 : ℝ)*X 0 0+(5184744273/10000000000 : ℝ)*X 0 1+(5450946413/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2097869361/5000000000 : ℝ)*X 0 0+(4542087499/10000000000 : ℝ)*X 0 1+(967453447/2500000000 : ℝ)*X 0 2+(2097869361/5000000000 : ℝ)*X 1 0+(4542087499/10000000000 : ℝ)*X 1 1+(967453447/2500000000 : ℝ)*X 1 2+(2097869361/5000000000 : ℝ)*X 2 0+(4542087499/10000000000 : ℝ)*X 2 1+(967453447/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1631_s5_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22947601824179903788553/4782500000000000000000000000 : ℝ) := by norm_num
    linear_combination (76280597/10000000000000 : ℝ)*(base19) + (685590183/100000000000000 : ℝ)*(base23) + (12147331/50000000000000 : ℝ)*(lower2) + (76628577/50000000000000 : ℝ)*(upper3) + (27268951/100000000000000 : ℝ)*(upper5) + (80703537551011/3125000000000 : ℝ)*(major0) + (80703537551011/3125000000000 : ℝ)*(major1) + (2582513201632353/100000000000000 : ℝ)*(major2) + (28905779732433/781250000000 : ℝ)*(sp0) + (903307312769/24414062500 : ℝ)*(sp1) + (369994683031761/10000000000000 : ℝ)*(sp2) + (45783580373383/3125000000000 : ℝ)*(sp3) + (7710156369/100000000000000 : ℝ)*(sp4) + (4155467183/100000000000000 : ℝ)*(sp5) + (1465078727415439/100000000000000 : ℝ)*(f.failure) + (3699947515907793/100000000000000 : ℝ)*(f.sum) + (7086184429271/1434750000000000000000000000 : ℝ)*base66 + (585800576214623711/89671875000000000000000000000000 : ℝ)*base67 + (4170585675100179043/717375000000000000000000000000000 : ℝ)*base70 + (835330342773501289/89671875000000000000000000000000 : ℝ)*base72 + (17651121072059/2869500000000000000000000000 : ℝ)*base73 + (928211426187695957/717375000000000000000000000000000 : ℝ)*base75 + (96775092790296569/14945312500000000000000000000000 : ℝ)*base78 + (34463812738672487/29890625000000000000000000000000 : ℝ)*base79 + (62588483784337/14347500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (13319297/2500000000000000000000 : ℝ)*base89 + (13319297/2500000000000000000000 : ℝ)*base91 + (11680703/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1631_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2113/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5283/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1631_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1631_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16411/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10469/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5283/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1631_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1631_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1631_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4839/1024 : ℝ) ≤ p) (hpb : p ≤ (4843/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (44067823/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16411/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10469/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5283/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1019/6250 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1631_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
