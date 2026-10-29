-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1335_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:02:45.579279+00:00
-- url     : https://prove2.me/submissions/b71c524e-c6b6-403f-87e8-1fc5f6db0b74

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
theorem support_rectangle_w1335_s3_0 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1024101013/5000000000 : ℝ)*x 0 + (169627411/312500000 : ℝ)*x 1 + (1307646113/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024101013/5000000000 : ℝ)^4295 ≤ (12467954599383/100000000000000 : ℝ)^3271 := by
    have hnat : (1024101013 : ℕ)^4295*100000000000000^3271 ≤ 12467954599383^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024101013 5000000000 12467954599383 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (169627411/312500000 : ℝ)^4295 ≤ (22415367273237/50000000000000 : ℝ)^3271 := by
    have hnat : (169627411 : ℕ)^4295*50000000000000^3271 ≤ 22415367273237^3271*312500000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169627411 312500000 22415367273237 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307646113/2500000000 : ℝ)^4295 ≤ (21350655419381/50000000000000 : ℝ)^3271 := by
    have hnat : (1307646113 : ℕ)^4295*50000000000000^3271 ≤ 21350655419381^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307646113 2500000000 21350655419381 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1024101013/5000000000 : ℝ), (169627411/312500000 : ℝ), (1307646113/2500000000 : ℝ)] ![(12467954599383/100000000000000 : ℝ), (22415367273237/50000000000000 : ℝ), (21350655419381/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1024101013/5000000000 : ℝ)|^4295 ≤ (12467954599383/100000000000000 : ℝ)^3271
        have hw : |(-1024101013/5000000000 : ℝ)|=(1024101013/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(169627411/312500000 : ℝ)|^4295 ≤ (22415367273237/50000000000000 : ℝ)^3271
        have hw : |(169627411/312500000 : ℝ)|=(169627411/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307646113/2500000000 : ℝ)|^4295 ≤ (21350655419381/50000000000000 : ℝ)^3271
        have hw : |(1307646113/2500000000 : ℝ)|=(1307646113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s3_1 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1338235121/2500000000 : ℝ)*x 0 + (-2149153567/10000000000 : ℝ)*x 1 + (5230584537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1338235121/2500000000 : ℝ)^4295 ≤ (880353610843/2000000000000 : ℝ)^3271 := by
    have hnat : (1338235121 : ℕ)^4295*2000000000000^3271 ≤ 880353610843^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1338235121 2500000000 880353610843 2000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2149153567/10000000000 : ℝ)^4295 ≤ (3320251922837/25000000000000 : ℝ)^3271 := by
    have hnat : (2149153567 : ℕ)^4295*25000000000000^3271 ≤ 3320251922837^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149153567 10000000000 3320251922837 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5230584537/10000000000 : ℝ)^4295 ≤ (21350655874959/50000000000000 : ℝ)^3271 := by
    have hnat : (5230584537 : ℕ)^4295*50000000000000^3271 ≤ 21350655874959^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230584537 10000000000 21350655874959 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1338235121/2500000000 : ℝ), (-2149153567/10000000000 : ℝ), (5230584537/10000000000 : ℝ)] ![(880353610843/2000000000000 : ℝ), (3320251922837/25000000000000 : ℝ), (21350655874959/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1338235121/2500000000 : ℝ)|^4295 ≤ (880353610843/2000000000000 : ℝ)^3271
        have hw : |(1338235121/2500000000 : ℝ)|=(1338235121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2149153567/10000000000 : ℝ)|^4295 ≤ (3320251922837/25000000000000 : ℝ)^3271
        have hw : |(-2149153567/10000000000 : ℝ)|=(2149153567/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5230584537/10000000000 : ℝ)|^4295 ≤ (21350655874959/50000000000000 : ℝ)^3271
        have hw : |(5230584537/10000000000 : ℝ)|=(5230584537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s3_2 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676470131/5000000000 : ℝ)*x 0 + (653823099/1250000000 : ℝ)*x 1 + (-1074576763/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676470131/5000000000 : ℝ)^4295 ≤ (22008839072569/50000000000000 : ℝ)^3271 := by
    have hnat : (2676470131 : ℕ)^4295*50000000000000^3271 ≤ 22008839072569^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676470131 5000000000 22008839072569 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653823099/1250000000 : ℝ)^4295 ≤ (5337664310423/12500000000000 : ℝ)^3271 := by
    have hnat : (653823099 : ℕ)^4295*12500000000000^3271 ≤ 5337664310423^3271*1250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653823099 1250000000 5337664310423 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1074576763/5000000000 : ℝ)^4295 ≤ (2656201471733/20000000000000 : ℝ)^3271 := by
    have hnat : (1074576763 : ℕ)^4295*20000000000000^3271 ≤ 2656201471733^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074576763 5000000000 2656201471733 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676470131/5000000000 : ℝ), (653823099/1250000000 : ℝ), (-1074576763/5000000000 : ℝ)] ![(22008839072569/50000000000000 : ℝ), (5337664310423/12500000000000 : ℝ), (2656201471733/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676470131/5000000000 : ℝ)|^4295 ≤ (22008839072569/50000000000000 : ℝ)^3271
        have hw : |(2676470131/5000000000 : ℝ)|=(2676470131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653823099/1250000000 : ℝ)|^4295 ≤ (5337664310423/12500000000000 : ℝ)^3271
        have hw : |(653823099/1250000000 : ℝ)|=(653823099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1074576763/5000000000 : ℝ)|^4295 ≤ (2656201471733/20000000000000 : ℝ)^3271
        have hw : |(-1074576763/5000000000 : ℝ)|=(1074576763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s3_3 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4327344473/10000000000 : ℝ)*x 0 + (2062832497/5000000000 : ℝ)*x 1 + (453823831/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4327344473/10000000000 : ℝ)^4295 ≤ (2080746247881/6250000000000 : ℝ)^3271 := by
    have hnat : (4327344473 : ℕ)^4295*6250000000000^3271 ≤ 2080746247881^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4327344473 10000000000 2080746247881 6250000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2062832497/5000000000 : ℝ)^4295 ≤ (977175984453/3125000000000 : ℝ)^3271 := by
    have hnat : (2062832497 : ℕ)^4295*3125000000000^3271 ≤ 977175984453^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2062832497 5000000000 977175984453 3125000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453823831/1000000000 : ℝ)^4295 ≤ (35438428520317/100000000000000 : ℝ)^3271 := by
    have hnat : (453823831 : ℕ)^4295*100000000000000^3271 ≤ 35438428520317^3271*1000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453823831 1000000000 35438428520317 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4327344473/10000000000 : ℝ), (2062832497/5000000000 : ℝ), (453823831/1000000000 : ℝ)] ![(2080746247881/6250000000000 : ℝ), (977175984453/3125000000000 : ℝ), (35438428520317/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4327344473/10000000000 : ℝ)|^4295 ≤ (2080746247881/6250000000000 : ℝ)^3271
        have hw : |(4327344473/10000000000 : ℝ)|=(4327344473/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2062832497/5000000000 : ℝ)|^4295 ≤ (977175984453/3125000000000 : ℝ)^3271
        have hw : |(2062832497/5000000000 : ℝ)|=(2062832497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(453823831/1000000000 : ℝ)|^4295 ≤ (35438428520317/100000000000000 : ℝ)^3271
        have hw : |(453823831/1000000000 : ℝ)|=(453823831/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s3_4 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-512055439/2500000000 : ℝ)*x 0 + (5231410981/10000000000 : ℝ)*x 1 + (217089823/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (512055439/2500000000 : ℝ)^4295 ≤ (12468112299779/100000000000000 : ℝ)^3271 := by
    have hnat : (512055439 : ℕ)^4295*100000000000000^3271 ≤ 12468112299779^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      512055439 2500000000 12468112299779 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5231410981/10000000000 : ℝ)^4295 ≤ (42710171016827/100000000000000 : ℝ)^3271 := by
    have hnat : (5231410981 : ℕ)^4295*100000000000000^3271 ≤ 42710171016827^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5231410981 10000000000 42710171016827 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217089823/400000000 : ℝ)^4295 ≤ (11205429166259/25000000000000 : ℝ)^3271 := by
    have hnat : (217089823 : ℕ)^4295*25000000000000^3271 ≤ 11205429166259^3271*400000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217089823 400000000 11205429166259 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-512055439/2500000000 : ℝ), (5231410981/10000000000 : ℝ), (217089823/400000000 : ℝ)] ![(12468112299779/100000000000000 : ℝ), (42710171016827/100000000000000 : ℝ), (11205429166259/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-512055439/2500000000 : ℝ)|^4295 ≤ (12468112299779/100000000000000 : ℝ)^3271
        have hw : |(-512055439/2500000000 : ℝ)|=(512055439/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5231410981/10000000000 : ℝ)|^4295 ≤ (42710171016827/100000000000000 : ℝ)^3271
        have hw : |(5231410981/10000000000 : ℝ)|=(5231410981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(217089823/400000000 : ℝ)|^4295 ≤ (11205429166259/25000000000000 : ℝ)^3271
        have hw : |(217089823/400000000 : ℝ)|=(217089823/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s3_5 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5302110189/10000000000 : ℝ)*x 0 + (-1952492797/10000000000 : ℝ)*x 1 + (2713622897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5302110189/10000000000 : ℝ)^4295 ≤ (43469665359477/100000000000000 : ℝ)^3271 := by
    have hnat : (5302110189 : ℕ)^4295*100000000000000^3271 ≤ 43469665359477^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5302110189 10000000000 43469665359477 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1952492797/10000000000 : ℝ)^4295 ≤ (5854307794023/50000000000000 : ℝ)^3271 := by
    have hnat : (1952492797 : ℕ)^4295*50000000000000^3271 ≤ 5854307794023^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952492797 10000000000 5854307794023 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2713622897/5000000000 : ℝ)^4295 ≤ (11205429759971/25000000000000 : ℝ)^3271 := by
    have hnat : (2713622897 : ℕ)^4295*25000000000000^3271 ≤ 11205429759971^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713622897 5000000000 11205429759971 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5302110189/10000000000 : ℝ), (-1952492797/10000000000 : ℝ), (2713622897/5000000000 : ℝ)] ![(43469665359477/100000000000000 : ℝ), (5854307794023/50000000000000 : ℝ), (11205429759971/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5302110189/10000000000 : ℝ)|^4295 ≤ (43469665359477/100000000000000 : ℝ)^3271
        have hw : |(5302110189/10000000000 : ℝ)|=(5302110189/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1952492797/10000000000 : ℝ)|^4295 ≤ (5854307794023/50000000000000 : ℝ)^3271
        have hw : |(-1952492797/10000000000 : ℝ)|=(1952492797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2713622897/5000000000 : ℝ)|^4295 ≤ (11205429759971/25000000000000 : ℝ)^3271
        have hw : |(2713622897/5000000000 : ℝ)|=(2713622897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s3_6 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651055931/5000000000 : ℝ)*x 0 + (2713622317/5000000000 : ℝ)*x 1 + (-1952492107/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651055931/5000000000 : ℝ)^4295 ≤ (43469683369577/100000000000000 : ℝ)^3271 := by
    have hnat : (2651055931 : ℕ)^4295*100000000000000^3271 ≤ 43469683369577^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651055931 5000000000 43469683369577 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2713622317/5000000000 : ℝ)^4295 ≤ (22410853230391/50000000000000 : ℝ)^3271 := by
    have hnat : (2713622317 : ℕ)^4295*50000000000000^3271 ≤ 22410853230391^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2713622317 5000000000 22410853230391 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1952492107/10000000000 : ℝ)^4295 ≤ (2341722030989/20000000000000 : ℝ)^3271 := by
    have hnat : (1952492107 : ℕ)^4295*20000000000000^3271 ≤ 2341722030989^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1952492107 10000000000 2341722030989 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651055931/5000000000 : ℝ), (2713622317/5000000000 : ℝ), (-1952492107/10000000000 : ℝ)] ![(43469683369577/100000000000000 : ℝ), (22410853230391/50000000000000 : ℝ), (2341722030989/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651055931/5000000000 : ℝ)|^4295 ≤ (43469683369577/100000000000000 : ℝ)^3271
        have hw : |(2651055931/5000000000 : ℝ)|=(2651055931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2713622317/5000000000 : ℝ)|^4295 ≤ (22410853230391/50000000000000 : ℝ)^3271
        have hw : |(2713622317/5000000000 : ℝ)|=(2713622317/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1952492107/10000000000 : ℝ)|^4295 ≤ (2341722030989/20000000000000 : ℝ)^3271
        have hw : |(-1952492107/10000000000 : ℝ)|=(1952492107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s3_7 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2163693131/5000000000 : ℝ)*x 0 + (453651169/1000000000 : ℝ)*x 1 + (412740127/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2163693131/5000000000 : ℝ)^4295 ≤ (16646181056153/50000000000000 : ℝ)^3271 := by
    have hnat : (2163693131 : ℕ)^4295*50000000000000^3271 ≤ 16646181056153^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2163693131 5000000000 16646181056153 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (453651169/1000000000 : ℝ)^4295 ≤ (35420725772503/100000000000000 : ℝ)^3271 := by
    have hnat : (453651169 : ℕ)^4295*100000000000000^3271 ≤ 35420725772503^3271*1000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453651169 1000000000 35420725772503 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (412740127/1000000000 : ℝ)^4295 ≤ (1251476484063/4000000000000 : ℝ)^3271 := by
    have hnat : (412740127 : ℕ)^4295*4000000000000^3271 ≤ 1251476484063^3271*1000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412740127 1000000000 1251476484063 4000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2163693131/5000000000 : ℝ), (453651169/1000000000 : ℝ), (412740127/1000000000 : ℝ)] ![(16646181056153/50000000000000 : ℝ), (35420725772503/100000000000000 : ℝ), (1251476484063/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2163693131/5000000000 : ℝ)|^4295 ≤ (16646181056153/50000000000000 : ℝ)^3271
        have hw : |(2163693131/5000000000 : ℝ)|=(2163693131/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(453651169/1000000000 : ℝ)|^4295 ≤ (35420725772503/100000000000000 : ℝ)^3271
        have hw : |(453651169/1000000000 : ℝ)|=(453651169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(412740127/1000000000 : ℝ)|^4295 ≤ (1251476484063/4000000000000 : ℝ)^3271
        have hw : |(412740127/1000000000 : ℝ)|=(412740127/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s3_8 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-21150229/2500000000 : ℝ)*x 0 + (4577757/8000000 : ℝ)*x 1 + (6056228749/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (21150229/2500000000 : ℝ)^4295 ≤ (94951386641/50000000000000 : ℝ)^3271 := by
    have hnat : (21150229 : ℕ)^4295*50000000000000^3271 ≤ 94951386641^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      21150229 2500000000 94951386641 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4577757/8000000 : ℝ)^4295 ≤ (48047054643679/100000000000000 : ℝ)^3271 := by
    have hnat : (4577757 : ℕ)^4295*100000000000000^3271 ≤ 48047054643679^3271*8000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4577757 8000000 48047054643679 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6056228749/10000000000 : ℝ)^4295 ≤ (8087975401/15625000000 : ℝ)^3271 := by
    have hnat : (6056228749 : ℕ)^4295*15625000000^3271 ≤ 8087975401^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6056228749 10000000000 8087975401 15625000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-21150229/2500000000 : ℝ), (4577757/8000000 : ℝ), (6056228749/10000000000 : ℝ)] ![(94951386641/50000000000000 : ℝ), (48047054643679/100000000000000 : ℝ), (8087975401/15625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-21150229/2500000000 : ℝ)|^4295 ≤ (94951386641/50000000000000 : ℝ)^3271
        have hw : |(-21150229/2500000000 : ℝ)|=(21150229/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4577757/8000000 : ℝ)|^4295 ≤ (48047054643679/100000000000000 : ℝ)^3271
        have hw : |(4577757/8000000 : ℝ)|=(4577757/8000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6056228749/10000000000 : ℝ)|^4295 ≤ (8087975401/15625000000 : ℝ)^3271
        have hw : |(6056228749/10000000000 : ℝ)|=(6056228749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s3_9 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (100923009/1000000000 : ℝ)*x 0 + (-4284706833/10000000000 : ℝ)*x 1 + (6966862743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (100923009/1000000000 : ℝ)^4295 ≤ (4922494324469/100000000000000 : ℝ)^3271 := by
    have hnat : (100923009 : ℕ)^4295*100000000000000^3271 ≤ 4922494324469^3271*1000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100923009 1000000000 4922494324469 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4284706833/10000000000 : ℝ)^4295 ≤ (8215471840967/25000000000000 : ℝ)^3271 := by
    have hnat : (4284706833 : ℕ)^4295*25000000000000^3271 ≤ 8215471840967^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4284706833 10000000000 8215471840967 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6966862743/10000000000 : ℝ)^4295 ≤ (15553904574139/25000000000000 : ℝ)^3271 := by
    have hnat : (6966862743 : ℕ)^4295*25000000000000^3271 ≤ 15553904574139^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6966862743 10000000000 15553904574139 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(100923009/1000000000 : ℝ), (-4284706833/10000000000 : ℝ), (6966862743/10000000000 : ℝ)] ![(4922494324469/100000000000000 : ℝ), (8215471840967/25000000000000 : ℝ), (15553904574139/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(100923009/1000000000 : ℝ)|^4295 ≤ (4922494324469/100000000000000 : ℝ)^3271
        have hw : |(100923009/1000000000 : ℝ)|=(100923009/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-4284706833/10000000000 : ℝ)|^4295 ≤ (8215471840967/25000000000000 : ℝ)^3271
        have hw : |(-4284706833/10000000000 : ℝ)|=(4284706833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6966862743/10000000000 : ℝ)|^4295 ≤ (15553904574139/25000000000000 : ℝ)^3271
        have hw : |(6966862743/10000000000 : ℝ)|=(6966862743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s3_10 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3942377/39062500 : ℝ)*x 0 + (6966903743/10000000000 : ℝ)*x 1 + (-2142323689/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3942377/39062500 : ℝ)^4295 ≤ (307663269153/6250000000000 : ℝ)^3271 := by
    have hnat : (3942377 : ℕ)^4295*6250000000000^3271 ≤ 307663269153^3271*39062500^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3942377 39062500 307663269153 6250000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (6966903743/10000000000 : ℝ)^4295 ≤ (31108049528677/50000000000000 : ℝ)^3271 := by
    have hnat : (6966903743 : ℕ)^4295*50000000000000^3271 ≤ 31108049528677^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6966903743 10000000000 31108049528677 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2142323689/5000000000 : ℝ)^4295 ≤ (32861288619481/100000000000000 : ℝ)^3271 := by
    have hnat : (2142323689 : ℕ)^4295*100000000000000^3271 ≤ 32861288619481^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2142323689 5000000000 32861288619481 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3942377/39062500 : ℝ), (6966903743/10000000000 : ℝ), (-2142323689/5000000000 : ℝ)] ![(307663269153/6250000000000 : ℝ), (31108049528677/50000000000000 : ℝ), (32861288619481/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3942377/39062500 : ℝ)|^4295 ≤ (307663269153/6250000000000 : ℝ)^3271
        have hw : |(3942377/39062500 : ℝ)|=(3942377/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(6966903743/10000000000 : ℝ)|^4295 ≤ (31108049528677/50000000000000 : ℝ)^3271
        have hw : |(6966903743/10000000000 : ℝ)|=(6966903743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2142323689/5000000000 : ℝ)|^4295 ≤ (32861288619481/100000000000000 : ℝ)^3271
        have hw : |(-2142323689/5000000000 : ℝ)|=(2142323689/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s3_11 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (931215269/10000000000 : ℝ)*x 0 + (366209667/625000000 : ℝ)*x 1 + (2768061953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (931215269/10000000000 : ℝ)^4295 ≤ (4429013249143/100000000000000 : ℝ)^3271 := by
    have hnat : (931215269 : ℕ)^4295*100000000000000^3271 ≤ 4429013249143^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      931215269 10000000000 4429013249143 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (366209667/625000000 : ℝ)^4295 ≤ (49564897031811/100000000000000 : ℝ)^3271 := by
    have hnat : (366209667 : ℕ)^4295*100000000000000^3271 ≤ 49564897031811^3271*625000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      366209667 625000000 49564897031811 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2768061953/5000000000 : ℝ)^4295 ≤ (46006089710887/100000000000000 : ℝ)^3271 := by
    have hnat : (2768061953 : ℕ)^4295*100000000000000^3271 ≤ 46006089710887^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768061953 5000000000 46006089710887 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(931215269/10000000000 : ℝ), (366209667/625000000 : ℝ), (2768061953/5000000000 : ℝ)] ![(4429013249143/100000000000000 : ℝ), (49564897031811/100000000000000 : ℝ), (46006089710887/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(931215269/10000000000 : ℝ)|^4295 ≤ (4429013249143/100000000000000 : ℝ)^3271
        have hw : |(931215269/10000000000 : ℝ)|=(931215269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(366209667/625000000 : ℝ)|^4295 ≤ (49564897031811/100000000000000 : ℝ)^3271
        have hw : |(366209667/625000000 : ℝ)|=(366209667/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2768061953/5000000000 : ℝ)|^4295 ≤ (46006089710887/100000000000000 : ℝ)^3271
        have hw : |(2768061953/5000000000 : ℝ)|=(2768061953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1335_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4033/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1961/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (10837/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1877/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4033/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1961/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4033/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1961/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4033/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1961/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4033/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1961/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4033/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1961/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4033/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1961/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1961/20000 : ℝ) ^ (2147/512 : ℝ) ≤ (2949492758540077/50000000000000000000 : ℝ) := by
    have hpowers : (1961/20000 : ℝ)^2147 ≤ (2949492758540077/50000000000000000000 : ℝ)^512 := by
      have hnat : (1961 : ℕ)^2147*50000000000000000000^512 ≤ 2949492758540077^512*20000^2147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1961 20000 2949492758540077 50000000000000000000 2147 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1961/20000 : ℝ)) (X := (2949492758540077/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hpowhi : (4033/25000 : ℝ) ^ (2147/512 : ℝ) ≤ (47593970980742761/100000000000000000000 : ℝ) := by
    have hpowers : (4033/25000 : ℝ)^2147 ≤ (47593970980742761/100000000000000000000 : ℝ)^512 := by
      have hnat : (4033 : ℕ)^2147*100000000000000000000^512 ≤ 47593970980742761^512*25000^2147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4033 25000 47593970980742761 100000000000000000000 2147 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4033/25000 : ℝ)) (X := (47593970980742761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002949492758540077/25000000000000000000 : ℝ) ≤ (10000281336275349/10000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (25002949492758540077/25000000000000000000 : ℝ)^512 ≤ (10000281336275349/10000000000000000 : ℝ)^2147 := by
      have hnat : (25002949492758540077 : ℕ)^512*10000000000000000^2147 ≤ 10000281336275349^2147*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002949492758540077 25000000000000000000 10000281336275349 10000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000281336275349/10000000000000000 : ℝ)) (X := (25002949492758540077/25000000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20010698591299564583/20000000000000000000 : ℝ) ≤ (1250159424877503/1250000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (20010698591299564583/20000000000000000000 : ℝ)^512 ≤ (1250159424877503/1250000000000000 : ℝ)^2147 := by
      have hnat : (20010698591299564583 : ℕ)^512*1250000000000000^2147 ≤ 1250159424877503^2147*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20010698591299564583 20000000000000000000 1250159424877503 1250000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250159424877503/1250000000000000 : ℝ)) (X := (20010698591299564583/20000000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50047593970980742761/50000000000000000000 : ℝ) ≤ (10002269461764699/10000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (50047593970980742761/50000000000000000000 : ℝ)^512 ≤ (10002269461764699/10000000000000000 : ℝ)^2147 := by
      have hnat : (50047593970980742761 : ℕ)^512*10000000000000000^2147 ≤ 10002269461764699^2147*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50047593970980742761 50000000000000000000 10002269461764699 10000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002269461764699/10000000000000000 : ℝ)) (X := (50047593970980742761/50000000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2949492758540077/50000000000000000000 : ℝ) ≤ ((9997200323090099/10000000000000000 : ℝ)+2*(232529297/148000000000 : ℝ)*(1961/20000 : ℝ))^(2147/512 : ℝ) := by
    rw [show (9997200323090099/10000000000000000 : ℝ)+2*(232529297/148000000000 : ℝ)*(1961/20000 : ℝ)=(10000281336275349/10000000000000000 : ℝ) by norm_num, show 1+2*(2949492758540077/50000000000000000000 : ℝ)=(25002949492758540077/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(47593970980742761/100000000000000000000 : ℝ)+(2949492758540077/50000000000000000000 : ℝ) ≤ ((9997200323090099/10000000000000000 : ℝ)+(232529297/148000000000 : ℝ)*((4033/25000 : ℝ)+(1961/20000 : ℝ)))^(2147/512 : ℝ) := by
    rw [show (9997200323090099/10000000000000000 : ℝ)+(232529297/148000000000 : ℝ)*((4033/25000 : ℝ)+(1961/20000 : ℝ))=(1250159424877503/1250000000000000 : ℝ) by norm_num, show 1+(47593970980742761/100000000000000000000 : ℝ)+(2949492758540077/50000000000000000000 : ℝ)=(20010698591299564583/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(47593970980742761/100000000000000000000 : ℝ) ≤ ((9997200323090099/10000000000000000 : ℝ)+2*(232529297/148000000000 : ℝ)*(4033/25000 : ℝ))^(2147/512 : ℝ) := by
    rw [show (9997200323090099/10000000000000000 : ℝ)+2*(232529297/148000000000 : ℝ)*(4033/25000 : ℝ)=(10002269461764699/10000000000000000 : ℝ) by norm_num, show 1+2*(47593970980742761/100000000000000000000 : ℝ)=(50047593970980742761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9997200323090099/10000000000000000 : ℝ)*(X 1 0+X 2 0)+(232529297/148000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (1961/20000 : ℝ)) (hi := (4033/25000 : ℝ)) (c := (9997200323090099/10000000000000000 : ℝ)) (alpha := (232529297/148000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9997200323090099/10000000000000000 : ℝ)*(X 0 1+X 2 1)+(232529297/148000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (1961/20000 : ℝ)) (hi := (4033/25000 : ℝ)) (c := (9997200323090099/10000000000000000 : ℝ)) (alpha := (232529297/148000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9997200323090099/10000000000000000 : ℝ)*(X 0 2+X 1 2)+(232529297/148000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (1961/20000 : ℝ)) (hi := (4033/25000 : ℝ)) (c := (9997200323090099/10000000000000000 : ℝ)) (alpha := (232529297/148000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1024101013/5000000000 : ℝ)*X 0 0+(169627411/312500000 : ℝ)*X 0 1+(1307646113/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1338235121/2500000000 : ℝ)*X 1 0+(-2149153567/10000000000 : ℝ)*X 1 1+(5230584537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676470131/5000000000 : ℝ)*X 2 0+(653823099/1250000000 : ℝ)*X 2 1+(-1074576763/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4327344473/10000000000 : ℝ)*X 0 0+(2062832497/5000000000 : ℝ)*X 0 1+(453823831/1000000000 : ℝ)*X 0 2+(4327344473/10000000000 : ℝ)*X 1 0+(2062832497/5000000000 : ℝ)*X 1 1+(453823831/1000000000 : ℝ)*X 1 2+(4327344473/10000000000 : ℝ)*X 2 0+(2062832497/5000000000 : ℝ)*X 2 1+(453823831/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-512055439/2500000000 : ℝ)*X 0 0+(5231410981/10000000000 : ℝ)*X 0 1+(217089823/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5302110189/10000000000 : ℝ)*X 1 0+(-1952492797/10000000000 : ℝ)*X 1 1+(2713622897/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651055931/5000000000 : ℝ)*X 2 0+(2713622317/5000000000 : ℝ)*X 2 1+(-1952492107/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2163693131/5000000000 : ℝ)*X 0 0+(453651169/1000000000 : ℝ)*X 0 1+(412740127/1000000000 : ℝ)*X 0 2+(2163693131/5000000000 : ℝ)*X 1 0+(453651169/1000000000 : ℝ)*X 1 1+(412740127/1000000000 : ℝ)*X 1 2+(2163693131/5000000000 : ℝ)*X 2 0+(453651169/1000000000 : ℝ)*X 2 1+(412740127/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-21150229/2500000000 : ℝ)*X 0 0+(4577757/8000000 : ℝ)*X 0 1+(6056228749/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((100923009/1000000000 : ℝ)*X 1 0+(-4284706833/10000000000 : ℝ)*X 1 1+(6966862743/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s3_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((3942377/39062500 : ℝ)*X 2 0+(6966903743/10000000000 : ℝ)*X 2 1+(-2142323689/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s3_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((931215269/10000000000 : ℝ)*X 0 0+(366209667/625000000 : ℝ)*X 0 1+(2768061953/5000000000 : ℝ)*X 0 2+(931215269/10000000000 : ℝ)*X 1 0+(366209667/625000000 : ℝ)*X 1 1+(2768061953/5000000000 : ℝ)*X 1 2+(931215269/10000000000 : ℝ)*X 2 0+(366209667/625000000 : ℝ)*X 2 1+(2768061953/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s3_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (135034962738142813426425297/9250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (277884621/50000000000000 : ℝ)*(lower2) + (65988261/25000000000000 : ℝ)*(lower4) + (3743647941132027/100000000000000 : ℝ)*(major0) + (3743647941132027/100000000000000 : ℝ)*(major1) + (3743647941132027/100000000000000 : ℝ)*(major2) + (506347871087503/10000000000000 : ℝ)*(sp0) + (5063476292712743/100000000000000 : ℝ)*(sp1) + (5063482578329773/100000000000000 : ℝ)*(sp2) + (1514881815581/62500000000 : ℝ)*(sp3) + (1083684999/20000000000000 : ℝ)*(sp5) + (1702137549/100000000000000 : ℝ)*(sp7) + (815541877/20000000000000 : ℝ)*(sp8) + (538723339/50000000000000 : ℝ)*(sp9) + (105127321/50000000000000 : ℝ)*(sp10) + (48476252141343/2000000000000 : ℝ)*(f.failure) + (1012696557716883/20000000000000 : ℝ)*(f.sum) + (57986997231/37000000000000000000000000 : ℝ)*base66 + (243201602501024901/37000000000000000000000000000000 : ℝ)*base67 + (127006242506024901/37000000000000000000000000000000 : ℝ)*base69 + (1149454876783975099/37000000000000000000000000000000 : ℝ)*base72 + (47198494383/7400000000000000000000000 : ℝ)*base73 + (151905361056024901/37000000000000000000000000000000 : ℝ)*base75 + (446454633125024901/37000000000000000000000000000000 : ℝ)*base77 + (389706195257024901/37000000000000000000000000000000 : ℝ)*base79 + (242472991723/37000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (436833/100000000000000000000 : ℝ)*base89 + (436833/100000000000000000000 : ℝ)*base91 + (436833/100000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13529736282548616537508107/4625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (107009977/50000000000000 : ℝ)*(lower2) + (1887680012692737/50000000000000 : ℝ)*(major0) + (1887680012692737/50000000000000 : ℝ)*(major1) + (1887680012692737/50000000000000 : ℝ)*(major2) + (969755301/12500000000000 : ℝ)*(sp0) + (1046716849/12500000000000 : ℝ)*(sp1) + (2941749489/50000000000000 : ℝ)*(sp3) + (5106366117553299/100000000000000 : ℝ)*(sp4) + (1021273417459311/20000000000000 : ℝ)*(sp5) + (5106374068690919/100000000000000 : ℝ)*(sp6) + (152771130707781/6250000000000 : ℝ)*(sp7) + (792717819/50000000000000 : ℝ)*(sp8) + (1392340427/100000000000000 : ℝ)*(sp10) + (517404501/100000000000000 : ℝ)*(sp11) + (1222172246113987/50000000000000 : ℝ)*(f.failure) + (5106375461031347/100000000000000 : ℝ)*(f.sum) + (57828638909/7400000000000000000000000 : ℝ)*base66 + (326481378655705631/18500000000000000000000000000000 : ℝ)*base67 + (420617734550705631/18500000000000000000000000000000 : ℝ)*base69 + (10583561964205631/18500000000000000000000000000000 : ℝ)*base71 + (933383199/1480000000000000000000000 : ℝ)*base74 + (63235626787205631/18500000000000000000000000000000 : ℝ)*base75 + (16843753247294369/18500000000000000000000000000000 : ℝ)*base78 + (267085258823705631/18500000000000000000000000000000 : ℝ)*base79 + (138453997989/37000000000000000000000000 : ℝ)*base82 + (1/50000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (14809603/2500000000000000000000 : ℝ)*base90 + (14809603/2500000000000000000000 : ℝ)*base92 + (14809603/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1335_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4033/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1961/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10837/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1877/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1335_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1335_s4_0 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-256215063/1250000000 : ℝ)*x 0 + (1353939333/2500000000 : ℝ)*x 1 + (1310476851/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (256215063/1250000000 : ℝ)^4295 ≤ (1560011633623/12500000000000 : ℝ)^3271 := by
    have hnat : (256215063 : ℕ)^4295*12500000000000^3271 ≤ 1560011633623^3271*1250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      256215063 1250000000 1560011633623 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353939333/2500000000 : ℝ)^4295 ≤ (8939435768931/20000000000000 : ℝ)^3271 := by
    have hnat : (1353939333 : ℕ)^4295*20000000000000^3271 ≤ 8939435768931^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353939333 2500000000 8939435768931 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310476851/2500000000 : ℝ)^4295 ≤ (42822728073853/100000000000000 : ℝ)^3271 := by
    have hnat : (1310476851 : ℕ)^4295*100000000000000^3271 ≤ 42822728073853^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310476851 2500000000 42822728073853 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-256215063/1250000000 : ℝ), (1353939333/2500000000 : ℝ), (1310476851/2500000000 : ℝ)] ![(1560011633623/12500000000000 : ℝ), (8939435768931/20000000000000 : ℝ), (42822728073853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-256215063/1250000000 : ℝ)|^4295 ≤ (1560011633623/12500000000000 : ℝ)^3271
        have hw : |(-256215063/1250000000 : ℝ)|=(256215063/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353939333/2500000000 : ℝ)|^4295 ≤ (8939435768931/20000000000000 : ℝ)^3271
        have hw : |(1353939333/2500000000 : ℝ)|=(1353939333/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310476851/2500000000 : ℝ)|^4295 ≤ (42822728073853/100000000000000 : ℝ)^3271
        have hw : |(1310476851/2500000000 : ℝ)|=(1310476851/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s4_1 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349804073/10000000000 : ℝ)*x 0 + (-1069177501/5000000000 : ℝ)*x 1 + (5241907249/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349804073/10000000000 : ℝ)^4295 ≤ (687247167293/1562500000000 : ℝ)^3271 := by
    have hnat : (5349804073 : ℕ)^4295*1562500000000^3271 ≤ 687247167293^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349804073 10000000000 687247167293 1562500000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1069177501/5000000000 : ℝ)^4295 ≤ (659672743381/5000000000000 : ℝ)^3271 := by
    have hnat : (1069177501 : ℕ)^4295*5000000000000^3271 ≤ 659672743381^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069177501 5000000000 659672743381 5000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5241907249/10000000000 : ℝ)^4295 ≤ (5352840801401/12500000000000 : ℝ)^3271 := by
    have hnat : (5241907249 : ℕ)^4295*12500000000000^3271 ≤ 5352840801401^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241907249 10000000000 5352840801401 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349804073/10000000000 : ℝ), (-1069177501/5000000000 : ℝ), (5241907249/10000000000 : ℝ)] ![(687247167293/1562500000000 : ℝ), (659672743381/5000000000000 : ℝ), (5352840801401/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349804073/10000000000 : ℝ)|^4295 ≤ (687247167293/1562500000000 : ℝ)^3271
        have hw : |(5349804073/10000000000 : ℝ)|=(5349804073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1069177501/5000000000 : ℝ)|^4295 ≤ (659672743381/5000000000000 : ℝ)^3271
        have hw : |(-1069177501/5000000000 : ℝ)|=(1069177501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5241907249/10000000000 : ℝ)|^4295 ≤ (5352840801401/12500000000000 : ℝ)^3271
        have hw : |(5241907249/10000000000 : ℝ)|=(5241907249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s4_2 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668725531/1250000000 : ℝ)*x 0 + (2620953483/5000000000 : ℝ)*x 1 + (-2138355143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668725531/1250000000 : ℝ)^4295 ≤ (21991910297971/50000000000000 : ℝ)^3271 := by
    have hnat : (668725531 : ℕ)^4295*50000000000000^3271 ≤ 21991910297971^3271*1250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668725531 1250000000 21991910297971 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2620953483/5000000000 : ℝ)^4295 ≤ (21411361687771/50000000000000 : ℝ)^3271 := by
    have hnat : (2620953483 : ℕ)^4295*50000000000000^3271 ≤ 21411361687771^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620953483 5000000000 21411361687771 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2138355143/10000000000 : ℝ)^4295 ≤ (13193456009921/100000000000000 : ℝ)^3271 := by
    have hnat : (2138355143 : ℕ)^4295*100000000000000^3271 ≤ 13193456009921^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2138355143 10000000000 13193456009921 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668725531/1250000000 : ℝ), (2620953483/5000000000 : ℝ), (-2138355143/10000000000 : ℝ)] ![(21991910297971/50000000000000 : ℝ), (21411361687771/50000000000000 : ℝ), (13193456009921/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668725531/1250000000 : ℝ)|^4295 ≤ (21991910297971/50000000000000 : ℝ)^3271
        have hw : |(668725531/1250000000 : ℝ)|=(668725531/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2620953483/5000000000 : ℝ)|^4295 ≤ (21411361687771/50000000000000 : ℝ)^3271
        have hw : |(2620953483/5000000000 : ℝ)|=(2620953483/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2138355143/10000000000 : ℝ)|^4295 ≤ (13193456009921/100000000000000 : ℝ)^3271
        have hw : |(-2138355143/10000000000 : ℝ)|=(2138355143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s4_3 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (865653273/2000000000 : ℝ)*x 0 + (4150245441/10000000000 : ℝ)*x 1 + (4513428687/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865653273/2000000000 : ℝ)^4295 ≤ (33301253077247/100000000000000 : ℝ)^3271 := by
    have hnat : (865653273 : ℕ)^4295*100000000000000^3271 ≤ 33301253077247^3271*2000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865653273 2000000000 33301253077247 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4150245441/10000000000 : ℝ)^4295 ≤ (31514484529701/100000000000000 : ℝ)^3271 := by
    have hnat : (4150245441 : ℕ)^4295*100000000000000^3271 ≤ 31514484529701^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4150245441 10000000000 31514484529701 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4513428687/10000000000 : ℝ)^4295 ≤ (7036852475941/20000000000000 : ℝ)^3271 := by
    have hnat : (4513428687 : ℕ)^4295*20000000000000^3271 ≤ 7036852475941^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4513428687 10000000000 7036852475941 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865653273/2000000000 : ℝ), (4150245441/10000000000 : ℝ), (4513428687/10000000000 : ℝ)] ![(33301253077247/100000000000000 : ℝ), (31514484529701/100000000000000 : ℝ), (7036852475941/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865653273/2000000000 : ℝ)|^4295 ≤ (33301253077247/100000000000000 : ℝ)^3271
        have hw : |(865653273/2000000000 : ℝ)|=(865653273/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4150245441/10000000000 : ℝ)|^4295 ≤ (31514484529701/100000000000000 : ℝ)^3271
        have hw : |(4150245441/10000000000 : ℝ)|=(4150245441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4513428687/10000000000 : ℝ)|^4295 ≤ (7036852475941/20000000000000 : ℝ)^3271
        have hw : |(4513428687/10000000000 : ℝ)|=(4513428687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s4_4 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1024867101/5000000000 : ℝ)*x 0 + (5242548357/10000000000 : ℝ)*x 1 + (2707556381/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1024867101/5000000000 : ℝ)^4295 ≤ (2496040516283/20000000000000 : ℝ)^3271 := by
    have hnat : (1024867101 : ℕ)^4295*20000000000000^3271 ≤ 2496040516283^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1024867101 5000000000 2496040516283 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5242548357/10000000000 : ℝ)^4295 ≤ (42829603539341/100000000000000 : ℝ)^3271 := by
    have hnat : (5242548357 : ℕ)^4295*100000000000000^3271 ≤ 42829603539341^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5242548357 10000000000 42829603539341 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2707556381/5000000000 : ℝ)^4295 ≤ (44690193858691/100000000000000 : ℝ)^3271 := by
    have hnat : (2707556381 : ℕ)^4295*100000000000000^3271 ≤ 44690193858691^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707556381 5000000000 44690193858691 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1024867101/5000000000 : ℝ), (5242548357/10000000000 : ℝ), (2707556381/5000000000 : ℝ)] ![(2496040516283/20000000000000 : ℝ), (42829603539341/100000000000000 : ℝ), (44690193858691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1024867101/5000000000 : ℝ)|^4295 ≤ (2496040516283/20000000000000 : ℝ)^3271
        have hw : |(-1024867101/5000000000 : ℝ)|=(1024867101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5242548357/10000000000 : ℝ)|^4295 ≤ (42829603539341/100000000000000 : ℝ)^3271
        have hw : |(5242548357/10000000000 : ℝ)|=(5242548357/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2707556381/5000000000 : ℝ)|^4295 ≤ (44690193858691/100000000000000 : ℝ)^3271
        have hw : |(2707556381/5000000000 : ℝ)|=(2707556381/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s4_5 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530506051/1000000000 : ℝ)*x 0 + (-491287279/2500000000 : ℝ)*x 1 + (5415113147/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530506051/1000000000 : ℝ)^4295 ≤ (43501428779849/100000000000000 : ℝ)^3271 := by
    have hnat : (530506051 : ℕ)^4295*100000000000000^3271 ≤ 43501428779849^3271*1000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530506051 1000000000 43501428779849 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (491287279/2500000000 : ℝ)^4295 ≤ (2952093292683/25000000000000 : ℝ)^3271 := by
    have hnat : (491287279 : ℕ)^4295*25000000000000^3271 ≤ 2952093292683^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491287279 2500000000 2952093292683 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415113147/10000000000 : ℝ)^4295 ≤ (44690198030727/100000000000000 : ℝ)^3271 := by
    have hnat : (5415113147 : ℕ)^4295*100000000000000^3271 ≤ 44690198030727^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415113147 10000000000 44690198030727 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530506051/1000000000 : ℝ), (-491287279/2500000000 : ℝ), (5415113147/10000000000 : ℝ)] ![(43501428779849/100000000000000 : ℝ), (2952093292683/25000000000000 : ℝ), (44690198030727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530506051/1000000000 : ℝ)|^4295 ≤ (43501428779849/100000000000000 : ℝ)^3271
        have hw : |(530506051/1000000000 : ℝ)|=(530506051/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-491287279/2500000000 : ℝ)|^4295 ≤ (2952093292683/25000000000000 : ℝ)^3271
        have hw : |(-491287279/2500000000 : ℝ)|=(491287279/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415113147/10000000000 : ℝ)|^4295 ≤ (44690198030727/100000000000000 : ℝ)^3271
        have hw : |(5415113147/10000000000 : ℝ)|=(5415113147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s4_6 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326265063/2500000000 : ℝ)*x 0 + (2707556579/5000000000 : ℝ)*x 1 + (-1965149453/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326265063/2500000000 : ℝ)^4295 ≤ (43501426001957/100000000000000 : ℝ)^3271 := by
    have hnat : (1326265063 : ℕ)^4295*100000000000000^3271 ≤ 43501426001957^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326265063 2500000000 43501426001957 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2707556579/5000000000 : ℝ)^4295 ≤ (5586274768741/12500000000000 : ℝ)^3271 := by
    have hnat : (2707556579 : ℕ)^4295*12500000000000^3271 ≤ 5586274768741^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2707556579 5000000000 5586274768741 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1965149453/10000000000 : ℝ)^4295 ≤ (11808375829663/100000000000000 : ℝ)^3271 := by
    have hnat : (1965149453 : ℕ)^4295*100000000000000^3271 ≤ 11808375829663^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1965149453 10000000000 11808375829663 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326265063/2500000000 : ℝ), (2707556579/5000000000 : ℝ), (-1965149453/10000000000 : ℝ)] ![(43501426001957/100000000000000 : ℝ), (5586274768741/12500000000000 : ℝ), (11808375829663/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326265063/2500000000 : ℝ)|^4295 ≤ (43501426001957/100000000000000 : ℝ)^3271
        have hw : |(1326265063/2500000000 : ℝ)|=(1326265063/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2707556579/5000000000 : ℝ)|^4295 ≤ (5586274768741/12500000000000 : ℝ)^3271
        have hw : |(2707556579/5000000000 : ℝ)|=(2707556579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1965149453/10000000000 : ℝ)|^4295 ≤ (11808375829663/100000000000000 : ℝ)^3271
        have hw : |(-1965149453/10000000000 : ℝ)|=(1965149453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s4_7 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (86565883/200000000 : ℝ)*x 0 + (282005591/625000000 : ℝ)*x 1 + (518949003/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86565883/200000000 : ℝ)^4295 ≤ (1332061351029/4000000000000 : ℝ)^3271 := by
    have hnat : (86565883 : ℕ)^4295*4000000000000^3271 ≤ 1332061351029^3271*200000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86565883 200000000 1332061351029 4000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (282005591/625000000 : ℝ)^4295 ≤ (4396319353823/12500000000000 : ℝ)^3271 := by
    have hnat : (282005591 : ℕ)^4295*12500000000000^3271 ≤ 4396319353823^3271*625000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      282005591 625000000 4396319353823 12500000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (518949003/1250000000 : ℝ)^4295 ≤ (31527911382643/100000000000000 : ℝ)^3271 := by
    have hnat : (518949003 : ℕ)^4295*100000000000000^3271 ≤ 31527911382643^3271*1250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518949003 1250000000 31527911382643 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86565883/200000000 : ℝ), (282005591/625000000 : ℝ), (518949003/1250000000 : ℝ)] ![(1332061351029/4000000000000 : ℝ), (4396319353823/12500000000000 : ℝ), (31527911382643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86565883/200000000 : ℝ)|^4295 ≤ (1332061351029/4000000000000 : ℝ)^3271
        have hw : |(86565883/200000000 : ℝ)|=(86565883/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(282005591/625000000 : ℝ)|^4295 ≤ (4396319353823/12500000000000 : ℝ)^3271
        have hw : |(282005591/625000000 : ℝ)|=(282005591/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(518949003/1250000000 : ℝ)|^4295 ≤ (31527911382643/100000000000000 : ℝ)^3271
        have hw : |(518949003/1250000000 : ℝ)|=(518949003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1335_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1877/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10837/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11079/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14759/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1877/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10837/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1877/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10837/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1877/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10837/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1877/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10837/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1877/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10837/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1877/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10837/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10837/100000 : ℝ) ^ (2147/512 : ℝ) ≤ (1794968827419601/20000000000000000000 : ℝ) := by
    have hpowers : (10837/100000 : ℝ)^2147 ≤ (1794968827419601/20000000000000000000 : ℝ)^512 := by
      have hnat : (10837 : ℕ)^2147*20000000000000000000^512 ≤ 1794968827419601^512*100000^2147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10837 100000 1794968827419601 20000000000000000000 2147 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10837/100000 : ℝ)) (X := (1794968827419601/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hpowhi : (1877/12500 : ℝ) ^ (2147/512 : ℝ) ≤ (35236769436064687/100000000000000000000 : ℝ) := by
    have hpowers : (1877/12500 : ℝ)^2147 ≤ (35236769436064687/100000000000000000000 : ℝ)^512 := by
      have hnat : (1877 : ℕ)^2147*100000000000000000000^512 ≤ 35236769436064687^512*12500^2147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1877 12500 35236769436064687 100000000000000000000 2147 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1877/12500 : ℝ)) (X := (35236769436064687/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001794968827419601/10000000000000000000 : ℝ) ≤ (10000428021068799/10000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (10001794968827419601/10000000000000000000 : ℝ)^512 ≤ (10000428021068799/10000000000000000 : ℝ)^2147 := by
      have hnat : (10001794968827419601 : ℕ)^512*10000000000000000^2147 ≤ 10000428021068799^2147*10000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001794968827419601 10000000000000000000 10000428021068799 10000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000428021068799/10000000000000000 : ℝ)) (X := (10001794968827419601/10000000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011052903393290673/25000000000000000000 : ℝ) ≤ (10001054147018823/10000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (25011052903393290673/25000000000000000000 : ℝ)^512 ≤ (10001054147018823/10000000000000000 : ℝ)^2147 := by
      have hnat : (25011052903393290673 : ℕ)^512*10000000000000000^2147 ≤ 10001054147018823^2147*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011052903393290673 25000000000000000000 10001054147018823 10000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001054147018823/10000000000000000 : ℝ)) (X := (25011052903393290673/25000000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035236769436064687/50000000000000000000 : ℝ) ≤ (10001680272968847/10000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (50035236769436064687/50000000000000000000 : ℝ)^512 ≤ (10001680272968847/10000000000000000 : ℝ)^2147 := by
      have hnat : (50035236769436064687 : ℕ)^512*10000000000000000^2147 ≤ 10001680272968847^2147*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035236769436064687 50000000000000000000 10001680272968847 10000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001680272968847/10000000000000000 : ℝ)) (X := (50035236769436064687/50000000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1794968827419601/20000000000000000000 : ℝ) ≤ ((2785214536413712723/2786000000000000000 : ℝ)+2*(26088581251/17412500000000 : ℝ)*(10837/100000 : ℝ))^(2147/512 : ℝ) := by
    rw [show (2785214536413712723/2786000000000000000 : ℝ)+2*(26088581251/17412500000000 : ℝ)*(10837/100000 : ℝ)=(10000428021068799/10000000000000000 : ℝ) by norm_num, show 1+2*(1794968827419601/20000000000000000000 : ℝ)=(10001794968827419601/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35236769436064687/100000000000000000000 : ℝ)+(1794968827419601/20000000000000000000 : ℝ) ≤ ((2785214536413712723/2786000000000000000 : ℝ)+(26088581251/17412500000000 : ℝ)*((1877/12500 : ℝ)+(10837/100000 : ℝ)))^(2147/512 : ℝ) := by
    rw [show (2785214536413712723/2786000000000000000 : ℝ)+(26088581251/17412500000000 : ℝ)*((1877/12500 : ℝ)+(10837/100000 : ℝ))=(10001054147018823/10000000000000000 : ℝ) by norm_num, show 1+(35236769436064687/100000000000000000000 : ℝ)+(1794968827419601/20000000000000000000 : ℝ)=(25011052903393290673/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35236769436064687/100000000000000000000 : ℝ) ≤ ((2785214536413712723/2786000000000000000 : ℝ)+2*(26088581251/17412500000000 : ℝ)*(1877/12500 : ℝ))^(2147/512 : ℝ) := by
    rw [show (2785214536413712723/2786000000000000000 : ℝ)+2*(26088581251/17412500000000 : ℝ)*(1877/12500 : ℝ)=(10001680272968847/10000000000000000 : ℝ) by norm_num, show 1+2*(35236769436064687/100000000000000000000 : ℝ)=(50035236769436064687/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2785214536413712723/2786000000000000000 : ℝ)*(X 1 0+X 2 0)+(26088581251/17412500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (10837/100000 : ℝ)) (hi := (1877/12500 : ℝ)) (c := (2785214536413712723/2786000000000000000 : ℝ)) (alpha := (26088581251/17412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2785214536413712723/2786000000000000000 : ℝ)*(X 0 1+X 2 1)+(26088581251/17412500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (10837/100000 : ℝ)) (hi := (1877/12500 : ℝ)) (c := (2785214536413712723/2786000000000000000 : ℝ)) (alpha := (26088581251/17412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2785214536413712723/2786000000000000000 : ℝ)*(X 0 2+X 1 2)+(26088581251/17412500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (10837/100000 : ℝ)) (hi := (1877/12500 : ℝ)) (c := (2785214536413712723/2786000000000000000 : ℝ)) (alpha := (26088581251/17412500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-256215063/1250000000 : ℝ)*X 0 0+(1353939333/2500000000 : ℝ)*X 0 1+(1310476851/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349804073/10000000000 : ℝ)*X 1 0+(-1069177501/5000000000 : ℝ)*X 1 1+(5241907249/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668725531/1250000000 : ℝ)*X 2 0+(2620953483/5000000000 : ℝ)*X 2 1+(-2138355143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((865653273/2000000000 : ℝ)*X 0 0+(4150245441/10000000000 : ℝ)*X 0 1+(4513428687/10000000000 : ℝ)*X 0 2+(865653273/2000000000 : ℝ)*X 1 0+(4150245441/10000000000 : ℝ)*X 1 1+(4513428687/10000000000 : ℝ)*X 1 2+(865653273/2000000000 : ℝ)*X 2 0+(4150245441/10000000000 : ℝ)*X 2 1+(4513428687/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1024867101/5000000000 : ℝ)*X 0 0+(5242548357/10000000000 : ℝ)*X 0 1+(2707556381/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((530506051/1000000000 : ℝ)*X 1 0+(-491287279/2500000000 : ℝ)*X 1 1+(5415113147/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326265063/2500000000 : ℝ)*X 2 0+(2707556579/5000000000 : ℝ)*X 2 1+(-1965149453/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((86565883/200000000 : ℝ)*X 0 0+(282005591/625000000 : ℝ)*X 0 1+(518949003/1250000000 : ℝ)*X 0 2+(86565883/200000000 : ℝ)*X 1 0+(282005591/625000000 : ℝ)*X 1 1+(518949003/1250000000 : ℝ)*X 1 2+(86565883/200000000 : ℝ)*X 2 0+(282005591/625000000 : ℝ)*X 2 1+(518949003/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1197246636525959243687481/155468750000000000000000000000 : ℝ) := by norm_num
    linear_combination (1613360951/100000000000000 : ℝ)*(base19) + (818794967/50000000000000 : ℝ)*(base23) + (92753/62500000000 : ℝ)*(lower2) + (3201739/1250000000000 : ℝ)*(upper3) + (15176093/25000000000000 : ℝ)*(lower4) + (132900088555299/3125000000000 : ℝ)*(major0) + (132900088555299/3125000000000 : ℝ)*(major1) + (132900088555299/3125000000000 : ℝ)*(major2) + (2876058875151243/50000000000000 : ℝ)*(sp0) + (1438035130391787/25000000000000 : ℝ)*(sp1) + (1438035124334541/25000000000000 : ℝ)*(sp2) + (1376722288227297/50000000000000 : ℝ)*(sp3) + (24384625613/100000000000000 : ℝ)*(sp4) + (9349730169/50000000000000 : ℝ)*(sp7) + (688365818978733/25000000000000 : ℝ)*(f.failure) + (2876071067464049/50000000000000 : ℝ)*(f.sum) + (1451639389/1741250000000000000000000000 : ℝ)*base66 + (145131792542259573/8706250000000000000000000000000 : ℝ)*base68 + (81052611670040823/8706250000000000000000000000000 : ℝ)*base70 + (118056661319303323/8706250000000000000000000000000 : ℝ)*base72 + (2530047663527/3482500000000000000000000000 : ℝ)*base73 + (131462464344953323/8706250000000000000000000000000 : ℝ)*base76 + (28785619613828323/8706250000000000000000000000000 : ℝ)*base78 + (49917240897153323/8706250000000000000000000000000 : ℝ)*base80 + (4402833071813/3482500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (14491923/1250000000000000000000 : ℝ)*base89 + (14491923/1250000000000000000000 : ℝ)*base91 + (14491923/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43724850069389637348969/6965000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1210187559/100000000000000 : ℝ)*(base19) + (183256553/20000000000000 : ℝ)*(base23) + (3744629/12500000000000 : ℝ)*(upper2) + (10199/4882812500 : ℝ)*(upper3) + (86074403/100000000000000 : ℝ)*(upper5) + (4284437684243599/100000000000000 : ℝ)*(major0) + (4284437684243599/100000000000000 : ℝ)*(major1) + (4284437684243599/100000000000000 : ℝ)*(major2) + (32856074431/100000000000000 : ℝ)*(sp1) + (6182038981/25000000000000 : ℝ)*(sp2) + (1448732500727319/25000000000000 : ℝ)*(sp4) + (2897447968323643/50000000000000 : ℝ)*(sp5) + (5794904358470587/100000000000000 : ℝ)*(sp6) + (86685786134939/3125000000000 : ℝ)*(sp7) + (86685786134939/3125000000000 : ℝ)*(f.failure) + (1448732500727319/25000000000000 : ℝ)*(f.sum) + (525525318329/217656250000000000000000000 : ℝ)*base66 + (63387751901450077/278600000000000000000000000000000 : ℝ)*base67 + (302686194843050077/278600000000000000000000000000000 : ℝ)*base69 + (337504770605650077/278600000000000000000000000000000 : ℝ)*base71 + (11490992029271/3482500000000000000000000000 : ℝ)*base73 + (663258744208349923/278600000000000000000000000000000 : ℝ)*base76 + (1198734564580149923/278600000000000000000000000000000 : ℝ)*base78 + (2348059844421349923/278600000000000000000000000000000 : ℝ)*base80 + (23889911794607/6965000000000000000000000000 : ℝ)*base81 + (64791/156250000000000000000 : ℝ)*base90 + (64791/156250000000000000000 : ℝ)*base92 + (64791/156250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1335_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1877/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10837/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1335_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1335_s5_0 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049984501/10000000000 : ℝ)*x 0 + (676685057/1250000000 : ℝ)*x 1 + (5244010607/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049984501/10000000000 : ℝ)^4295 ≤ (2496440741199/20000000000000 : ℝ)^3271 := by
    have hnat : (2049984501 : ℕ)^4295*20000000000000^3271 ≤ 2496440741199^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049984501 10000000000 2496440741199 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676685057/1250000000 : ℝ)^4295 ≤ (11168126569421/25000000000000 : ℝ)^3271 := by
    have hnat : (676685057 : ℕ)^4295*25000000000000^3271 ≤ 11168126569421^3271*1250000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676685057 1250000000 11168126569421 25000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5244010607/10000000000 : ℝ)^4295 ≤ (42845289994859/100000000000000 : ℝ)^3271 := by
    have hnat : (5244010607 : ℕ)^4295*100000000000000^3271 ≤ 42845289994859^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244010607 10000000000 42845289994859 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049984501/10000000000 : ℝ), (676685057/1250000000 : ℝ), (5244010607/10000000000 : ℝ)] ![(2496440741199/20000000000000 : ℝ), (11168126569421/25000000000000 : ℝ), (42845289994859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049984501/10000000000 : ℝ)|^4295 ≤ (2496440741199/20000000000000 : ℝ)^3271
        have hw : |(-2049984501/10000000000 : ℝ)|=(2049984501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676685057/1250000000 : ℝ)|^4295 ≤ (11168126569421/25000000000000 : ℝ)^3271
        have hw : |(676685057/1250000000 : ℝ)|=(676685057/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5244010607/10000000000 : ℝ)|^4295 ≤ (42845289994859/100000000000000 : ℝ)^3271
        have hw : |(5244010607/10000000000 : ℝ)|=(5244010607/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s5_1 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349223351/10000000000 : ℝ)*x 0 + (-85453719/400000000 : ℝ)*x 1 + (2622005457/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349223351/10000000000 : ℝ)^4295 ≤ (43977549702287/100000000000000 : ℝ)^3271 := by
    have hnat : (5349223351 : ℕ)^4295*100000000000000^3271 ≤ 43977549702287^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349223351 10000000000 43977549702287 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (85453719/400000000 : ℝ)^4295 ≤ (13177156985363/100000000000000 : ℝ)^3271 := by
    have hnat : (85453719 : ℕ)^4295*100000000000000^3271 ≤ 13177156985363^3271*400000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      85453719 400000000 13177156985363 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622005457/5000000000 : ℝ)^4295 ≤ (42845293288381/100000000000000 : ℝ)^3271 := by
    have hnat : (2622005457 : ℕ)^4295*100000000000000^3271 ≤ 42845293288381^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622005457 5000000000 42845293288381 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349223351/10000000000 : ℝ), (-85453719/400000000 : ℝ), (2622005457/5000000000 : ℝ)] ![(43977549702287/100000000000000 : ℝ), (13177156985363/100000000000000 : ℝ), (42845293288381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349223351/10000000000 : ℝ)|^4295 ≤ (43977549702287/100000000000000 : ℝ)^3271
        have hw : |(5349223351/10000000000 : ℝ)|=(5349223351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-85453719/400000000 : ℝ)|^4295 ≤ (13177156985363/100000000000000 : ℝ)^3271
        have hw : |(-85453719/400000000 : ℝ)|=(85453719/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622005457/5000000000 : ℝ)|^4295 ≤ (42845293288381/100000000000000 : ℝ)^3271
        have hw : |(2622005457/5000000000 : ℝ)|=(2622005457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s5_2 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349222471/10000000000 : ℝ)*x 0 + (5244011293/10000000000 : ℝ)*x 1 + (-66760739/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349222471/10000000000 : ℝ)^4295 ≤ (43977540202681/100000000000000 : ℝ)^3271 := by
    have hnat : (5349222471 : ℕ)^4295*100000000000000^3271 ≤ 43977540202681^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349222471 10000000000 43977540202681 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244011293/10000000000 : ℝ)^4295 ≤ (1713811894173/4000000000000 : ℝ)^3271 := by
    have hnat : (5244011293 : ℕ)^4295*4000000000000^3271 ≤ 1713811894173^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244011293 10000000000 1713811894173 4000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (66760739/312500000 : ℝ)^4295 ≤ (2635432487203/20000000000000 : ℝ)^3271 := by
    have hnat : (66760739 : ℕ)^4295*20000000000000^3271 ≤ 2635432487203^3271*312500000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66760739 312500000 2635432487203 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349222471/10000000000 : ℝ), (5244011293/10000000000 : ℝ), (-66760739/312500000 : ℝ)] ![(43977540202681/100000000000000 : ℝ), (1713811894173/4000000000000 : ℝ), (2635432487203/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349222471/10000000000 : ℝ)|^4295 ≤ (43977540202681/100000000000000 : ℝ)^3271
        have hw : |(5349222471/10000000000 : ℝ)|=(5349222471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244011293/10000000000 : ℝ)|^4295 ≤ (1713811894173/4000000000000 : ℝ)^3271
        have hw : |(5244011293/10000000000 : ℝ)|=(5244011293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-66760739/312500000 : ℝ)|^4295 ≤ (2635432487203/20000000000000 : ℝ)^3271
        have hw : |(-66760739/312500000 : ℝ)|=(66760739/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s5_3 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2164211711/5000000000 : ℝ)*x 0 + (4154802153/10000000000 : ℝ)*x 1 + (4508833579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2164211711/5000000000 : ℝ)^4295 ≤ (416285496949/1250000000000 : ℝ)^3271 := by
    have hnat : (2164211711 : ℕ)^4295*1250000000000^3271 ≤ 416285496949^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164211711 5000000000 416285496949 1250000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4154802153/10000000000 : ℝ)^4295 ≤ (1972495328359/6250000000000 : ℝ)^3271 := by
    have hnat : (4154802153 : ℕ)^4295*6250000000000^3271 ≤ 1972495328359^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154802153 10000000000 1972495328359 6250000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4508833579/10000000000 : ℝ)^4295 ≤ (35137234978223/100000000000000 : ℝ)^3271 := by
    have hnat : (4508833579 : ℕ)^4295*100000000000000^3271 ≤ 35137234978223^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4508833579 10000000000 35137234978223 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2164211711/5000000000 : ℝ), (4154802153/10000000000 : ℝ), (4508833579/10000000000 : ℝ)] ![(416285496949/1250000000000 : ℝ), (1972495328359/6250000000000 : ℝ), (35137234978223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2164211711/5000000000 : ℝ)|^4295 ≤ (416285496949/1250000000000 : ℝ)^3271
        have hw : |(2164211711/5000000000 : ℝ)|=(2164211711/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4154802153/10000000000 : ℝ)|^4295 ≤ (1972495328359/6250000000000 : ℝ)^3271
        have hw : |(4154802153/10000000000 : ℝ)|=(4154802153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4508833579/10000000000 : ℝ)|^4295 ≤ (35137234978223/100000000000000 : ℝ)^3271
        have hw : |(4508833579/10000000000 : ℝ)|=(4508833579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s5_4 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2049996217/10000000000 : ℝ)*x 0 + (5244620173/10000000000 : ℝ)*x 1 + (5412868263/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2049996217/10000000000 : ℝ)^4295 ≤ (390071793017/3125000000000 : ℝ)^3271 := by
    have hnat : (2049996217 : ℕ)^4295*3125000000000^3271 ≤ 390071793017^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049996217 10000000000 390071793017 3125000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244620173/10000000000 : ℝ)^4295 ≤ (42851829588849/100000000000000 : ℝ)^3271 := by
    have hnat : (5244620173 : ℕ)^4295*100000000000000^3271 ≤ 42851829588849^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244620173 10000000000 42851829588849 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412868263/10000000000 : ℝ)^4295 ≤ (4466587301737/10000000000000 : ℝ)^3271 := by
    have hnat : (5412868263 : ℕ)^4295*10000000000000^3271 ≤ 4466587301737^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412868263 10000000000 4466587301737 10000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2049996217/10000000000 : ℝ), (5244620173/10000000000 : ℝ), (5412868263/10000000000 : ℝ)] ![(390071793017/3125000000000 : ℝ), (42851829588849/100000000000000 : ℝ), (4466587301737/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2049996217/10000000000 : ℝ)|^4295 ≤ (390071793017/3125000000000 : ℝ)^3271
        have hw : |(-2049996217/10000000000 : ℝ)|=(2049996217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244620173/10000000000 : ℝ)|^4295 ≤ (42851829588849/100000000000000 : ℝ)^3271
        have hw : |(5244620173/10000000000 : ℝ)|=(5244620173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412868263/10000000000 : ℝ)|^4295 ≤ (4466587301737/10000000000000 : ℝ)^3271
        have hw : |(5412868263/10000000000 : ℝ)|=(5412868263/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s5_5 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1061121433/2000000000 : ℝ)*x 0 + (-7685491/39062500 : ℝ)*x 1 + (1082573653/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1061121433/2000000000 : ℝ)^4295 ≤ (8701462944789/20000000000000 : ℝ)^3271 := by
    have hnat : (1061121433 : ℕ)^4295*20000000000000^3271 ≤ 8701462944789^3271*2000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1061121433 2000000000 8701462944789 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7685491/39062500 : ℝ)^4295 ≤ (473072488989/4000000000000 : ℝ)^3271 := by
    have hnat : (7685491 : ℕ)^4295*4000000000000^3271 ≤ 473072488989^3271*39062500^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7685491 39062500 473072488989 4000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082573653/2000000000 : ℝ)^4295 ≤ (139580853247/312500000000 : ℝ)^3271 := by
    have hnat : (1082573653 : ℕ)^4295*312500000000^3271 ≤ 139580853247^3271*2000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082573653 2000000000 139580853247 312500000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1061121433/2000000000 : ℝ), (-7685491/39062500 : ℝ), (1082573653/2000000000 : ℝ)] ![(8701462944789/20000000000000 : ℝ), (473072488989/4000000000000 : ℝ), (139580853247/312500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1061121433/2000000000 : ℝ)|^4295 ≤ (8701462944789/20000000000000 : ℝ)^3271
        have hw : |(1061121433/2000000000 : ℝ)|=(1061121433/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7685491/39062500 : ℝ)|^4295 ≤ (473072488989/4000000000000 : ℝ)^3271
        have hw : |(-7685491/39062500 : ℝ)|=(7685491/39062500 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1082573653/2000000000 : ℝ)|^4295 ≤ (139580853247/312500000000 : ℝ)^3271
        have hw : |(1082573653/2000000000 : ℝ)|=(1082573653/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s5_6 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652803571/5000000000 : ℝ)*x 0 + (2706434143/5000000000 : ℝ)*x 1 + (-1967485697/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652803571/5000000000 : ℝ)^4295 ≤ (8701462895259/20000000000000 : ℝ)^3271 := by
    have hnat : (2652803571 : ℕ)^4295*20000000000000^3271 ≤ 8701462895259^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652803571 5000000000 8701462895259 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2706434143/5000000000 : ℝ)^4295 ≤ (2791617079161/6250000000000 : ℝ)^3271 := by
    have hnat : (2706434143 : ℕ)^4295*6250000000000^3271 ≤ 2791617079161^3271*5000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706434143 5000000000 2791617079161 6250000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1967485697/10000000000 : ℝ)^4295 ≤ (5913406116309/50000000000000 : ℝ)^3271 := by
    have hnat : (1967485697 : ℕ)^4295*50000000000000^3271 ≤ 5913406116309^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1967485697 10000000000 5913406116309 50000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652803571/5000000000 : ℝ), (2706434143/5000000000 : ℝ), (-1967485697/10000000000 : ℝ)] ![(8701462895259/20000000000000 : ℝ), (2791617079161/6250000000000 : ℝ), (5913406116309/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652803571/5000000000 : ℝ)|^4295 ≤ (8701462895259/20000000000000 : ℝ)^3271
        have hw : |(2652803571/5000000000 : ℝ)|=(2652803571/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2706434143/5000000000 : ℝ)|^4295 ≤ (2791617079161/6250000000000 : ℝ)^3271
        have hw : |(2706434143/5000000000 : ℝ)|=(2706434143/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1967485697/10000000000 : ℝ)|^4295 ≤ (5913406116309/50000000000000 : ℝ)^3271
        have hw : |(-1967485697/10000000000 : ℝ)|=(1967485697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1335_s5_7 (p : ℝ) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (865690007/2000000000 : ℝ)*x 0 + (1126890199/2500000000 : ℝ)*x 1 + (4156080863/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (865690007/2000000000 : ℝ)^4295 ≤ (33303108617289/100000000000000 : ℝ)^3271 := by
    have hnat : (865690007 : ℕ)^4295*100000000000000^3271 ≤ 33303108617289^3271*2000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      865690007 2000000000 33303108617289 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1126890199/2500000000 : ℝ)^4295 ≤ (35124211674291/100000000000000 : ℝ)^3271 := by
    have hnat : (1126890199 : ℕ)^4295*100000000000000^3271 ≤ 35124211674291^3271*2500000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126890199 2500000000 35124211674291 100000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4156080863/10000000000 : ℝ)^4295 ≤ (6314535937739/20000000000000 : ℝ)^3271 := by
    have hnat : (4156080863 : ℕ)^4295*20000000000000^3271 ≤ 6314535937739^3271*10000000000^4295 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4156080863 10000000000 6314535937739 20000000000000 4295 3271 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4295/1024 : ℝ)) 4295 3271 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(865690007/2000000000 : ℝ), (1126890199/2500000000 : ℝ), (4156080863/10000000000 : ℝ)] ![(33303108617289/100000000000000 : ℝ), (35124211674291/100000000000000 : ℝ), (6314535937739/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(865690007/2000000000 : ℝ)|^4295 ≤ (33303108617289/100000000000000 : ℝ)^3271
        have hw : |(865690007/2000000000 : ℝ)|=(865690007/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1126890199/2500000000 : ℝ)|^4295 ≤ (35124211674291/100000000000000 : ℝ)^3271
        have hw : |(1126890199/2500000000 : ℝ)|=(1126890199/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4156080863/10000000000 : ℝ)|^4295 ≤ (6314535937739/20000000000000 : ℝ)^3271
        have hw : |(4156080863/10000000000 : ℝ)|=(4156080863/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1335_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2781/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14711/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11079/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11079/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11079/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14759/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11079/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11079/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14759/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11079/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11079/100000 : ℝ) ^ (2147/512 : ℝ) ≤ (4922859938686007/50000000000000000000 : ℝ) := by
    have hpowers : (11079/100000 : ℝ)^2147 ≤ (4922859938686007/50000000000000000000 : ℝ)^512 := by
      have hnat : (11079 : ℕ)^2147*50000000000000000000^512 ≤ 4922859938686007^512*100000^2147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11079 100000 4922859938686007 50000000000000000000 2147 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11079/100000 : ℝ)) (X := (4922859938686007/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hpowhi : (14759/100000 : ℝ) ^ (2147/512 : ℝ) ≤ (16388043315389041/50000000000000000000 : ℝ) := by
    have hpowers : (14759/100000 : ℝ)^2147 ≤ (16388043315389041/50000000000000000000 : ℝ)^512 := by
      have hnat : (14759 : ℕ)^2147*50000000000000000000^512 ≤ 16388043315389041^512*100000^2147 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14759 100000 16388043315389041 50000000000000000000 2147 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14759/100000 : ℝ)) (X := (16388043315389041/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004922859938686007/25000000000000000000 : ℝ) ≤ (625029346941411/625000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (25004922859938686007/25000000000000000000 : ℝ)^512 ≤ (625029346941411/625000000000000 : ℝ)^2147 := by
      have hnat : (25004922859938686007 : ℕ)^512*625000000000000^2147 ≤ 625029346941411^2147*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004922859938686007 25000000000000000000 625029346941411 625000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625029346941411/625000000000000 : ℝ)) (X := (25004922859938686007/25000000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252663862906759381/6250000000000000000 : ℝ) ≤ (2000203249411279/2000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (6252663862906759381/6250000000000000000 : ℝ)^512 ≤ (2000203249411279/2000000000000000 : ℝ)^2147 := by
      have hnat : (6252663862906759381 : ℕ)^512*2000000000000000^2147 ≤ 2000203249411279^2147*6250000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252663862906759381 6250000000000000000 2000203249411279 2000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000203249411279/2000000000000000 : ℝ)) (X := (6252663862906759381/6250000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016388043315389041/25000000000000000000 : ℝ) ≤ (5000781471525107/5000000000000000 : ℝ) ^ (2147/512 : ℝ) := by
    have hpowers : (25016388043315389041/25000000000000000000 : ℝ)^512 ≤ (5000781471525107/5000000000000000 : ℝ)^2147 := by
      have hnat : (25016388043315389041 : ℕ)^512*5000000000000000^2147 ≤ 5000781471525107^2147*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016388043315389041 25000000000000000000 5000781471525107 5000000000000000 512 2147 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000781471525107/5000000000000000 : ℝ)) (X := (25016388043315389041/25000000000000000000 : ℝ)) (by norm_num) 2147 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4922859938686007/50000000000000000000 : ℝ) ≤ ((18394807129039619139/18400000000000000000 : ℝ)+2*(546695993819/368000000000000 : ℝ)*(11079/100000 : ℝ))^(2147/512 : ℝ) := by
    rw [show (18394807129039619139/18400000000000000000 : ℝ)+2*(546695993819/368000000000000 : ℝ)*(11079/100000 : ℝ)=(625029346941411/625000000000000 : ℝ) by norm_num, show 1+2*(4922859938686007/50000000000000000000 : ℝ)=(25004922859938686007/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16388043315389041/50000000000000000000 : ℝ)+(4922859938686007/50000000000000000000 : ℝ) ≤ ((18394807129039619139/18400000000000000000 : ℝ)+(546695993819/368000000000000 : ℝ)*((14759/100000 : ℝ)+(11079/100000 : ℝ)))^(2147/512 : ℝ) := by
    rw [show (18394807129039619139/18400000000000000000 : ℝ)+(546695993819/368000000000000 : ℝ)*((14759/100000 : ℝ)+(11079/100000 : ℝ))=(2000203249411279/2000000000000000 : ℝ) by norm_num, show 1+(16388043315389041/50000000000000000000 : ℝ)+(4922859938686007/50000000000000000000 : ℝ)=(6252663862906759381/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16388043315389041/50000000000000000000 : ℝ) ≤ ((18394807129039619139/18400000000000000000 : ℝ)+2*(546695993819/368000000000000 : ℝ)*(14759/100000 : ℝ))^(2147/512 : ℝ) := by
    rw [show (18394807129039619139/18400000000000000000 : ℝ)+2*(546695993819/368000000000000 : ℝ)*(14759/100000 : ℝ)=(5000781471525107/5000000000000000 : ℝ) by norm_num, show 1+2*(16388043315389041/50000000000000000000 : ℝ)=(25016388043315389041/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18394807129039619139/18400000000000000000 : ℝ)*(X 1 0+X 2 0)+(546695993819/368000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (11079/100000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (18394807129039619139/18400000000000000000 : ℝ)) (alpha := (546695993819/368000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18394807129039619139/18400000000000000000 : ℝ)*(X 0 1+X 2 1)+(546695993819/368000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (11079/100000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (18394807129039619139/18400000000000000000 : ℝ)) (alpha := (546695993819/368000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18394807129039619139/18400000000000000000 : ℝ)*(X 0 2+X 1 2)+(546695993819/368000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2147/512 : ℝ)) (lo := (11079/100000 : ℝ)) (hi := (14759/100000 : ℝ)) (c := (18394807129039619139/18400000000000000000 : ℝ)) (alpha := (546695993819/368000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2049984501/10000000000 : ℝ)*X 0 0+(676685057/1250000000 : ℝ)*X 0 1+(5244010607/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349223351/10000000000 : ℝ)*X 1 0+(-85453719/400000000 : ℝ)*X 1 1+(2622005457/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349222471/10000000000 : ℝ)*X 2 0+(5244011293/10000000000 : ℝ)*X 2 1+(-66760739/312500000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2164211711/5000000000 : ℝ)*X 0 0+(4154802153/10000000000 : ℝ)*X 0 1+(4508833579/10000000000 : ℝ)*X 0 2+(2164211711/5000000000 : ℝ)*X 1 0+(4154802153/10000000000 : ℝ)*X 1 1+(4508833579/10000000000 : ℝ)*X 1 2+(2164211711/5000000000 : ℝ)*X 2 0+(4154802153/10000000000 : ℝ)*X 2 1+(4508833579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2049996217/10000000000 : ℝ)*X 0 0+(5244620173/10000000000 : ℝ)*X 0 1+(5412868263/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1061121433/2000000000 : ℝ)*X 1 0+(-7685491/39062500 : ℝ)*X 1 1+(1082573653/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652803571/5000000000 : ℝ)*X 2 0+(2706434143/5000000000 : ℝ)*X 2 1+(-1967485697/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((865690007/2000000000 : ℝ)*X 0 0+(1126890199/2500000000 : ℝ)*X 0 1+(4156080863/10000000000 : ℝ)*X 0 2+(865690007/2000000000 : ℝ)*X 1 0+(1126890199/2500000000 : ℝ)*X 1 1+(4156080863/10000000000 : ℝ)*X 1 2+(865690007/2000000000 : ℝ)*X 2 0+(1126890199/2500000000 : ℝ)*X 2 1+(4156080863/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1335_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3544947439530890396012363223/460000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1322815863/100000000000000 : ℝ)*(base19) + (468296581/50000000000000 : ℝ)*(base23) + (436839237/100000000000000 : ℝ)*(upper2) + (71243437/12500000000000 : ℝ)*(upper3) + (31041599/25000000000000 : ℝ)*(upper4) + (4362725949933081/100000000000000 : ℝ)*(major0) + (4362725949933081/100000000000000 : ℝ)*(major1) + (4362725949933081/100000000000000 : ℝ)*(major2) + (2950402386067823/50000000000000 : ℝ)*(sp0) + (1475204420614381/25000000000000 : ℝ)*(sp1) + (236032722747209/4000000000000 : ℝ)*(sp2) + (706154749215229/25000000000000 : ℝ)*(sp3) + (14233137741/100000000000000 : ℝ)*(sp4) + (6820425803/50000000000000 : ℝ)*(sp7) + (1412316318856261/50000000000000 : ℝ)*(f.failure) + (5900819005273387/100000000000000 : ℝ)*(f.sum) + (135361964956739/18400000000000000000000000000 : ℝ)*base65 + (6839279036973787259/1840000000000000000000000000000000 : ℝ)*base67 + (9141761097613787259/1840000000000000000000000000000000 : ℝ)*base69 + (2135044153853787259/1840000000000000000000000000000000 : ℝ)*base71 + (15530781744739/18400000000000000000000000000 : ℝ)*base73 + (728377815426212741/1840000000000000000000000000000000 : ℝ)*base76 + (1331160940013787259/1840000000000000000000000000000000 : ℝ)*base77 + (16098900269933787259/1840000000000000000000000000000000 : ℝ)*base79 + (74656294453539/18400000000000000000000000000 : ℝ)*base81 + (14034491/2500000000000000000000 : ℝ)*base89 + (14034491/2500000000000000000000 : ℝ)*base91 + (14034491/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5257250937871517561493453/2500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (405632009/100000000000000 : ℝ)*(base19) + (390907707/100000000000000 : ℝ)*(base23) + (52201137/100000000000000 : ℝ)*(upper3) + (55097/1250000000000 : ℝ)*(lower4) + (20534979/50000000000000 : ℝ)*(upper5) + (549294748507493/12500000000000 : ℝ)*(major0) + (549294748507493/12500000000000 : ℝ)*(major1) + (549294748507493/12500000000000 : ℝ)*(major2) + (3999124941/50000000000000 : ℝ)*(sp1) + (8330948579/100000000000000 : ℝ)*(sp2) + (742950401094067/12500000000000 : ℝ)*(sp4) + (1188718960974129/20000000000000 : ℝ)*(sp5) + (4754875589517/80000000000 : ℝ)*(sp6) + (2845112697270669/100000000000000 : ℝ)*(sp7) + (2845112697270669/100000000000000 : ℝ)*(f.failure) + (742950401094067/12500000000000 : ℝ)*(f.sum) + (217767006571/100000000000000000000000000 : ℝ)*base66 + (8380937249393849/10000000000000000000000000000000 : ℝ)*base67 + (50063226619393849/10000000000000000000000000000000 : ℝ)*base69 + (84203055549393849/10000000000000000000000000000000 : ℝ)*base71 + (154132261671/100000000000000000000000000 : ℝ)*base74 + (49163054430606151/10000000000000000000000000000000 : ℝ)*base76 + (24125353529393849/10000000000000000000000000000000 : ℝ)*base77 + (74329723059393849/10000000000000000000000000000000 : ℝ)*base79 + (396780213229/100000000000000000000000000 : ℝ)*base81 + (7852339/5000000000000000000000 : ℝ)*base89 + (7852339/5000000000000000000000 : ℝ)*base91 + (7852339/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1335_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14759/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11079/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1335_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1335_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4033/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1961/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1335_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1335_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1335_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2147/512 : ℝ) ≤ p) (hpb : p ≤ (4295/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (77226431/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4033/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1961/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2781/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14711/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1335_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
