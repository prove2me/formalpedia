-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1074_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T14:12:55.738189+00:00
-- url     : https://prove2.me/submissions/8e87916a-3700-494e-941d-301498b8c033

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
theorem support_rectangle_w1074_s6_0 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2199787001/10000000000 : ℝ)*x 0 + (1078951627/2000000000 : ℝ)*x 1 + (1316022429/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2199787001/10000000000 : ℝ)^8267 ≤ (1670043478473/12500000000000 : ℝ)^6219 := by
    have hnat : (2199787001 : ℕ)^8267*12500000000000^6219 ≤ 1670043478473^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199787001 10000000000 1670043478473 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078951627/2000000000 : ℝ)^8267 ≤ (44025749790129/100000000000000 : ℝ)^6219 := by
    have hnat : (1078951627 : ℕ)^8267*100000000000000^6219 ≤ 44025749790129^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078951627 2000000000 44025749790129 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316022429/2500000000 : ℝ)^8267 ≤ (2663368897911/6250000000000 : ℝ)^6219 := by
    have hnat : (1316022429 : ℕ)^8267*6250000000000^6219 ≤ 2663368897911^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316022429 2500000000 2663368897911 6250000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2199787001/10000000000 : ℝ), (1078951627/2000000000 : ℝ), (1316022429/2500000000 : ℝ)] ![(1670043478473/12500000000000 : ℝ), (44025749790129/100000000000000 : ℝ), (2663368897911/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2199787001/10000000000 : ℝ)|^8267 ≤ (1670043478473/12500000000000 : ℝ)^6219
        have hw : |(-2199787001/10000000000 : ℝ)|=(2199787001/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078951627/2000000000 : ℝ)|^8267 ≤ (44025749790129/100000000000000 : ℝ)^6219
        have hw : |(1078951627/2000000000 : ℝ)|=(1078951627/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316022429/2500000000 : ℝ)|^8267 ≤ (2663368897911/6250000000000 : ℝ)^6219
        have hw : |(1316022429/2500000000 : ℝ)|=(1316022429/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s6_1 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345095667/10000000000 : ℝ)*x 0 + (-1133044719/5000000000 : ℝ)*x 1 + (5264089783/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345095667/10000000000 : ℝ)^8267 ≤ (43487814166091/100000000000000 : ℝ)^6219 := by
    have hnat : (5345095667 : ℕ)^8267*100000000000000^6219 ≤ 43487814166091^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345095667 10000000000 43487814166091 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1133044719/5000000000 : ℝ)^8267 ≤ (6949141367257/50000000000000 : ℝ)^6219 := by
    have hnat : (1133044719 : ℕ)^8267*50000000000000^6219 ≤ 6949141367257^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1133044719 5000000000 6949141367257 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264089783/10000000000 : ℝ)^8267 ≤ (42613903087567/100000000000000 : ℝ)^6219 := by
    have hnat : (5264089783 : ℕ)^8267*100000000000000^6219 ≤ 42613903087567^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264089783 10000000000 42613903087567 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345095667/10000000000 : ℝ), (-1133044719/5000000000 : ℝ), (5264089783/10000000000 : ℝ)] ![(43487814166091/100000000000000 : ℝ), (6949141367257/50000000000000 : ℝ), (42613903087567/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345095667/10000000000 : ℝ)|^8267 ≤ (43487814166091/100000000000000 : ℝ)^6219
        have hw : |(5345095667/10000000000 : ℝ)|=(5345095667/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1133044719/5000000000 : ℝ)|^8267 ≤ (6949141367257/50000000000000 : ℝ)^6219
        have hw : |(-1133044719/5000000000 : ℝ)|=(1133044719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264089783/10000000000 : ℝ)|^8267 ≤ (42613903087567/100000000000000 : ℝ)^6219
        have hw : |(5264089783/10000000000 : ℝ)|=(5264089783/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s6_2 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1336273861/2500000000 : ℝ)*x 0 + (5264089903/10000000000 : ℝ)*x 1 + (-90643583/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336273861/2500000000 : ℝ)^8267 ≤ (21743905877137/50000000000000 : ℝ)^6219 := by
    have hnat : (1336273861 : ℕ)^8267*50000000000000^6219 ≤ 21743905877137^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336273861 2500000000 21743905877137 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264089903/10000000000 : ℝ)^8267 ≤ (2663369023681/6250000000000 : ℝ)^6219 := by
    have hnat : (5264089903 : ℕ)^8267*6250000000000^6219 ≤ 2663369023681^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264089903 10000000000 2663369023681 6250000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (90643583/400000000 : ℝ)^8267 ≤ (13898283851459/100000000000000 : ℝ)^6219 := by
    have hnat : (90643583 : ℕ)^8267*100000000000000^6219 ≤ 13898283851459^6219*400000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90643583 400000000 13898283851459 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336273861/2500000000 : ℝ), (5264089903/10000000000 : ℝ), (-90643583/400000000 : ℝ)] ![(21743905877137/50000000000000 : ℝ), (2663369023681/6250000000000 : ℝ), (13898283851459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336273861/2500000000 : ℝ)|^8267 ≤ (21743905877137/50000000000000 : ℝ)^6219
        have hw : |(1336273861/2500000000 : ℝ)|=(1336273861/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264089903/10000000000 : ℝ)|^8267 ≤ (2663369023681/6250000000000 : ℝ)^6219
        have hw : |(5264089903/10000000000 : ℝ)|=(5264089903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-90643583/400000000 : ℝ)|^8267 ≤ (13898283851459/100000000000000 : ℝ)^6219
        have hw : |(-90643583/400000000 : ℝ)|=(90643583/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s6_3 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187158039/5000000000 : ℝ)*x 0 + (4247967713/10000000000 : ℝ)*x 1 + (4504466443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187158039/5000000000 : ℝ)^8267 ≤ (16658161624841/50000000000000 : ℝ)^6219 := by
    have hnat : (2187158039 : ℕ)^8267*50000000000000^6219 ≤ 16658161624841^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187158039 5000000000 16658161624841 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4247967713/10000000000 : ℝ)^8267 ≤ (32043230837249/100000000000000 : ℝ)^6219 := by
    have hnat : (4247967713 : ℕ)^8267*100000000000000^6219 ≤ 32043230837249^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247967713 10000000000 32043230837249 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4504466443/10000000000 : ℝ)^8267 ≤ (34640445901417/100000000000000 : ℝ)^6219 := by
    have hnat : (4504466443 : ℕ)^8267*100000000000000^6219 ≤ 34640445901417^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4504466443 10000000000 34640445901417 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187158039/5000000000 : ℝ), (4247967713/10000000000 : ℝ), (4504466443/10000000000 : ℝ)] ![(16658161624841/50000000000000 : ℝ), (32043230837249/100000000000000 : ℝ), (34640445901417/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187158039/5000000000 : ℝ)|^8267 ≤ (16658161624841/50000000000000 : ℝ)^6219
        have hw : |(2187158039/5000000000 : ℝ)|=(2187158039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4247967713/10000000000 : ℝ)|^8267 ≤ (32043230837249/100000000000000 : ℝ)^6219
        have hw : |(4247967713/10000000000 : ℝ)|=(4247967713/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4504466443/10000000000 : ℝ)|^8267 ≤ (34640445901417/100000000000000 : ℝ)^6219
        have hw : |(4504466443/10000000000 : ℝ)|=(4504466443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s6_4 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-549948057/2500000000 : ℝ)*x 0 + (5264419833/10000000000 : ℝ)*x 1 + (674303347/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549948057/2500000000 : ℝ)^8267 ≤ (3340097507061/25000000000000 : ℝ)^6219 := by
    have hnat : (549948057 : ℕ)^8267*25000000000000^6219 ≤ 3340097507061^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549948057 2500000000 3340097507061 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264419833/10000000000 : ℝ)^8267 ≤ (42617454814981/100000000000000 : ℝ)^6219 := by
    have hnat : (5264419833 : ℕ)^8267*100000000000000^6219 ≤ 42617454814981^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264419833 10000000000 42617454814981 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674303347/1250000000 : ℝ)^8267 ≤ (440221551407/1000000000000 : ℝ)^6219 := by
    have hnat : (674303347 : ℕ)^8267*1000000000000^6219 ≤ 440221551407^6219*1250000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674303347 1250000000 440221551407 1000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549948057/2500000000 : ℝ), (5264419833/10000000000 : ℝ), (674303347/1250000000 : ℝ)] ![(3340097507061/25000000000000 : ℝ), (42617454814981/100000000000000 : ℝ), (440221551407/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549948057/2500000000 : ℝ)|^8267 ≤ (3340097507061/25000000000000 : ℝ)^6219
        have hw : |(-549948057/2500000000 : ℝ)|=(549948057/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264419833/10000000000 : ℝ)|^8267 ≤ (42617454814981/100000000000000 : ℝ)^6219
        have hw : |(5264419833/10000000000 : ℝ)|=(5264419833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674303347/1250000000 : ℝ)|^8267 ≤ (440221551407/1000000000000 : ℝ)^6219
        have hw : |(674303347/1250000000 : ℝ)|=(674303347/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s6_5 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312162057/10000000000 : ℝ)*x 0 + (-427150489/2000000000 : ℝ)*x 1 + (2697213411/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312162057/10000000000 : ℝ)^8267 ≤ (5391498551361/12500000000000 : ℝ)^6219 := by
    have hnat : (5312162057 : ℕ)^8267*12500000000000^6219 ≤ 5391498551361^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312162057 10000000000 5391498551361 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (427150489/2000000000 : ℝ)^8267 ≤ (3211463985097/25000000000000 : ℝ)^6219 := by
    have hnat : (427150489 : ℕ)^8267*25000000000000^6219 ≤ 3211463985097^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      427150489 2000000000 3211463985097 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2697213411/5000000000 : ℝ)^8267 ≤ (44022155639713/100000000000000 : ℝ)^6219 := by
    have hnat : (2697213411 : ℕ)^8267*100000000000000^6219 ≤ 44022155639713^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697213411 5000000000 44022155639713 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312162057/10000000000 : ℝ), (-427150489/2000000000 : ℝ), (2697213411/5000000000 : ℝ)] ![(5391498551361/12500000000000 : ℝ), (3211463985097/25000000000000 : ℝ), (44022155639713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312162057/10000000000 : ℝ)|^8267 ≤ (5391498551361/12500000000000 : ℝ)^6219
        have hw : |(5312162057/10000000000 : ℝ)|=(5312162057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-427150489/2000000000 : ℝ)|^8267 ≤ (3211463985097/25000000000000 : ℝ)^6219
        have hw : |(-427150489/2000000000 : ℝ)|=(427150489/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2697213411/5000000000 : ℝ)|^8267 ≤ (44022155639713/100000000000000 : ℝ)^6219
        have hw : |(2697213411/5000000000 : ℝ)|=(2697213411/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s6_6 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062432353/2000000000 : ℝ)*x 0 + (1348606801/2500000000 : ℝ)*x 1 + (-3337113/15625000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062432353/2000000000 : ℝ)^8267 ≤ (8626397051847/20000000000000 : ℝ)^6219 := by
    have hnat : (1062432353 : ℕ)^8267*20000000000000^6219 ≤ 8626397051847^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062432353 2000000000 8626397051847 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1348606801/2500000000 : ℝ)^8267 ≤ (11005539945921/25000000000000 : ℝ)^6219 := by
    have hnat : (1348606801 : ℕ)^8267*25000000000000^6219 ≤ 11005539945921^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1348606801 2500000000 11005539945921 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3337113/15625000 : ℝ)^8267 ≤ (3211463735241/25000000000000 : ℝ)^6219 := by
    have hnat : (3337113 : ℕ)^8267*25000000000000^6219 ≤ 3211463735241^6219*15625000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3337113 15625000 3211463735241 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062432353/2000000000 : ℝ), (1348606801/2500000000 : ℝ), (-3337113/15625000 : ℝ)] ![(8626397051847/20000000000000 : ℝ), (11005539945921/25000000000000 : ℝ), (3211463735241/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062432353/2000000000 : ℝ)|^8267 ≤ (8626397051847/20000000000000 : ℝ)^6219
        have hw : |(1062432353/2000000000 : ℝ)|=(1062432353/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1348606801/2500000000 : ℝ)|^8267 ≤ (11005539945921/25000000000000 : ℝ)^6219
        have hw : |(1348606801/2500000000 : ℝ)|=(1348606801/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3337113/15625000 : ℝ)|^8267 ≤ (3211463735241/25000000000000 : ℝ)^6219
        have hw : |(-3337113/15625000 : ℝ)|=(3337113/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s6_7 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374326239/10000000000 : ℝ)*x 0 + (2251909253/5000000000 : ℝ)*x 1 + (4248617989/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374326239/10000000000 : ℝ)^8267 ≤ (8329106531233/25000000000000 : ℝ)^6219 := by
    have hnat : (4374326239 : ℕ)^8267*25000000000000^6219 ≤ 8329106531233^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374326239 10000000000 8329106531233 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251909253/5000000000 : ℝ)^8267 ≤ (34633822364019/100000000000000 : ℝ)^6219 := by
    have hnat : (2251909253 : ℕ)^8267*100000000000000^6219 ≤ 34633822364019^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251909253 5000000000 34633822364019 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4248617989/10000000000 : ℝ)^8267 ≤ (32049751491063/100000000000000 : ℝ)^6219 := by
    have hnat : (4248617989 : ℕ)^8267*100000000000000^6219 ≤ 32049751491063^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248617989 10000000000 32049751491063 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374326239/10000000000 : ℝ), (2251909253/5000000000 : ℝ), (4248617989/10000000000 : ℝ)] ![(8329106531233/25000000000000 : ℝ), (34633822364019/100000000000000 : ℝ), (32049751491063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374326239/10000000000 : ℝ)|^8267 ≤ (8329106531233/25000000000000 : ℝ)^6219
        have hw : |(4374326239/10000000000 : ℝ)|=(4374326239/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251909253/5000000000 : ℝ)|^8267 ≤ (34633822364019/100000000000000 : ℝ)^6219
        have hw : |(2251909253/5000000000 : ℝ)|=(2251909253/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4248617989/10000000000 : ℝ)|^8267 ≤ (32049751491063/100000000000000 : ℝ)^6219
        have hw : |(4248617989/10000000000 : ℝ)|=(4248617989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1074_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (2813/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14019/100000 : ℝ)*pair X 0 0 := by
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
  have lower0 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11211/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7031/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11211/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7031/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11211/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11211/100000 : ℝ) ^ (4133/1024 : ℝ) ≤ (456129761059549/3125000000000000000 : ℝ) := by
    have hpowers : (11211/100000 : ℝ)^4133 ≤ (456129761059549/3125000000000000000 : ℝ)^1024 := by
      have hnat : (11211 : ℕ)^4133*3125000000000000000^1024 ≤ 456129761059549^1024*100000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11211 100000 456129761059549 3125000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11211/100000 : ℝ)) (X := (456129761059549/3125000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7031/50000 : ℝ) ^ (4133/1024 : ℝ) ≤ (36425449498646631/100000000000000000000 : ℝ) := by
    have hpowers : (7031/50000 : ℝ)^4133 ≤ (36425449498646631/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7031 : ℕ)^4133*100000000000000000000^1024 ≤ 36425449498646631^1024*50000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7031 50000 36425449498646631 100000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7031/50000 : ℝ)) (X := (36425449498646631/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1562956129761059549/1562500000000000000 : ℝ) ≤ (10000723194735131/10000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (1562956129761059549/1562500000000000000 : ℝ)^1024 ≤ (10000723194735131/10000000000000000 : ℝ)^4133 := by
      have hnat : (1562956129761059549 : ℕ)^1024*10000000000000000^4133 ≤ 10000723194735131^4133*1562500000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1562956129761059549 1562500000000000000 10000723194735131 10000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000723194735131/10000000000000000 : ℝ)) (X := (1562956129761059549/1562500000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100051021601852552199/100000000000000000000 : ℝ) ≤ (5000631939234829/5000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (100051021601852552199/100000000000000000000 : ℝ)^1024 ≤ (5000631939234829/5000000000000000 : ℝ)^4133 := by
      have hnat : (100051021601852552199 : ℕ)^1024*5000000000000000^4133 ≤ 5000631939234829^4133*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100051021601852552199 100000000000000000000 5000631939234829 5000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000631939234829/5000000000000000 : ℝ)) (X := (100051021601852552199/100000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036425449498646631/50000000000000000000 : ℝ) ≤ (2000360912440837/2000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (50036425449498646631/50000000000000000000 : ℝ)^1024 ≤ (2000360912440837/2000000000000000 : ℝ)^4133 := by
      have hnat : (50036425449498646631 : ℕ)^1024*2000000000000000^4133 ≤ 2000360912440837^4133*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036425449498646631 50000000000000000000 2000360912440837 2000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000360912440837/2000000000000000 : ℝ)) (X := (50036425449498646631/50000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(456129761059549/3125000000000000000 : ℝ) ≤ ((28499938617494294087/28510000000000000000 : ℝ)+2*(540683734527/285100000000000 : ℝ)*(11211/100000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (28499938617494294087/28510000000000000000 : ℝ)+2*(540683734527/285100000000000 : ℝ)*(11211/100000 : ℝ)=(10000723194735131/10000000000000000 : ℝ) by norm_num, show 1+2*(456129761059549/3125000000000000000 : ℝ)=(1562956129761059549/1562500000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36425449498646631/100000000000000000000 : ℝ)+(456129761059549/3125000000000000000 : ℝ) ≤ ((28499938617494294087/28510000000000000000 : ℝ)+(540683734527/285100000000000 : ℝ)*((7031/50000 : ℝ)+(11211/100000 : ℝ)))^(4133/1024 : ℝ) := by
    rw [show (28499938617494294087/28510000000000000000 : ℝ)+(540683734527/285100000000000 : ℝ)*((7031/50000 : ℝ)+(11211/100000 : ℝ))=(5000631939234829/5000000000000000 : ℝ) by norm_num, show 1+(36425449498646631/100000000000000000000 : ℝ)+(456129761059549/3125000000000000000 : ℝ)=(100051021601852552199/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36425449498646631/100000000000000000000 : ℝ) ≤ ((28499938617494294087/28510000000000000000 : ℝ)+2*(540683734527/285100000000000 : ℝ)*(7031/50000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (28499938617494294087/28510000000000000000 : ℝ)+2*(540683734527/285100000000000 : ℝ)*(7031/50000 : ℝ)=(2000360912440837/2000000000000000 : ℝ) by norm_num, show 1+2*(36425449498646631/100000000000000000000 : ℝ)=(50036425449498646631/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (28499938617494294087/28510000000000000000 : ℝ)*(X 1 0+X 2 0)+(540683734527/285100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (28499938617494294087/28510000000000000000 : ℝ)) (alpha := (540683734527/285100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (28499938617494294087/28510000000000000000 : ℝ)*(X 0 1+X 2 1)+(540683734527/285100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (28499938617494294087/28510000000000000000 : ℝ)) (alpha := (540683734527/285100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (28499938617494294087/28510000000000000000 : ℝ)*(X 0 2+X 1 2)+(540683734527/285100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11211/100000 : ℝ)) (hi := (7031/50000 : ℝ)) (c := (28499938617494294087/28510000000000000000 : ℝ)) (alpha := (540683734527/285100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2199787001/10000000000 : ℝ)*X 0 0+(1078951627/2000000000 : ℝ)*X 0 1+(1316022429/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345095667/10000000000 : ℝ)*X 1 0+(-1133044719/5000000000 : ℝ)*X 1 1+(5264089783/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336273861/2500000000 : ℝ)*X 2 0+(5264089903/10000000000 : ℝ)*X 2 1+(-90643583/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2187158039/5000000000 : ℝ)*X 0 0+(4247967713/10000000000 : ℝ)*X 0 1+(4504466443/10000000000 : ℝ)*X 0 2+(2187158039/5000000000 : ℝ)*X 1 0+(4247967713/10000000000 : ℝ)*X 1 1+(4504466443/10000000000 : ℝ)*X 1 2+(2187158039/5000000000 : ℝ)*X 2 0+(4247967713/10000000000 : ℝ)*X 2 1+(4504466443/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-549948057/2500000000 : ℝ)*X 0 0+(5264419833/10000000000 : ℝ)*X 0 1+(674303347/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312162057/10000000000 : ℝ)*X 1 0+(-427150489/2000000000 : ℝ)*X 1 1+(2697213411/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062432353/2000000000 : ℝ)*X 2 0+(1348606801/2500000000 : ℝ)*X 2 1+(-3337113/15625000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4374326239/10000000000 : ℝ)*X 0 0+(2251909253/5000000000 : ℝ)*X 0 1+(4248617989/10000000000 : ℝ)*X 0 2+(4374326239/10000000000 : ℝ)*X 1 0+(2251909253/5000000000 : ℝ)*X 1 1+(4248617989/10000000000 : ℝ)*X 1 2+(4374326239/10000000000 : ℝ)*X 2 0+(2251909253/5000000000 : ℝ)*X 2 1+(4248617989/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (225635633142170176032845283/89093750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (709662059/100000000000000 : ℝ)*(base19) + (221775097/50000000000000 : ℝ)*(base23) + (1106163/3125000000000 : ℝ)*(upper2) + (173514037/100000000000000 : ℝ)*(upper3) + (721980179069753/12500000000000 : ℝ)*(major0) + (721980179069753/12500000000000 : ℝ)*(major1) + (721980179069753/12500000000000 : ℝ)*(major2) + (765298769194337/10000000000000 : ℝ)*(sp0) + (3826501694895933/50000000000000 : ℝ)*(sp1) + (7653001538140917/100000000000000 : ℝ)*(sp2) + (1949332998921921/50000000000000 : ℝ)*(sp3) + (8203755277/50000000000000 : ℝ)*(sp4) + (2117762813/100000000000000 : ℝ)*(sp6) + (6341699733/50000000000000 : ℝ)*(sp7) + (974669670310827/25000000000000 : ℝ)*(f.failure) + (306120163978157/4000000000000 : ℝ)*(f.sum) + (2402782323601/1781875000000000000000000000 : ℝ)*base65 + (4475781648932699489/356375000000000000000000000000000 : ℝ)*base68 + (1378719369136449489/356375000000000000000000000000000 : ℝ)*base70 + (1588752527732449489/356375000000000000000000000000000 : ℝ)*base72 + (24811895330489/7127500000000000000000000000 : ℝ)*base73 + (7877405750655699489/356375000000000000000000000000000 : ℝ)*base76 + (102003631664925511/356375000000000000000000000000000 : ℝ)*base77 + (4738213872160324489/356375000000000000000000000000000 : ℝ)*base80 + (4009101753827/14255000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (16822543/2500000000000000000000 : ℝ)*base90 + (16822543/2500000000000000000000 : ℝ)*base92 + (16822543/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4459388352885001944675747387/1425500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (157256249/20000000000000 : ℝ)*(base19) + (285260171/50000000000000 : ℝ)*(base23) + (70282299/100000000000000 : ℝ)*(upper2) + (85494079/50000000000000 : ℝ)*(upper3) + (78331717/100000000000000 : ℝ)*(upper5) + (5805186893458033/100000000000000 : ℝ)*(major0) + (5805186893458033/100000000000000 : ℝ)*(major1) + (5805186893458033/100000000000000 : ℝ)*(major2) + (17379718417/100000000000000 : ℝ)*(sp1) + (7358939431/25000000000000 : ℝ)*(sp2) + (1538377377574107/20000000000000 : ℝ)*(sp4) + (7691868721870873/100000000000000 : ℝ)*(sp5) + (7691856881592469/100000000000000 : ℝ)*(sp6) + (1959243397384467/50000000000000 : ℝ)*(sp7) + (1959243397384467/50000000000000 : ℝ)*(f.failure) + (1538377377574107/20000000000000 : ℝ)*(f.sum) + (10825146563661/14255000000000000000000000000 : ℝ)*base65 + (1706747524824650871/2851000000000000000000000000000000 : ℝ)*base67 + (20606637702247650871/2851000000000000000000000000000000 : ℝ)*base69 + (9780247556992349129/2851000000000000000000000000000000 : ℝ)*base72 + (796192128403/1781875000000000000000000000 : ℝ)*base74 + (43263694480840650871/2851000000000000000000000000000000 : ℝ)*base75 + (3382556178816650871/2851000000000000000000000000000000 : ℝ)*base77 + (4244620302018349129/2851000000000000000000000000000000 : ℝ)*base80 + (53985136933161/14255000000000000000000000000 : ℝ)*base81 + (40217303/5000000000000000000000 : ℝ)*base90 + (40217303/5000000000000000000000 : ℝ)*base92 + (40217303/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1074_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14019/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1074_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1074_s7_0 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-549956731/2500000000 : ℝ)*x 0 + (2697152443/5000000000 : ℝ)*x 1 + (210580667/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549956731/2500000000 : ℝ)^8267 ≤ (6680335074533/50000000000000 : ℝ)^6219 := by
    have hnat : (549956731 : ℕ)^8267*50000000000000^6219 ≤ 6680335074533^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549956731 2500000000 6680335074533 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697152443/5000000000 : ℝ)^8267 ≤ (44020832871629/100000000000000 : ℝ)^6219 := by
    have hnat : (2697152443 : ℕ)^8267*100000000000000^6219 ≤ 44020832871629^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697152443 5000000000 44020832871629 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (210580667/400000000 : ℝ)^8267 ≤ (10654624240769/25000000000000 : ℝ)^6219 := by
    have hnat : (210580667 : ℕ)^8267*25000000000000^6219 ≤ 10654624240769^6219*400000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210580667 400000000 10654624240769 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549956731/2500000000 : ℝ), (2697152443/5000000000 : ℝ), (210580667/400000000 : ℝ)] ![(6680335074533/50000000000000 : ℝ), (44020832871629/100000000000000 : ℝ), (10654624240769/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549956731/2500000000 : ℝ)|^8267 ≤ (6680335074533/50000000000000 : ℝ)^6219
        have hw : |(-549956731/2500000000 : ℝ)|=(549956731/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697152443/5000000000 : ℝ)|^8267 ≤ (44020832871629/100000000000000 : ℝ)^6219
        have hw : |(2697152443/5000000000 : ℝ)|=(2697152443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(210580667/400000000 : ℝ)|^8267 ≤ (10654624240769/25000000000000 : ℝ)^6219
        have hw : |(210580667/400000000 : ℝ)|=(210580667/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s7_1 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344982249/10000000000 : ℝ)*x 0 + (-113283797/500000000 : ℝ)*x 1 + (1052903407/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344982249/10000000000 : ℝ)^8267 ≤ (1087164687953/2500000000000 : ℝ)^6219 := by
    have hnat : (5344982249 : ℕ)^8267*2500000000000^6219 ≤ 1087164687953^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344982249 10000000000 1087164687953 2500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (113283797/500000000 : ℝ)^8267 ≤ (6947455816461/50000000000000 : ℝ)^6219 := by
    have hnat : (113283797 : ℕ)^8267*50000000000000^6219 ≤ 6947455816461^6219*500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113283797 500000000 6947455816461 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052903407/2000000000 : ℝ)^8267 ≤ (10654625209291/25000000000000 : ℝ)^6219 := by
    have hnat : (1052903407 : ℕ)^8267*25000000000000^6219 ≤ 10654625209291^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052903407 2000000000 10654625209291 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344982249/10000000000 : ℝ), (-113283797/500000000 : ℝ), (1052903407/2000000000 : ℝ)] ![(1087164687953/2500000000000 : ℝ), (6947455816461/50000000000000 : ℝ), (10654625209291/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344982249/10000000000 : ℝ)|^8267 ≤ (1087164687953/2500000000000 : ℝ)^6219
        have hw : |(5344982249/10000000000 : ℝ)|=(5344982249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-113283797/500000000 : ℝ)|^8267 ≤ (6947455816461/50000000000000 : ℝ)^6219
        have hw : |(-113283797/500000000 : ℝ)|=(113283797/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052903407/2000000000 : ℝ)|^8267 ≤ (10654625209291/25000000000000 : ℝ)^6219
        have hw : |(1052903407/2000000000 : ℝ)|=(1052903407/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s7_2 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344982383/10000000000 : ℝ)*x 0 + (5264516729/10000000000 : ℝ)*x 1 + (-453135233/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344982383/10000000000 : ℝ)^8267 ≤ (43486588967363/100000000000000 : ℝ)^6219 := by
    have hnat : (5344982383 : ℕ)^8267*100000000000000^6219 ≤ 43486588967363^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344982383 10000000000 43486588967363 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264516729/10000000000 : ℝ)^8267 ≤ (42618497544189/100000000000000 : ℝ)^6219 := by
    have hnat : (5264516729 : ℕ)^8267*100000000000000^6219 ≤ 42618497544189^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264516729 10000000000 42618497544189 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (453135233/2000000000 : ℝ)^8267 ≤ (13894913467211/100000000000000 : ℝ)^6219 := by
    have hnat : (453135233 : ℕ)^8267*100000000000000^6219 ≤ 13894913467211^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      453135233 2000000000 13894913467211 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344982383/10000000000 : ℝ), (5264516729/10000000000 : ℝ), (-453135233/2000000000 : ℝ)] ![(43486588967363/100000000000000 : ℝ), (42618497544189/100000000000000 : ℝ), (13894913467211/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344982383/10000000000 : ℝ)|^8267 ≤ (43486588967363/100000000000000 : ℝ)^6219
        have hw : |(5344982383/10000000000 : ℝ)|=(5344982383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264516729/10000000000 : ℝ)|^8267 ≤ (42618497544189/100000000000000 : ℝ)^6219
        have hw : |(5264516729/10000000000 : ℝ)|=(5264516729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-453135233/2000000000 : ℝ)|^8267 ≤ (13894913467211/100000000000000 : ℝ)^6219
        have hw : |(-453135233/2000000000 : ℝ)|=(453135233/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s7_3 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4374338527/10000000000 : ℝ)*x 0 + (4248829259/10000000000 : ℝ)*x 1 + (2251799541/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4374338527/10000000000 : ℝ)^8267 ≤ (16658275267571/50000000000000 : ℝ)^6219 := by
    have hnat : (4374338527 : ℕ)^8267*50000000000000^6219 ≤ 16658275267571^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4374338527 10000000000 16658275267571 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4248829259/10000000000 : ℝ)^8267 ≤ (32051870075373/100000000000000 : ℝ)^6219 := by
    have hnat : (4248829259 : ℕ)^8267*100000000000000^6219 ≤ 32051870075373^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4248829259 10000000000 32051870075373 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2251799541/5000000000 : ℝ)^8267 ≤ (4328947421603/12500000000000 : ℝ)^6219 := by
    have hnat : (2251799541 : ℕ)^8267*12500000000000^6219 ≤ 4328947421603^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251799541 5000000000 4328947421603 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4374338527/10000000000 : ℝ), (4248829259/10000000000 : ℝ), (2251799541/5000000000 : ℝ)] ![(16658275267571/50000000000000 : ℝ), (32051870075373/100000000000000 : ℝ), (4328947421603/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4374338527/10000000000 : ℝ)|^8267 ≤ (16658275267571/50000000000000 : ℝ)^6219
        have hw : |(4374338527/10000000000 : ℝ)|=(4374338527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4248829259/10000000000 : ℝ)|^8267 ≤ (32051870075373/100000000000000 : ℝ)^6219
        have hw : |(4248829259/10000000000 : ℝ)|=(4248829259/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2251799541/5000000000 : ℝ)|^8267 ≤ (4328947421603/12500000000000 : ℝ)^6219
        have hw : |(2251799541/5000000000 : ℝ)|=(2251799541/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s7_4 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2199832153/10000000000 : ℝ)*x 0 + (1316210627/2500000000 : ℝ)*x 1 + (2696988879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2199832153/10000000000 : ℝ)^8267 ≤ (534428494637/4000000000000 : ℝ)^6219 := by
    have hnat : (2199832153 : ℕ)^8267*4000000000000^6219 ≤ 534428494637^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199832153 10000000000 534428494637 4000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316210627/2500000000 : ℝ)^8267 ≤ (8524400680753/20000000000000 : ℝ)^6219 := by
    have hnat : (1316210627 : ℕ)^8267*20000000000000^6219 ≤ 8524400680753^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316210627 2500000000 8524400680753 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696988879/5000000000 : ℝ)^8267 ≤ (44017284218677/100000000000000 : ℝ)^6219 := by
    have hnat : (2696988879 : ℕ)^8267*100000000000000^6219 ≤ 44017284218677^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696988879 5000000000 44017284218677 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2199832153/10000000000 : ℝ), (1316210627/2500000000 : ℝ), (2696988879/5000000000 : ℝ)] ![(534428494637/4000000000000 : ℝ), (8524400680753/20000000000000 : ℝ), (44017284218677/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2199832153/10000000000 : ℝ)|^8267 ≤ (534428494637/4000000000000 : ℝ)^6219
        have hw : |(-2199832153/10000000000 : ℝ)|=(2199832153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316210627/2500000000 : ℝ)|^8267 ≤ (8524400680753/20000000000000 : ℝ)^6219
        have hw : |(1316210627/2500000000 : ℝ)|=(1316210627/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696988879/5000000000 : ℝ)|^8267 ≤ (44017284218677/100000000000000 : ℝ)^6219
        have hw : |(2696988879/5000000000 : ℝ)|=(2696988879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s7_5 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062454173/2000000000 : ℝ)*x 0 + (-2136215161/10000000000 : ℝ)*x 1 + (5393977507/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062454173/2000000000 : ℝ)^8267 ≤ (43133162815741/100000000000000 : ℝ)^6219 := by
    have hnat : (1062454173 : ℕ)^8267*100000000000000^6219 ≤ 43133162815741^6219*2000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062454173 2000000000 43133162815741 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136215161/10000000000 : ℝ)^8267 ≤ (1606194458259/12500000000000 : ℝ)^6219 := by
    have hnat : (2136215161 : ℕ)^8267*12500000000000^6219 ≤ 1606194458259^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136215161 10000000000 1606194458259 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393977507/10000000000 : ℝ)^8267 ≤ (44017281495881/100000000000000 : ℝ)^6219 := by
    have hnat : (5393977507 : ℕ)^8267*100000000000000^6219 ≤ 44017281495881^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393977507 10000000000 44017281495881 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062454173/2000000000 : ℝ), (-2136215161/10000000000 : ℝ), (5393977507/10000000000 : ℝ)] ![(43133162815741/100000000000000 : ℝ), (1606194458259/12500000000000 : ℝ), (44017281495881/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062454173/2000000000 : ℝ)|^8267 ≤ (43133162815741/100000000000000 : ℝ)^6219
        have hw : |(1062454173/2000000000 : ℝ)|=(1062454173/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136215161/10000000000 : ℝ)|^8267 ≤ (1606194458259/12500000000000 : ℝ)^6219
        have hw : |(-2136215161/10000000000 : ℝ)|=(2136215161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393977507/10000000000 : ℝ)|^8267 ≤ (44017281495881/100000000000000 : ℝ)^6219
        have hw : |(5393977507/10000000000 : ℝ)|=(5393977507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s7_6 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312270749/10000000000 : ℝ)*x 0 + (2696988877/5000000000 : ℝ)*x 1 + (-2136214983/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312270749/10000000000 : ℝ)^8267 ≤ (21566580781853/50000000000000 : ℝ)^6219 := by
    have hnat : (5312270749 : ℕ)^8267*50000000000000^6219 ≤ 21566580781853^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312270749 10000000000 21566580781853 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696988877/5000000000 : ℝ)^8267 ≤ (22008642087643/50000000000000 : ℝ)^6219 := by
    have hnat : (2696988877 : ℕ)^8267*50000000000000^6219 ≤ 22008642087643^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696988877 5000000000 22008642087643 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2136214983/10000000000 : ℝ)^8267 ≤ (1606194280349/12500000000000 : ℝ)^6219 := by
    have hnat : (2136214983 : ℕ)^8267*12500000000000^6219 ≤ 1606194280349^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136214983 10000000000 1606194280349 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312270749/10000000000 : ℝ), (2696988877/5000000000 : ℝ), (-2136214983/10000000000 : ℝ)] ![(21566580781853/50000000000000 : ℝ), (22008642087643/50000000000000 : ℝ), (1606194280349/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312270749/10000000000 : ℝ)|^8267 ≤ (21566580781853/50000000000000 : ℝ)^6219
        have hw : |(5312270749/10000000000 : ℝ)|=(5312270749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696988877/5000000000 : ℝ)|^8267 ≤ (22008642087643/50000000000000 : ℝ)^6219
        have hw : |(2696988877/5000000000 : ℝ)|=(2696988877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2136214983/10000000000 : ℝ)|^8267 ≤ (1606194280349/12500000000000 : ℝ)^6219
        have hw : |(-2136214983/10000000000 : ℝ)|=(2136214983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s7_7 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187173971/5000000000 : ℝ)*x 0 + (180118427/400000000 : ℝ)*x 1 + (424947049/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187173971/5000000000 : ℝ)^8267 ≤ (33316645857659/100000000000000 : ℝ)^6219 := by
    have hnat : (2187173971 : ℕ)^8267*100000000000000^6219 ≤ 33316645857659^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187173971 5000000000 33316645857659 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (180118427/400000000 : ℝ)^8267 ≤ (34625053667483/100000000000000 : ℝ)^6219 := by
    have hnat : (180118427 : ℕ)^8267*100000000000000^6219 ≤ 34625053667483^6219*400000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      180118427 400000000 34625053667483 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424947049/1000000000 : ℝ)^8267 ≤ (32058300457429/100000000000000 : ℝ)^6219 := by
    have hnat : (424947049 : ℕ)^8267*100000000000000^6219 ≤ 32058300457429^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424947049 1000000000 32058300457429 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187173971/5000000000 : ℝ), (180118427/400000000 : ℝ), (424947049/1000000000 : ℝ)] ![(33316645857659/100000000000000 : ℝ), (34625053667483/100000000000000 : ℝ), (32058300457429/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187173971/5000000000 : ℝ)|^8267 ≤ (33316645857659/100000000000000 : ℝ)^6219
        have hw : |(2187173971/5000000000 : ℝ)|=(2187173971/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(180118427/400000000 : ℝ)|^8267 ≤ (34625053667483/100000000000000 : ℝ)^6219
        have hw : |(180118427/400000000 : ℝ)|=(180118427/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(424947049/1000000000 : ℝ)|^8267 ≤ (32058300457429/100000000000000 : ℝ)^6219
        have hw : |(424947049/1000000000 : ℝ)|=(424947049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1074_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14019/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (11261/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1401/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14019/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2813/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14019/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2813/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14019/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2813/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14019/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2813/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14019/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2813/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14019/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2813/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2813/25000 : ℝ) ^ (4133/1024 : ℝ) ≤ (14812799875961841/100000000000000000000 : ℝ) := by
    have hpowers : (2813/25000 : ℝ)^4133 ≤ (14812799875961841/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2813 : ℕ)^4133*100000000000000000000^1024 ≤ 14812799875961841^1024*25000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2813 25000 14812799875961841 100000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2813/25000 : ℝ)) (X := (14812799875961841/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14019/100000 : ℝ) ^ (4133/1024 : ℝ) ≤ (35977967870685437/100000000000000000000 : ℝ) := by
    have hpowers : (14019/100000 : ℝ)^4133 ≤ (35977967870685437/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14019 : ℕ)^4133*100000000000000000000^1024 ≤ 35977967870685437^1024*100000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14019 100000 35977967870685437 100000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14019/100000 : ℝ)) (X := (35977967870685437/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50014812799875961841/50000000000000000000 : ℝ) ≤ (2000146785552369/2000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (50014812799875961841/50000000000000000000 : ℝ)^1024 ≤ (2000146785552369/2000000000000000 : ℝ)^4133 := by
      have hnat : (50014812799875961841 : ℕ)^1024*2000000000000000^4133 ≤ 2000146785552369^4133*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014812799875961841 50000000000000000000 2000146785552369 2000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000146785552369/2000000000000000 : ℝ)) (X := (50014812799875961841/50000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025395383873323639/50000000000000000000 : ℝ) ≤ (10001258161468721/10000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (50025395383873323639/50000000000000000000 : ℝ)^1024 ≤ (10001258161468721/10000000000000000 : ℝ)^4133 := by
      have hnat : (50025395383873323639 : ℕ)^1024*10000000000000000^4133 ≤ 10001258161468721^4133*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025395383873323639 50000000000000000000 10001258161468721 10000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001258161468721/10000000000000000 : ℝ)) (X := (50025395383873323639/50000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50035977967870685437/50000000000000000000 : ℝ) ≤ (10001782395175597/10000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (50035977967870685437/50000000000000000000 : ℝ)^1024 ≤ (10001782395175597/10000000000000000 : ℝ)^4133 := by
      have hnat : (50035977967870685437 : ℕ)^1024*10000000000000000^4133 ≤ 10001782395175597^4133*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50035977967870685437 50000000000000000000 10001782395175597 10000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001782395175597/10000000000000000 : ℝ)) (X := (50035977967870685437/50000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(14812799875961841/100000000000000000000 : ℝ) ≤ ((27660233422777487611/27670000000000000000 : ℝ)+2*(131058426719/69175000000000 : ℝ)*(2813/25000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (27660233422777487611/27670000000000000000 : ℝ)+2*(131058426719/69175000000000 : ℝ)*(2813/25000 : ℝ)=(2000146785552369/2000000000000000 : ℝ) by norm_num, show 1+2*(14812799875961841/100000000000000000000 : ℝ)=(50014812799875961841/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(35977967870685437/100000000000000000000 : ℝ)+(14812799875961841/100000000000000000000 : ℝ) ≤ ((27660233422777487611/27670000000000000000 : ℝ)+(131058426719/69175000000000 : ℝ)*((14019/100000 : ℝ)+(2813/25000 : ℝ)))^(4133/1024 : ℝ) := by
    rw [show (27660233422777487611/27670000000000000000 : ℝ)+(131058426719/69175000000000 : ℝ)*((14019/100000 : ℝ)+(2813/25000 : ℝ))=(10001258161468721/10000000000000000 : ℝ) by norm_num, show 1+(35977967870685437/100000000000000000000 : ℝ)+(14812799875961841/100000000000000000000 : ℝ)=(50025395383873323639/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(35977967870685437/100000000000000000000 : ℝ) ≤ ((27660233422777487611/27670000000000000000 : ℝ)+2*(131058426719/69175000000000 : ℝ)*(14019/100000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (27660233422777487611/27670000000000000000 : ℝ)+2*(131058426719/69175000000000 : ℝ)*(14019/100000 : ℝ)=(10001782395175597/10000000000000000 : ℝ) by norm_num, show 1+2*(35977967870685437/100000000000000000000 : ℝ)=(50035977967870685437/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (27660233422777487611/27670000000000000000 : ℝ)*(X 1 0+X 2 0)+(131058426719/69175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (14019/100000 : ℝ)) (c := (27660233422777487611/27670000000000000000 : ℝ)) (alpha := (131058426719/69175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (27660233422777487611/27670000000000000000 : ℝ)*(X 0 1+X 2 1)+(131058426719/69175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (14019/100000 : ℝ)) (c := (27660233422777487611/27670000000000000000 : ℝ)) (alpha := (131058426719/69175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (27660233422777487611/27670000000000000000 : ℝ)*(X 0 2+X 1 2)+(131058426719/69175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (2813/25000 : ℝ)) (hi := (14019/100000 : ℝ)) (c := (27660233422777487611/27670000000000000000 : ℝ)) (alpha := (131058426719/69175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-549956731/2500000000 : ℝ)*X 0 0+(2697152443/5000000000 : ℝ)*X 0 1+(210580667/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344982249/10000000000 : ℝ)*X 1 0+(-113283797/500000000 : ℝ)*X 1 1+(1052903407/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344982383/10000000000 : ℝ)*X 2 0+(5264516729/10000000000 : ℝ)*X 2 1+(-453135233/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4374338527/10000000000 : ℝ)*X 0 0+(4248829259/10000000000 : ℝ)*X 0 1+(2251799541/5000000000 : ℝ)*X 0 2+(4374338527/10000000000 : ℝ)*X 1 0+(4248829259/10000000000 : ℝ)*X 1 1+(2251799541/5000000000 : ℝ)*X 1 2+(4374338527/10000000000 : ℝ)*X 2 0+(4248829259/10000000000 : ℝ)*X 2 1+(2251799541/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2199832153/10000000000 : ℝ)*X 0 0+(1316210627/2500000000 : ℝ)*X 0 1+(2696988879/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1062454173/2000000000 : ℝ)*X 1 0+(-2136215161/10000000000 : ℝ)*X 1 1+(5393977507/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312270749/10000000000 : ℝ)*X 2 0+(2696988877/5000000000 : ℝ)*X 2 1+(-2136214983/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187173971/5000000000 : ℝ)*X 0 0+(180118427/400000000 : ℝ)*X 0 1+(424947049/1000000000 : ℝ)*X 0 2+(2187173971/5000000000 : ℝ)*X 1 0+(180118427/400000000 : ℝ)*X 1 1+(424947049/1000000000 : ℝ)*X 1 2+(2187173971/5000000000 : ℝ)*X 2 0+(180118427/400000000 : ℝ)*X 2 1+(424947049/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (631901345057513365944197907/276700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (441358479/50000000000000 : ℝ)*(base19) + (1251698461/100000000000000 : ℝ)*(base23) + (23779383/20000000000000 : ℝ)*(upper2) + (190713083/100000000000000 : ℝ)*(upper3) + (24923241/100000000000000 : ℝ)*(upper4) + (1163008828552221/20000000000000 : ℝ)*(major0) + (1163008828552221/20000000000000 : ℝ)*(major1) + (1163008828552221/20000000000000 : ℝ)*(major2) + (308196352521559/4000000000000 : ℝ)*(sp0) + (385247345650687/5000000000000 : ℝ)*(sp1) + (1926236636008059/25000000000000 : ℝ)*(sp2) + (981281002193911/25000000000000 : ℝ)*(sp3) + (38982691723/100000000000000 : ℝ)*(sp4) + (16404892341/100000000000000 : ℝ)*(sp7) + (785028082733597/20000000000000 : ℝ)*(f.failure) + (3852473897865349/50000000000000 : ℝ)*(f.sum) + (10942939952201/2767000000000000000000000000 : ℝ)*base66 + (1249550212546634031/553400000000000000000000000000000 : ℝ)*base67 + (825795257109834031/553400000000000000000000000000000 : ℝ)*base69 + (3640346844004365969/553400000000000000000000000000000 : ℝ)*base72 + (12308250468961/2767000000000000000000000000 : ℝ)*base74 + (2092811849959565969/553400000000000000000000000000000 : ℝ)*base76 + (3105047345360434031/553400000000000000000000000000000 : ℝ)*base77 + (7516150590152634031/553400000000000000000000000000000 : ℝ)*base79 + (1328770921919/276700000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2728473/2000000000000000000000 : ℝ)*base90 + (2728473/2000000000000000000000 : ℝ)*base92 + (2728473/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (455572023312545481469101477/86468750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (907607339/50000000000000 : ℝ)*(base19) + (693197671/25000000000000 : ℝ)*(base23) + (18312683/4000000000000 : ℝ)*(upper2) + (118129641/50000000000000 : ℝ)*(upper3) + (365272667908319/6250000000000 : ℝ)*(major0) + (365272667908319/6250000000000 : ℝ)*(major1) + (365272667908319/6250000000000 : ℝ)*(major2) + (15659738659/50000000000000 : ℝ)*(sp1) + (74331832211/100000000000000 : ℝ)*(sp2) + (1786838729/100000000000000 : ℝ)*(sp3) + (1548758967849271/20000000000000 : ℝ)*(sp4) + (7743761704554359/100000000000000 : ℝ)*(sp5) + (7743717734623461/100000000000000 : ℝ)*(sp6) + (78898571427201/2000000000000 : ℝ)*(sp7) + (197246517909939/5000000000000 : ℝ)*(f.failure) + (1548758967849271/20000000000000 : ℝ)*(f.sum) + (7820670178647/1729375000000000000000000000 : ℝ)*base66 + (698008701178451591/172937500000000000000000000000000 : ℝ)*base68 + (221399774747235909/172937500000000000000000000000000 : ℝ)*base69 + (617790621299264091/172937500000000000000000000000000 : ℝ)*base72 + (27855283604517/6917500000000000000000000000 : ℝ)*base73 + (1006649635519048409/172937500000000000000000000000000 : ℝ)*base75 + (360771321255201591/172937500000000000000000000000000 : ℝ)*base78 + (653561355177889091/172937500000000000000000000000000 : ℝ)*base80 + (4727143858151/3458750000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (1260151/500000000000000000000 : ℝ)*base90 + (1260151/500000000000000000000 : ℝ)*base92 + (1260151/500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1074_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14019/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2813/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1074_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1074_s8_0 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2199833703/10000000000 : ℝ)*x 0 + (2697104849/5000000000 : ℝ)*x 1 + (658075943/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2199833703/10000000000 : ℝ)^8267 ≤ (13360724880013/100000000000000 : ℝ)^6219 := by
    have hnat : (2199833703 : ℕ)^8267*100000000000000^6219 ≤ 13360724880013^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2199833703 10000000000 13360724880013 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2697104849/5000000000 : ℝ)^8267 ≤ (44019800274087/100000000000000 : ℝ)^6219 := by
    have hnat : (2697104849 : ℕ)^8267*100000000000000^6219 ≤ 44019800274087^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2697104849 5000000000 44019800274087 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658075943/1250000000 : ℝ)^8267 ≤ (42619474839527/100000000000000 : ℝ)^6219 := by
    have hnat : (658075943 : ℕ)^8267*100000000000000^6219 ≤ 42619474839527^6219*1250000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658075943 1250000000 42619474839527 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2199833703/10000000000 : ℝ), (2697104849/5000000000 : ℝ), (658075943/1250000000 : ℝ)] ![(13360724880013/100000000000000 : ℝ), (44019800274087/100000000000000 : ℝ), (42619474839527/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2199833703/10000000000 : ℝ)|^8267 ≤ (13360724880013/100000000000000 : ℝ)^6219
        have hw : |(-2199833703/10000000000 : ℝ)|=(2199833703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2697104849/5000000000 : ℝ)|^8267 ≤ (44019800274087/100000000000000 : ℝ)^6219
        have hw : |(2697104849/5000000000 : ℝ)|=(2697104849/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658075943/1250000000 : ℝ)|^8267 ≤ (42619474839527/100000000000000 : ℝ)^6219
        have hw : |(658075943/1250000000 : ℝ)|=(658075943/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s8_1 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668119857/1250000000 : ℝ)*x 0 + (-2265587493/10000000000 : ℝ)*x 1 + (1316151887/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668119857/1250000000 : ℝ)^8267 ≤ (43486334517229/100000000000000 : ℝ)^6219 := by
    have hnat : (668119857 : ℕ)^8267*100000000000000^6219 ≤ 43486334517229^6219*1250000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668119857 1250000000 43486334517229 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2265587493/10000000000 : ℝ)^8267 ≤ (2778838116481/20000000000000 : ℝ)^6219 := by
    have hnat : (2265587493 : ℕ)^8267*20000000000000^6219 ≤ 2778838116481^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2265587493 10000000000 2778838116481 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316151887/2500000000 : ℝ)^8267 ≤ (10654868720643/25000000000000 : ℝ)^6219 := by
    have hnat : (1316151887 : ℕ)^8267*25000000000000^6219 ≤ 10654868720643^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316151887 2500000000 10654868720643 25000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668119857/1250000000 : ℝ), (-2265587493/10000000000 : ℝ), (1316151887/2500000000 : ℝ)] ![(43486334517229/100000000000000 : ℝ), (2778838116481/20000000000000 : ℝ), (10654868720643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668119857/1250000000 : ℝ)|^8267 ≤ (43486334517229/100000000000000 : ℝ)^6219
        have hw : |(668119857/1250000000 : ℝ)|=(668119857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2265587493/10000000000 : ℝ)|^8267 ≤ (2778838116481/20000000000000 : ℝ)^6219
        have hw : |(-2265587493/10000000000 : ℝ)|=(2265587493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316151887/2500000000 : ℝ)|^8267 ≤ (10654868720643/25000000000000 : ℝ)^6219
        have hw : |(1316151887/2500000000 : ℝ)|=(1316151887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s8_2 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344958859/10000000000 : ℝ)*x 0 + (2632303773/5000000000 : ℝ)*x 1 + (-566396873/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344958859/10000000000 : ℝ)^8267 ≤ (1739453381987/4000000000000 : ℝ)^6219 := by
    have hnat : (5344958859 : ℕ)^8267*4000000000000^6219 ≤ 1739453381987^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344958859 10000000000 1739453381987 4000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2632303773/5000000000 : ℝ)^8267 ≤ (42619474861049/100000000000000 : ℝ)^6219 := by
    have hnat : (2632303773 : ℕ)^8267*100000000000000^6219 ≤ 42619474861049^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632303773 5000000000 42619474861049 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (566396873/2500000000 : ℝ)^8267 ≤ (13894190574253/100000000000000 : ℝ)^6219 := by
    have hnat : (566396873 : ℕ)^8267*100000000000000^6219 ≤ 13894190574253^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      566396873 2500000000 13894190574253 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344958859/10000000000 : ℝ), (2632303773/5000000000 : ℝ), (-566396873/2500000000 : ℝ)] ![(1739453381987/4000000000000 : ℝ), (42619474861049/100000000000000 : ℝ), (13894190574253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344958859/10000000000 : ℝ)|^8267 ≤ (1739453381987/4000000000000 : ℝ)^6219
        have hw : |(5344958859/10000000000 : ℝ)|=(5344958859/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2632303773/5000000000 : ℝ)|^8267 ≤ (42619474861049/100000000000000 : ℝ)^6219
        have hw : |(2632303773/5000000000 : ℝ)|=(2632303773/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-566396873/2500000000 : ℝ)|^8267 ≤ (13894190574253/100000000000000 : ℝ)^6219
        have hw : |(-566396873/2500000000 : ℝ)|=(566396873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s8_3 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (546792919/1250000000 : ℝ)*x 0 + (4249010689/10000000000 : ℝ)*x 1 + (1125854079/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (546792919/1250000000 : ℝ)^8267 ≤ (1332663975441/4000000000000 : ℝ)^6219 := by
    have hnat : (546792919 : ℕ)^8267*4000000000000^6219 ≤ 1332663975441^6219*1250000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546792919 1250000000 1332663975441 4000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4249010689/10000000000 : ℝ)^8267 ≤ (16026844728133/50000000000000 : ℝ)^6219 := by
    have hnat : (4249010689 : ℕ)^8267*50000000000000^6219 ≤ 16026844728133^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4249010689 10000000000 16026844728133 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1125854079/2500000000 : ℝ)^8267 ≤ (4328713891713/12500000000000 : ℝ)^6219 := by
    have hnat : (1125854079 : ℕ)^8267*12500000000000^6219 ≤ 4328713891713^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1125854079 2500000000 4328713891713 12500000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(546792919/1250000000 : ℝ), (4249010689/10000000000 : ℝ), (1125854079/2500000000 : ℝ)] ![(1332663975441/4000000000000 : ℝ), (16026844728133/50000000000000 : ℝ), (4328713891713/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(546792919/1250000000 : ℝ)|^8267 ≤ (1332663975441/4000000000000 : ℝ)^6219
        have hw : |(546792919/1250000000 : ℝ)|=(546792919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4249010689/10000000000 : ℝ)|^8267 ≤ (16026844728133/50000000000000 : ℝ)^6219
        have hw : |(4249010689/10000000000 : ℝ)|=(4249010689/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1125854079/2500000000 : ℝ)|^8267 ≤ (4328713891713/12500000000000 : ℝ)^6219
        have hw : |(1125854079/2500000000 : ℝ)|=(1125854079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s8_4 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-549959693/2500000000 : ℝ)*x 0 + (526493233/1000000000 : ℝ)*x 1 + (5393883723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549959693/2500000000 : ℝ)^8267 ≤ (13360765805137/100000000000000 : ℝ)^6219 := by
    have hnat : (549959693 : ℕ)^8267*100000000000000^6219 ≤ 13360765805137^6219*2500000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549959693 2500000000 13360765805137 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526493233/1000000000 : ℝ)^8267 ≤ (42622970032713/100000000000000 : ℝ)^6219 := by
    have hnat : (526493233 : ℕ)^8267*100000000000000^6219 ≤ 42622970032713^6219*1000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526493233 1000000000 42622970032713 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393883723/10000000000 : ℝ)^8267 ≤ (44016264149193/100000000000000 : ℝ)^6219 := by
    have hnat : (5393883723 : ℕ)^8267*100000000000000^6219 ≤ 44016264149193^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393883723 10000000000 44016264149193 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549959693/2500000000 : ℝ), (526493233/1000000000 : ℝ), (5393883723/10000000000 : ℝ)] ![(13360765805137/100000000000000 : ℝ), (42622970032713/100000000000000 : ℝ), (44016264149193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549959693/2500000000 : ℝ)|^8267 ≤ (13360765805137/100000000000000 : ℝ)^6219
        have hw : |(-549959693/2500000000 : ℝ)|=(549959693/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526493233/1000000000 : ℝ)|^8267 ≤ (42622970032713/100000000000000 : ℝ)^6219
        have hw : |(526493233/1000000000 : ℝ)|=(526493233/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393883723/10000000000 : ℝ)|^8267 ≤ (44016264149193/100000000000000 : ℝ)^6219
        have hw : |(5393883723/10000000000 : ℝ)|=(5393883723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s8_5 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312293867/10000000000 : ℝ)*x 0 + (-2136311261/10000000000 : ℝ)*x 1 + (674235473/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312293867/10000000000 : ℝ)^8267 ≤ (43133411085821/100000000000000 : ℝ)^6219 := by
    have hnat : (5312293867 : ℕ)^8267*100000000000000^6219 ≤ 43133411085821^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312293867 10000000000 43133411085821 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2136311261/10000000000 : ℝ)^8267 ≤ (12850324083317/100000000000000 : ℝ)^6219 := by
    have hnat : (2136311261 : ℕ)^8267*100000000000000^6219 ≤ 12850324083317^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136311261 10000000000 12850324083317 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (674235473/1250000000 : ℝ)^8267 ≤ (8803252962181/20000000000000 : ℝ)^6219 := by
    have hnat : (674235473 : ℕ)^8267*20000000000000^6219 ≤ 8803252962181^6219*1250000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      674235473 1250000000 8803252962181 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312293867/10000000000 : ℝ), (-2136311261/10000000000 : ℝ), (674235473/1250000000 : ℝ)] ![(43133411085821/100000000000000 : ℝ), (12850324083317/100000000000000 : ℝ), (8803252962181/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312293867/10000000000 : ℝ)|^8267 ≤ (43133411085821/100000000000000 : ℝ)^6219
        have hw : |(5312293867/10000000000 : ℝ)|=(5312293867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2136311261/10000000000 : ℝ)|^8267 ≤ (12850324083317/100000000000000 : ℝ)^6219
        have hw : |(-2136311261/10000000000 : ℝ)|=(2136311261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(674235473/1250000000 : ℝ)|^8267 ≤ (8803252962181/20000000000000 : ℝ)^6219
        have hw : |(674235473/1250000000 : ℝ)|=(674235473/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s8_6 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656146989/5000000000 : ℝ)*x 0 + (5393883903/10000000000 : ℝ)*x 1 + (-2136310951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656146989/5000000000 : ℝ)^8267 ≤ (43133412283891/100000000000000 : ℝ)^6219 := by
    have hnat : (2656146989 : ℕ)^8267*100000000000000^6219 ≤ 43133412283891^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656146989 5000000000 43133412283891 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393883903/10000000000 : ℝ)^8267 ≤ (8803253220357/20000000000000 : ℝ)^6219 := by
    have hnat : (5393883903 : ℕ)^8267*20000000000000^6219 ≤ 8803253220357^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393883903 10000000000 8803253220357 20000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2136310951/10000000000 : ℝ)^8267 ≤ (12850321604533/100000000000000 : ℝ)^6219 := by
    have hnat : (2136310951 : ℕ)^8267*100000000000000^6219 ≤ 12850321604533^6219*10000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2136310951 10000000000 12850321604533 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656146989/5000000000 : ℝ), (5393883903/10000000000 : ℝ), (-2136310951/10000000000 : ℝ)] ![(43133412283891/100000000000000 : ℝ), (8803253220357/20000000000000 : ℝ), (12850321604533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656146989/5000000000 : ℝ)|^8267 ≤ (43133412283891/100000000000000 : ℝ)^6219
        have hw : |(2656146989/5000000000 : ℝ)|=(2656146989/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393883903/10000000000 : ℝ)|^8267 ≤ (8803253220357/20000000000000 : ℝ)^6219
        have hw : |(5393883903/10000000000 : ℝ)|=(5393883903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2136310951/10000000000 : ℝ)|^8267 ≤ (12850321604533/100000000000000 : ℝ)^6219
        have hw : |(-2136310951/10000000000 : ℝ)|=(2136310951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1074_s8_7 (p : ℝ) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2187176727/5000000000 : ℝ)*x 0 + (2251389457/5000000000 : ℝ)*x 1 + (2124825093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2187176727/5000000000 : ℝ)^8267 ≤ (16658350832069/50000000000000 : ℝ)^6219 := by
    have hnat : (2187176727 : ℕ)^8267*50000000000000^6219 ≤ 16658350832069^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2187176727 5000000000 16658350832069 50000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2251389457/5000000000 : ℝ)^8267 ≤ (34623195788171/100000000000000 : ℝ)^6219 := by
    have hnat : (2251389457 : ℕ)^8267*100000000000000^6219 ≤ 34623195788171^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2251389457 5000000000 34623195788171 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2124825093/5000000000 : ℝ)^8267 ≤ (32060102539193/100000000000000 : ℝ)^6219 := by
    have hnat : (2124825093 : ℕ)^8267*100000000000000^6219 ≤ 32060102539193^6219*5000000000^8267 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2124825093 5000000000 32060102539193 100000000000000 8267 6219 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8267/2048 : ℝ)) 8267 6219 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2187176727/5000000000 : ℝ), (2251389457/5000000000 : ℝ), (2124825093/5000000000 : ℝ)] ![(16658350832069/50000000000000 : ℝ), (34623195788171/100000000000000 : ℝ), (32060102539193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2187176727/5000000000 : ℝ)|^8267 ≤ (16658350832069/50000000000000 : ℝ)^6219
        have hw : |(2187176727/5000000000 : ℝ)|=(2187176727/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2251389457/5000000000 : ℝ)|^8267 ≤ (34623195788171/100000000000000 : ℝ)^6219
        have hw : |(2251389457/5000000000 : ℝ)|=(2251389457/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2124825093/5000000000 : ℝ)|^8267 ≤ (32060102539193/100000000000000 : ℝ)^6219
        have hw : |(2124825093/5000000000 : ℝ)|=(2124825093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1074_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11263/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1751/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1401/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11261/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1401/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11261/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1401/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11261/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1401/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11261/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1401/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11261/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1401/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11261/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11261/100000 : ℝ) ^ (4133/1024 : ℝ) ≤ (3715169653436637/25000000000000000000 : ℝ) := by
    have hpowers : (11261/100000 : ℝ)^4133 ≤ (3715169653436637/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11261 : ℕ)^4133*25000000000000000000^1024 ≤ 3715169653436637^1024*100000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11261 100000 3715169653436637 25000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11261/100000 : ℝ)) (X := (3715169653436637/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1401/10000 : ℝ) ^ (4133/1024 : ℝ) ≤ (717696694480179/2000000000000000000 : ℝ) := by
    have hpowers : (1401/10000 : ℝ)^4133 ≤ (717696694480179/2000000000000000000 : ℝ)^1024 := by
      have hnat : (1401 : ℕ)^4133*2000000000000000000^1024 ≤ 717696694480179^1024*10000^4133 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1401 10000 717696694480179 2000000000000000000 4133 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1401/10000 : ℝ)) (X := (717696694480179/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503715169653436637/12500000000000000000 : ℝ) ≤ (625046018733623/625000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (12503715169653436637/12500000000000000000 : ℝ)^1024 ≤ (625046018733623/625000000000000 : ℝ)^4133 := by
      have hnat : (12503715169653436637 : ℕ)^1024*625000000000000^4133 ≤ 625046018733623^4133*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503715169653436637 12500000000000000000 625046018733623 625000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625046018733623/625000000000000 : ℝ)) (X := (12503715169653436637/12500000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50025372756668877749/50000000000000000000 : ℝ) ≤ (10001257040664819/10000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (50025372756668877749/50000000000000000000 : ℝ)^1024 ≤ (10001257040664819/10000000000000000 : ℝ)^4133 := by
      have hnat : (50025372756668877749 : ℕ)^1024*10000000000000000^4133 ≤ 10001257040664819^4133*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50025372756668877749 50000000000000000000 10001257040664819 10000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001257040664819/10000000000000000 : ℝ)) (X := (50025372756668877749/50000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000717696694480179/1000000000000000000 : ℝ) ≤ (1000177778159167/1000000000000000 : ℝ) ^ (4133/1024 : ℝ) := by
    have hpowers : (1000717696694480179/1000000000000000000 : ℝ)^1024 ≤ (1000177778159167/1000000000000000 : ℝ)^4133 := by
      have hnat : (1000717696694480179 : ℕ)^1024*1000000000000000^4133 ≤ 1000177778159167^4133*1000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000717696694480179 1000000000000000000 1000177778159167 1000000000000000 1024 4133 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000177778159167/1000000000000000 : ℝ)) (X := (1000717696694480179/1000000000000000000 : ℝ)) (by norm_num) 4133 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3715169653436637/25000000000000000000 : ℝ) ≤ ((2748029596082513581/2749000000000000000 : ℝ)+2*(520740926851/274900000000000 : ℝ)*(11261/100000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (2748029596082513581/2749000000000000000 : ℝ)+2*(520740926851/274900000000000 : ℝ)*(11261/100000 : ℝ)=(625046018733623/625000000000000 : ℝ) by norm_num, show 1+2*(3715169653436637/25000000000000000000 : ℝ)=(12503715169653436637/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(717696694480179/2000000000000000000 : ℝ)+(3715169653436637/25000000000000000000 : ℝ) ≤ ((2748029596082513581/2749000000000000000 : ℝ)+(520740926851/274900000000000 : ℝ)*((1401/10000 : ℝ)+(11261/100000 : ℝ)))^(4133/1024 : ℝ) := by
    rw [show (2748029596082513581/2749000000000000000 : ℝ)+(520740926851/274900000000000 : ℝ)*((1401/10000 : ℝ)+(11261/100000 : ℝ))=(10001257040664819/10000000000000000 : ℝ) by norm_num, show 1+(717696694480179/2000000000000000000 : ℝ)+(3715169653436637/25000000000000000000 : ℝ)=(50025372756668877749/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(717696694480179/2000000000000000000 : ℝ) ≤ ((2748029596082513581/2749000000000000000 : ℝ)+2*(520740926851/274900000000000 : ℝ)*(1401/10000 : ℝ))^(4133/1024 : ℝ) := by
    rw [show (2748029596082513581/2749000000000000000 : ℝ)+2*(520740926851/274900000000000 : ℝ)*(1401/10000 : ℝ)=(1000177778159167/1000000000000000 : ℝ) by norm_num, show 1+2*(717696694480179/2000000000000000000 : ℝ)=(1000717696694480179/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2748029596082513581/2749000000000000000 : ℝ)*(X 1 0+X 2 0)+(520740926851/274900000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11261/100000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (2748029596082513581/2749000000000000000 : ℝ)) (alpha := (520740926851/274900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2748029596082513581/2749000000000000000 : ℝ)*(X 0 1+X 2 1)+(520740926851/274900000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11261/100000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (2748029596082513581/2749000000000000000 : ℝ)) (alpha := (520740926851/274900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2748029596082513581/2749000000000000000 : ℝ)*(X 0 2+X 1 2)+(520740926851/274900000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4133/1024 : ℝ)) (lo := (11261/100000 : ℝ)) (hi := (1401/10000 : ℝ)) (c := (2748029596082513581/2749000000000000000 : ℝ)) (alpha := (520740926851/274900000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2199833703/10000000000 : ℝ)*X 0 0+(2697104849/5000000000 : ℝ)*X 0 1+(658075943/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668119857/1250000000 : ℝ)*X 1 0+(-2265587493/10000000000 : ℝ)*X 1 1+(1316151887/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5344958859/10000000000 : ℝ)*X 2 0+(2632303773/5000000000 : ℝ)*X 2 1+(-566396873/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((546792919/1250000000 : ℝ)*X 0 0+(4249010689/10000000000 : ℝ)*X 0 1+(1125854079/2500000000 : ℝ)*X 0 2+(546792919/1250000000 : ℝ)*X 1 0+(4249010689/10000000000 : ℝ)*X 1 1+(1125854079/2500000000 : ℝ)*X 1 2+(546792919/1250000000 : ℝ)*X 2 0+(4249010689/10000000000 : ℝ)*X 2 1+(1125854079/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-549959693/2500000000 : ℝ)*X 0 0+(526493233/1000000000 : ℝ)*X 0 1+(5393883723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312293867/10000000000 : ℝ)*X 1 0+(-2136311261/10000000000 : ℝ)*X 1 1+(674235473/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656146989/5000000000 : ℝ)*X 2 0+(5393883903/10000000000 : ℝ)*X 2 1+(-2136310951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2187176727/5000000000 : ℝ)*X 0 0+(2251389457/5000000000 : ℝ)*X 0 1+(2124825093/5000000000 : ℝ)*X 0 2+(2187176727/5000000000 : ℝ)*X 1 0+(2251389457/5000000000 : ℝ)*X 1 1+(2124825093/5000000000 : ℝ)*X 1 2+(2187176727/5000000000 : ℝ)*X 2 0+(2251389457/5000000000 : ℝ)*X 2 1+(2124825093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1074_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (20825341364902838393679/6872500000000000000000000000 : ℝ) := by norm_num
    linear_combination (612650901/100000000000000 : ℝ)*(base19) + (573509737/100000000000000 : ℝ)*(base23) + (23235577/100000000000000 : ℝ)*(lower2) + (3873877/5000000000000 : ℝ)*(upper3) + (47755839/100000000000000 : ℝ)*(upper5) + (5823351602497337/100000000000000 : ℝ)*(major0) + (5823351602497337/100000000000000 : ℝ)*(major1) + (5823351602497337/100000000000000 : ℝ)*(major2) + (7715938488549341/100000000000000 : ℝ)*(sp0) + (3857977281446537/50000000000000 : ℝ)*(sp1) + (3857977301017119/50000000000000 : ℝ)*(sp2) + (24567117813139/625000000000 : ℝ)*(sp3) + (8343497317/50000000000000 : ℝ)*(sp4) + (1815668073/20000000000000 : ℝ)*(sp7) + (786149585688521/20000000000000 : ℝ)*(f.failure) + (308638207021759/4000000000000 : ℝ)*(f.sum) + (1854887126921/1718125000000000000000000000 : ℝ)*base66 + (321521100102496203/274900000000000000000000000000000 : ℝ)*base68 + (1527794232961696203/274900000000000000000000000000000 : ℝ)*base70 + (4343364396180103797/274900000000000000000000000000000 : ℝ)*base71 + (7126687746773/13745000000000000000000000000 : ℝ)*base74 + (7342802214054903797/274900000000000000000000000000000 : ℝ)*base75 + (2979296549339903797/274900000000000000000000000000000 : ℝ)*base77 + (340306036981496203/274900000000000000000000000000000 : ℝ)*base80 + (54134191148543/13745000000000000000000000000 : ℝ)*base82 + (20123989/2000000000000000000000 : ℝ)*base90 + (20123989/2000000000000000000000 : ℝ)*base92 + (20123989/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (147764636327131525779/21476562500000000000000000 : ℝ) := by norm_num
    linear_combination (776605227/50000000000000 : ℝ)*(base19) + (2128398981/100000000000000 : ℝ)*(base23) + (485647239/100000000000000 : ℝ)*(lower1) + (138541963/50000000000000 : ℝ)*(upper3) + (55697819/50000000000000 : ℝ)*(lower4) + (105485513/100000000000000 : ℝ)*(upper5) + (36579246503123/625000000000 : ℝ)*(major0) + (36579246503123/625000000000 : ℝ)*(major1) + (36579246503123/625000000000 : ℝ)*(major2) + (6617689079/20000000000000 : ℝ)*(sp2) + (7754814505100953/100000000000000 : ℝ)*(sp4) + (7754812951890499/100000000000000 : ℝ)*(sp5) + (121168426379009/1562500000000 : ℝ)*(sp6) + (1975272073277947/50000000000000 : ℝ)*(sp7) + (1975272073277947/50000000000000 : ℝ)*(f.failure) + (7754814505100953/100000000000000 : ℝ)*(f.sum) + (119683755857/21476562500000000000000000 : ℝ)*base65 + (43492666591165287/1718125000000000000000000000000 : ℝ)*base68 + (2429134951887897/429531250000000000000000000000 : ℝ)*base69 + (163303462568371419/859062500000000000000000000000 : ℝ)*base71 + (9729149629663/2749000000000000000000000000 : ℝ)*base73 + (192110490269080963/1718125000000000000000000000000 : ℝ)*base75 + (4603253077253581/859062500000000000000000000000 : ℝ)*base78 + (3602505410347787/1718125000000000000000000000000 : ℝ)*base80 + (680246281419/171812500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (72782623/5000000000000000000000 : ℝ)*base90 + (72782623/5000000000000000000000 : ℝ)*base92 + (72782623/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1074_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1401/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11261/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1074_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1074_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1074_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1074_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1074_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4133/1024 : ℝ) ≤ p) (hpb : p ≤ (8267/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (148148691/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7031/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11211/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11263/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1751/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1074_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
