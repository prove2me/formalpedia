-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1325_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:44:53.909649+00:00
-- url     : https://prove2.me/submissions/fbf47478-fbe5-486b-acf1-30462bc546f7

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
theorem support_rectangle_w1325_s3_0 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-128550411/625000000 : ℝ)*x 0 + (5429401841/10000000000 : ℝ)*x 1 + (2614764039/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (128550411/625000000 : ℝ)^4285 ≤ (12517756751611/100000000000000 : ℝ)^3261 := by
    have hnat : (128550411 : ℕ)^4285*100000000000000^3261 ≤ 12517756751611^3261*625000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      128550411 625000000 12517756751611 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429401841/10000000000 : ℝ)^4285 ≤ (4481881480437/10000000000000 : ℝ)^3261 := by
    have hnat : (5429401841 : ℕ)^4285*10000000000000^3261 ≤ 4481881480437^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429401841 10000000000 4481881480437 10000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614764039/5000000000 : ℝ)^4285 ≤ (42663428435971/100000000000000 : ℝ)^3261 := by
    have hnat : (2614764039 : ℕ)^4285*100000000000000^3261 ≤ 42663428435971^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614764039 5000000000 42663428435971 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-128550411/625000000 : ℝ), (5429401841/10000000000 : ℝ), (2614764039/5000000000 : ℝ)] ![(12517756751611/100000000000000 : ℝ), (4481881480437/10000000000000 : ℝ), (42663428435971/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-128550411/625000000 : ℝ)|^4285 ≤ (12517756751611/100000000000000 : ℝ)^3261
        have hw : |(-128550411/625000000 : ℝ)|=(128550411/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429401841/10000000000 : ℝ)|^4285 ≤ (4481881480437/10000000000000 : ℝ)^3261
        have hw : |(5429401841/10000000000 : ℝ)|=(5429401841/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614764039/5000000000 : ℝ)|^4285 ≤ (42663428435971/100000000000000 : ℝ)^3261
        have hw : |(2614764039/5000000000 : ℝ)|=(2614764039/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s3_1 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676653469/5000000000 : ℝ)*x 0 + (-1079501359/5000000000 : ℝ)*x 1 + (209181117/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676653469/5000000000 : ℝ)^4285 ≤ (43995237882519/100000000000000 : ℝ)^3261 := by
    have hnat : (2676653469 : ℕ)^4285*100000000000000^3261 ≤ 43995237882519^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676653469 5000000000 43995237882519 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1079501359/5000000000 : ℝ)^4285 ≤ (667066765269/5000000000000 : ℝ)^3261 := by
    have hnat : (1079501359 : ℕ)^4285*5000000000000^3261 ≤ 667066765269^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079501359 5000000000 667066765269 5000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (209181117/400000000 : ℝ)^4285 ≤ (42663426795817/100000000000000 : ℝ)^3261 := by
    have hnat : (209181117 : ℕ)^4285*100000000000000^3261 ≤ 42663426795817^3261*400000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209181117 400000000 42663426795817 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676653469/5000000000 : ℝ), (-1079501359/5000000000 : ℝ), (209181117/400000000 : ℝ)] ![(43995237882519/100000000000000 : ℝ), (667066765269/5000000000000 : ℝ), (42663426795817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676653469/5000000000 : ℝ)|^4285 ≤ (43995237882519/100000000000000 : ℝ)^3261
        have hw : |(2676653469/5000000000 : ℝ)|=(2676653469/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1079501359/5000000000 : ℝ)|^4285 ≤ (667066765269/5000000000000 : ℝ)^3261
        have hw : |(-1079501359/5000000000 : ℝ)|=(1079501359/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(209181117/400000000 : ℝ)|^4285 ≤ (42663426795817/100000000000000 : ℝ)^3261
        have hw : |(209181117/400000000 : ℝ)|=(209181117/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s3_2 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070661417/2000000000 : ℝ)*x 0 + (2614763887/5000000000 : ℝ)*x 1 + (-1079501361/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070661417/2000000000 : ℝ)^4285 ≤ (10998809867493/25000000000000 : ℝ)^3261 := by
    have hnat : (1070661417 : ℕ)^4285*25000000000000^3261 ≤ 10998809867493^3261*2000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070661417 2000000000 10998809867493 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2614763887/5000000000 : ℝ)^4285 ≤ (42663425177103/100000000000000 : ℝ)^3261 := by
    have hnat : (2614763887 : ℕ)^4285*100000000000000^3261 ≤ 42663425177103^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614763887 5000000000 42663425177103 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079501361/5000000000 : ℝ)^4285 ≤ (667066766893/5000000000000 : ℝ)^3261 := by
    have hnat : (1079501361 : ℕ)^4285*5000000000000^3261 ≤ 667066766893^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079501361 5000000000 667066766893 5000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070661417/2000000000 : ℝ), (2614763887/5000000000 : ℝ), (-1079501361/5000000000 : ℝ)] ![(10998809867493/25000000000000 : ℝ), (42663425177103/100000000000000 : ℝ), (667066766893/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070661417/2000000000 : ℝ)|^4285 ≤ (10998809867493/25000000000000 : ℝ)^3261
        have hw : |(1070661417/2000000000 : ℝ)|=(1070661417/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2614763887/5000000000 : ℝ)|^4285 ≤ (42663425177103/100000000000000 : ℝ)^3261
        have hw : |(2614763887/5000000000 : ℝ)|=(2614763887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1079501361/5000000000 : ℝ)|^4285 ≤ (667066766893/5000000000000 : ℝ)^3261
        have hw : |(-1079501361/5000000000 : ℝ)|=(1079501361/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s3_3 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4329910743/10000000000 : ℝ)*x 0 + (12895703/31250000 : ℝ)*x 1 + (4542598873/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329910743/10000000000 : ℝ)^4285 ≤ (2080694033129/6250000000000 : ℝ)^3261 := by
    have hnat : (4329910743 : ℕ)^4285*6250000000000^3261 ≤ 2080694033129^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329910743 10000000000 2080694033129 6250000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (12895703/31250000 : ℝ)^4285 ≤ (31252618348407/100000000000000 : ℝ)^3261 := by
    have hnat : (12895703 : ℕ)^4285*100000000000000^3261 ≤ 31252618348407^3261*31250000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      12895703 31250000 31252618348407 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4542598873/10000000000 : ℝ)^4285 ≤ (35456277096909/100000000000000 : ℝ)^3261 := by
    have hnat : (4542598873 : ℕ)^4285*100000000000000^3261 ≤ 35456277096909^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4542598873 10000000000 35456277096909 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329910743/10000000000 : ℝ), (12895703/31250000 : ℝ), (4542598873/10000000000 : ℝ)] ![(2080694033129/6250000000000 : ℝ), (31252618348407/100000000000000 : ℝ), (35456277096909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329910743/10000000000 : ℝ)|^4285 ≤ (2080694033129/6250000000000 : ℝ)^3261
        have hw : |(4329910743/10000000000 : ℝ)|=(4329910743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(12895703/31250000 : ℝ)|^4285 ≤ (31252618348407/100000000000000 : ℝ)^3261
        have hw : |(12895703/31250000 : ℝ)|=(12895703/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4542598873/10000000000 : ℝ)|^4285 ≤ (35456277096909/100000000000000 : ℝ)^3261
        have hw : |(4542598873/10000000000 : ℝ)|=(4542598873/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s3_4 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2056827109/10000000000 : ℝ)*x 0 + (653796197/1250000000 : ℝ)*x 1 + (1085711003/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2056827109/10000000000 : ℝ)^4285 ≤ (12517920956533/100000000000000 : ℝ)^3261 := by
    have hnat : (2056827109 : ℕ)^4285*100000000000000^3261 ≤ 12517920956533^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2056827109 10000000000 12517920956533 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (653796197/1250000000 : ℝ)^4285 ≤ (42672449491177/100000000000000 : ℝ)^3261 := by
    have hnat : (653796197 : ℕ)^4285*100000000000000^3261 ≤ 42672449491177^3261*1250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      653796197 1250000000 42672449491177 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1085711003/2000000000 : ℝ)^4285 ≤ (22404814766863/50000000000000 : ℝ)^3261 := by
    have hnat : (1085711003 : ℕ)^4285*50000000000000^3261 ≤ 22404814766863^3261*2000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085711003 2000000000 22404814766863 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2056827109/10000000000 : ℝ), (653796197/1250000000 : ℝ), (1085711003/2000000000 : ℝ)] ![(12517920956533/100000000000000 : ℝ), (42672449491177/100000000000000 : ℝ), (22404814766863/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2056827109/10000000000 : ℝ)|^4285 ≤ (12517920956533/100000000000000 : ℝ)^3261
        have hw : |(-2056827109/10000000000 : ℝ)|=(2056827109/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(653796197/1250000000 : ℝ)|^4285 ≤ (42672449491177/100000000000000 : ℝ)^3261
        have hw : |(653796197/1250000000 : ℝ)|=(653796197/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1085711003/2000000000 : ℝ)|^4285 ≤ (22404814766863/50000000000000 : ℝ)^3261
        have hw : |(1085711003/2000000000 : ℝ)|=(1085711003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s3_5 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2650961959/5000000000 : ℝ)*x 0 + (-489993967/2500000000 : ℝ)*x 1 + (339284701/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2650961959/5000000000 : ℝ)^4285 ≤ (10860297673997/25000000000000 : ℝ)^3261 := by
    have hnat : (2650961959 : ℕ)^4285*25000000000000^3261 ≤ 10860297673997^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2650961959 5000000000 10860297673997 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (489993967/2500000000 : ℝ)^4285 ≤ (11749177582877/100000000000000 : ℝ)^3261 := by
    have hnat : (489993967 : ℕ)^4285*100000000000000^3261 ≤ 11749177582877^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      489993967 2500000000 11749177582877 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (339284701/625000000 : ℝ)^4285 ≤ (2240481585693/5000000000000 : ℝ)^3261 := by
    have hnat : (339284701 : ℕ)^4285*5000000000000^3261 ≤ 2240481585693^3261*625000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339284701 625000000 2240481585693 5000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2650961959/5000000000 : ℝ), (-489993967/2500000000 : ℝ), (339284701/625000000 : ℝ)] ![(10860297673997/25000000000000 : ℝ), (11749177582877/100000000000000 : ℝ), (2240481585693/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2650961959/5000000000 : ℝ)|^4285 ≤ (10860297673997/25000000000000 : ℝ)^3261
        have hw : |(2650961959/5000000000 : ℝ)|=(2650961959/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-489993967/2500000000 : ℝ)|^4285 ≤ (11749177582877/100000000000000 : ℝ)^3261
        have hw : |(-489993967/2500000000 : ℝ)|=(489993967/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(339284701/625000000 : ℝ)|^4285 ≤ (2240481585693/5000000000000 : ℝ)^3261
        have hw : |(339284701/625000000 : ℝ)|=(339284701/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s3_6 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5301925629/10000000000 : ℝ)*x 0 + (1085710803/2000000000 : ℝ)*x 1 + (-979987591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5301925629/10000000000 : ℝ)^4285 ≤ (10860302279301/25000000000000 : ℝ)^3261 := by
    have hnat : (5301925629 : ℕ)^4285*25000000000000^3261 ≤ 10860302279301^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5301925629 10000000000 10860302279301 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1085710803/2000000000 : ℝ)^4285 ≤ (5601202335911/12500000000000 : ℝ)^3261 := by
    have hnat : (1085710803 : ℕ)^4285*12500000000000^3261 ≤ 5601202335911^3261*2000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1085710803 2000000000 5601202335911 12500000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (979987591/5000000000 : ℝ)^4285 ≤ (5874586089653/50000000000000 : ℝ)^3261 := by
    have hnat : (979987591 : ℕ)^4285*50000000000000^3261 ≤ 5874586089653^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      979987591 5000000000 5874586089653 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5301925629/10000000000 : ℝ), (1085710803/2000000000 : ℝ), (-979987591/5000000000 : ℝ)] ![(10860302279301/25000000000000 : ℝ), (5601202335911/12500000000000 : ℝ), (5874586089653/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5301925629/10000000000 : ℝ)|^4285 ≤ (10860302279301/25000000000000 : ℝ)^3261
        have hw : |(5301925629/10000000000 : ℝ)|=(5301925629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1085710803/2000000000 : ℝ)|^4285 ≤ (5601202335911/12500000000000 : ℝ)^3261
        have hw : |(1085710803/2000000000 : ℝ)|=(1085710803/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-979987591/5000000000 : ℝ)|^4285 ≤ (5874586089653/50000000000000 : ℝ)^3261
        have hw : |(-979987591/5000000000 : ℝ)|=(979987591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s3_7 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4329953317/10000000000 : ℝ)*x 0 + (1135211871/2500000000 : ℝ)*x 1 + (4128386523/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4329953317/10000000000 : ℝ)^4285 ≤ (8322883663699/25000000000000 : ℝ)^3261 := by
    have hnat : (4329953317 : ℕ)^4285*25000000000000^3261 ≤ 8322883663699^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4329953317 10000000000 8322883663699 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1135211871/2500000000 : ℝ)^4285 ≤ (7087663098753/20000000000000 : ℝ)^3261 := by
    have hnat : (1135211871 : ℕ)^4285*20000000000000^3261 ≤ 7087663098753^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1135211871 2500000000 7087663098753 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4128386523/10000000000 : ℝ)^4285 ≤ (6254029966797/20000000000000 : ℝ)^3261 := by
    have hnat : (4128386523 : ℕ)^4285*20000000000000^3261 ≤ 6254029966797^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128386523 10000000000 6254029966797 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4329953317/10000000000 : ℝ), (1135211871/2500000000 : ℝ), (4128386523/10000000000 : ℝ)] ![(8322883663699/25000000000000 : ℝ), (7087663098753/20000000000000 : ℝ), (6254029966797/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4329953317/10000000000 : ℝ)|^4285 ≤ (8322883663699/25000000000000 : ℝ)^3261
        have hw : |(4329953317/10000000000 : ℝ)|=(4329953317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1135211871/2500000000 : ℝ)|^4285 ≤ (7087663098753/20000000000000 : ℝ)^3261
        have hw : |(1135211871/2500000000 : ℝ)|=(1135211871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4128386523/10000000000 : ℝ)|^4285 ≤ (6254029966797/20000000000000 : ℝ)^3261
        have hw : |(4128386523/10000000000 : ℝ)|=(4128386523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1325_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16173/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4869/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (5399/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15027/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16173/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4869/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16173/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4869/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16173/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4869/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16173/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4869/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16173/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4869/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16173/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4869/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4869/50000 : ℝ) ^ (1071/256 : ℝ) ≤ (5863655579532101/100000000000000000000 : ℝ) := by
    have hpowers : (4869/50000 : ℝ)^1071 ≤ (5863655579532101/100000000000000000000 : ℝ)^256 := by
      have hnat : (4869 : ℕ)^1071*100000000000000000000^256 ≤ 5863655579532101^256*50000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4869 50000 5863655579532101 100000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4869/50000 : ℝ)) (X := (5863655579532101/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hpowhi : (16173/100000 : ℝ) ^ (1071/256 : ℝ) ≤ (48966745802706611/100000000000000000000 : ℝ) := by
    have hpowers : (16173/100000 : ℝ)^1071 ≤ (48966745802706611/100000000000000000000 : ℝ)^256 := by
      have hnat : (16173 : ℕ)^1071*100000000000000000000^256 ≤ 48966745802706611^256*100000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16173 100000 48966745802706611 100000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16173/100000 : ℝ)) (X := (48966745802706611/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005863655579532101/50000000000000000000 : ℝ) ≤ (10000280304174229/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (50005863655579532101/50000000000000000000 : ℝ)^256 ≤ (10000280304174229/10000000000000000 : ℝ)^1071 := by
      have hnat : (50005863655579532101 : ℕ)^256*10000000000000000^1071 ≤ 10000280304174229^1071*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005863655579532101 50000000000000000000 10000280304174229 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000280304174229/10000000000000000 : ℝ)) (X := (50005863655579532101/50000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (12506853800172779839/12500000000000000000 : ℝ) ≤ (10001310331966353/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (12506853800172779839/12500000000000000000 : ℝ)^256 ≤ (10001310331966353/10000000000000000 : ℝ)^1071 := by
      have hnat : (12506853800172779839 : ℕ)^256*10000000000000000^1071 ≤ 10001310331966353^1071*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12506853800172779839 12500000000000000000 10001310331966353 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001310331966353/10000000000000000 : ℝ)) (X := (12506853800172779839/12500000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50048966745802706611/50000000000000000000 : ℝ) ≤ (10002340359758477/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (50048966745802706611/50000000000000000000 : ℝ)^256 ≤ (10002340359758477/10000000000000000 : ℝ)^1071 := by
      have hnat : (50048966745802706611 : ℕ)^256*10000000000000000^1071 ≤ 10002340359758477^1071*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50048966745802706611 50000000000000000000 10002340359758477 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002340359758477/10000000000000000 : ℝ)) (X := (50048966745802706611/50000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5863655579532101/100000000000000000000 : ℝ) ≤ ((7147971437342417399/7150000000000000000 : ℝ)+2*(257506948031/160875000000000 : ℝ)*(4869/50000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (7147971437342417399/7150000000000000000 : ℝ)+2*(257506948031/160875000000000 : ℝ)*(4869/50000 : ℝ)=(10000280304174229/10000000000000000 : ℝ) by norm_num, show 1+2*(5863655579532101/100000000000000000000 : ℝ)=(50005863655579532101/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48966745802706611/100000000000000000000 : ℝ)+(5863655579532101/100000000000000000000 : ℝ) ≤ ((7147971437342417399/7150000000000000000 : ℝ)+(257506948031/160875000000000 : ℝ)*((16173/100000 : ℝ)+(4869/50000 : ℝ)))^(1071/256 : ℝ) := by
    rw [show (7147971437342417399/7150000000000000000 : ℝ)+(257506948031/160875000000000 : ℝ)*((16173/100000 : ℝ)+(4869/50000 : ℝ))=(10001310331966353/10000000000000000 : ℝ) by norm_num, show 1+(48966745802706611/100000000000000000000 : ℝ)+(5863655579532101/100000000000000000000 : ℝ)=(12506853800172779839/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48966745802706611/100000000000000000000 : ℝ) ≤ ((7147971437342417399/7150000000000000000 : ℝ)+2*(257506948031/160875000000000 : ℝ)*(16173/100000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (7147971437342417399/7150000000000000000 : ℝ)+2*(257506948031/160875000000000 : ℝ)*(16173/100000 : ℝ)=(10002340359758477/10000000000000000 : ℝ) by norm_num, show 1+2*(48966745802706611/100000000000000000000 : ℝ)=(50048966745802706611/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7147971437342417399/7150000000000000000 : ℝ)*(X 1 0+X 2 0)+(257506948031/160875000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (4869/50000 : ℝ)) (hi := (16173/100000 : ℝ)) (c := (7147971437342417399/7150000000000000000 : ℝ)) (alpha := (257506948031/160875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7147971437342417399/7150000000000000000 : ℝ)*(X 0 1+X 2 1)+(257506948031/160875000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (4869/50000 : ℝ)) (hi := (16173/100000 : ℝ)) (c := (7147971437342417399/7150000000000000000 : ℝ)) (alpha := (257506948031/160875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7147971437342417399/7150000000000000000 : ℝ)*(X 0 2+X 1 2)+(257506948031/160875000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (4869/50000 : ℝ)) (hi := (16173/100000 : ℝ)) (c := (7147971437342417399/7150000000000000000 : ℝ)) (alpha := (257506948031/160875000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-128550411/625000000 : ℝ)*X 0 0+(5429401841/10000000000 : ℝ)*X 0 1+(2614764039/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676653469/5000000000 : ℝ)*X 1 0+(-1079501359/5000000000 : ℝ)*X 1 1+(209181117/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070661417/2000000000 : ℝ)*X 2 0+(2614763887/5000000000 : ℝ)*X 2 1+(-1079501361/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4329910743/10000000000 : ℝ)*X 0 0+(12895703/31250000 : ℝ)*X 0 1+(4542598873/10000000000 : ℝ)*X 0 2+(4329910743/10000000000 : ℝ)*X 1 0+(12895703/31250000 : ℝ)*X 1 1+(4542598873/10000000000 : ℝ)*X 1 2+(4329910743/10000000000 : ℝ)*X 2 0+(12895703/31250000 : ℝ)*X 2 1+(4542598873/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2056827109/10000000000 : ℝ)*X 0 0+(653796197/1250000000 : ℝ)*X 0 1+(1085711003/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2650961959/5000000000 : ℝ)*X 1 0+(-489993967/2500000000 : ℝ)*X 1 1+(339284701/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5301925629/10000000000 : ℝ)*X 2 0+(1085710803/2000000000 : ℝ)*X 2 1+(-979987591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4329953317/10000000000 : ℝ)*X 0 0+(1135211871/2500000000 : ℝ)*X 0 1+(4128386523/10000000000 : ℝ)*X 0 2+(4329953317/10000000000 : ℝ)*X 1 0+(1135211871/2500000000 : ℝ)*X 1 1+(4128386523/10000000000 : ℝ)*X 1 2+(4329953317/10000000000 : ℝ)*X 2 0+(1135211871/2500000000 : ℝ)*X 2 1+(4128386523/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (62340940873843053273049641/22343750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (599438421/100000000000000 : ℝ)*(base19) + (140221511/25000000000000 : ℝ)*(base23) + (100947113/100000000000000 : ℝ)*(lower2) + (56719289/50000000000000 : ℝ)*(upper3) + (3381137/50000000000000 : ℝ)*(lower4) + (231474086951903/6250000000000 : ℝ)*(major0) + (231474086951903/6250000000000 : ℝ)*(major1) + (231474086951903/6250000000000 : ℝ)*(major2) + (12507909188039/250000000000 : ℝ)*(sp0) + (500316789790683/10000000000000 : ℝ)*(sp1) + (5003167936459207/100000000000000 : ℝ)*(sp2) + (2403998293372847/100000000000000 : ℝ)*(sp3) + (96442593/2000000000000 : ℝ)*(sp4) + (389873999/10000000000000 : ℝ)*(sp7) + (2404002192112837/100000000000000 : ℝ)*(f.failure) + (5003168497345251/100000000000000 : ℝ)*(f.sum) + (61714567386877/32175000000000000000000000000 : ℝ)*base65 + (2270404554879942673/402187500000000000000000000000000 : ℝ)*base67 + (924200306737869827/402187500000000000000000000000000 : ℝ)*base70 + (239424277705880173/402187500000000000000000000000000 : ℝ)*base71 + (26070461650513/8043750000000000000000000000 : ℝ)*base73 + (579089728425369827/402187500000000000000000000000000 : ℝ)*base76 + (1341170608476932327/402187500000000000000000000000000 : ℝ)*base78 + (2807239666859432327/402187500000000000000000000000000 : ℝ)*base80 + (14630917593173/32175000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (2716611/625000000000000000000 : ℝ)*base90 + (2716611/625000000000000000000 : ℝ)*base92 + (2716611/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1090788930337955102063790489/178750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1577136163/100000000000000 : ℝ)*(base19) + (1841032699/50000000000000 : ℝ)*(base23) + (340006651/100000000000000 : ℝ)*(upper3) + (92633723/100000000000000 : ℝ)*(lower4) + (45036507/25000000000000 : ℝ)*(upper5) + (1867565982782121/50000000000000 : ℝ)*(major0) + (1867565982782121/50000000000000 : ℝ)*(major1) + (1867565982782121/50000000000000 : ℝ)*(major2) + (3029689451/12500000000000 : ℝ)*(sp1) + (13846936367/25000000000000 : ℝ)*(sp2) + (5045784612342677/100000000000000 : ℝ)*(sp4) + (1009151759538181/20000000000000 : ℝ)*(sp5) + (504572554253181/10000000000000 : ℝ)*(sp6) + (2424479115375269/100000000000000 : ℝ)*(sp7) + (2424479115375269/100000000000000 : ℝ)*(f.failure) + (5045784612342677/100000000000000 : ℝ)*(f.sum) + (1842385994333/1340625000000000000000000000 : ℝ)*base66 + (6290352417406369837/1072500000000000000000000000000000 : ℝ)*base67 + (6325094238091369837/1072500000000000000000000000000000 : ℝ)*base69 + (20096426965028869837/1072500000000000000000000000000000 : ℝ)*base71 + (8729020613483/1340625000000000000000000000 : ℝ)*base74 + (291221330528869837/1072500000000000000000000000000000 : ℝ)*base75 + (17492884763768869837/1072500000000000000000000000000000 : ℝ)*base77 + (24820846081231369837/1072500000000000000000000000000000 : ℝ)*base79 + (26228886535639/10725000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (6005507/625000000000000000000 : ℝ)*base90 + (6005507/625000000000000000000 : ℝ)*base92 + (6005507/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1325_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16173/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4869/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5399/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15027/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1325_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1325_s4_0 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2058407883/10000000000 : ℝ)*x 0 + (5416471537/10000000000 : ℝ)*x 1 + (2620703861/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2058407883/10000000000 : ℝ)^4285 ≤ (12530564145291/100000000000000 : ℝ)^3261 := by
    have hnat : (2058407883 : ℕ)^4285*100000000000000^3261 ≤ 12530564145291^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058407883 10000000000 12530564145291 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5416471537/10000000000 : ℝ)^4285 ≤ (4467861266661/10000000000000 : ℝ)^3261 := by
    have hnat : (5416471537 : ℕ)^4285*10000000000000^3261 ≤ 4467861266661^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416471537 10000000000 4467861266661 10000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620703861/5000000000 : ℝ)^4285 ≤ (427908231759/1000000000000 : ℝ)^3261 := by
    have hnat : (2620703861 : ℕ)^4285*1000000000000^3261 ≤ 427908231759^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620703861 5000000000 427908231759 1000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2058407883/10000000000 : ℝ), (5416471537/10000000000 : ℝ), (2620703861/5000000000 : ℝ)] ![(12530564145291/100000000000000 : ℝ), (4467861266661/10000000000000 : ℝ), (427908231759/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2058407883/10000000000 : ℝ)|^4285 ≤ (12530564145291/100000000000000 : ℝ)^3261
        have hw : |(-2058407883/10000000000 : ℝ)|=(2058407883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5416471537/10000000000 : ℝ)|^4285 ≤ (4467861266661/10000000000000 : ℝ)^3261
        have hw : |(5416471537/10000000000 : ℝ)|=(5416471537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620703861/5000000000 : ℝ)|^4285 ≤ (427908231759/1000000000000 : ℝ)^3261
        have hw : |(2620703861/5000000000 : ℝ)|=(2620703861/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s4_1 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337505341/2500000000 : ℝ)*x 0 + (-53691831/250000000 : ℝ)*x 1 + (2620703791/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337505341/2500000000 : ℝ)^4285 ≤ (879195207749/2000000000000 : ℝ)^3261 := by
    have hnat : (1337505341 : ℕ)^4285*2000000000000^3261 ≤ 879195207749^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337505341 2500000000 879195207749 2000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (53691831/250000000 : ℝ)^4285 ≤ (6624708961963/50000000000000 : ℝ)^3261 := by
    have hnat : (53691831 : ℕ)^4285*50000000000000^3261 ≤ 6624708961963^3261*250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53691831 250000000 6624708961963 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620703791/5000000000 : ℝ)^4285 ≤ (8558164334807/20000000000000 : ℝ)^3261 := by
    have hnat : (2620703791 : ℕ)^4285*20000000000000^3261 ≤ 8558164334807^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620703791 5000000000 8558164334807 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337505341/2500000000 : ℝ), (-53691831/250000000 : ℝ), (2620703791/5000000000 : ℝ)] ![(879195207749/2000000000000 : ℝ), (6624708961963/50000000000000 : ℝ), (8558164334807/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337505341/2500000000 : ℝ)|^4285 ≤ (879195207749/2000000000000 : ℝ)^3261
        have hw : |(1337505341/2500000000 : ℝ)|=(1337505341/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-53691831/250000000 : ℝ)|^4285 ≤ (6624708961963/50000000000000 : ℝ)^3261
        have hw : |(-53691831/250000000 : ℝ)|=(53691831/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620703791/5000000000 : ℝ)|^4285 ≤ (8558164334807/20000000000000 : ℝ)^3261
        have hw : |(2620703791/5000000000 : ℝ)|=(2620703791/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s4_2 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2675010699/5000000000 : ℝ)*x 0 + (1310351829/2500000000 : ℝ)*x 1 + (-2147673547/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2675010699/5000000000 : ℝ)^4285 ≤ (8791952150909/20000000000000 : ℝ)^3261 := by
    have hnat : (2675010699 : ℕ)^4285*20000000000000^3261 ≤ 8791952150909^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2675010699 5000000000 8791952150909 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1310351829/2500000000 : ℝ)^4285 ≤ (42790818820493/100000000000000 : ℝ)^3261 := by
    have hnat : (1310351829 : ℕ)^4285*100000000000000^3261 ≤ 42790818820493^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310351829 2500000000 42790818820493 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2147673547/10000000000 : ℝ)^4285 ≤ (6624710206297/50000000000000 : ℝ)^3261 := by
    have hnat : (2147673547 : ℕ)^4285*50000000000000^3261 ≤ 6624710206297^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2147673547 10000000000 6624710206297 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2675010699/5000000000 : ℝ), (1310351829/2500000000 : ℝ), (-2147673547/10000000000 : ℝ)] ![(8791952150909/20000000000000 : ℝ), (42790818820493/100000000000000 : ℝ), (6624710206297/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2675010699/5000000000 : ℝ)|^4285 ≤ (8791952150909/20000000000000 : ℝ)^3261
        have hw : |(2675010699/5000000000 : ℝ)|=(2675010699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1310351829/2500000000 : ℝ)|^4285 ≤ (42790818820493/100000000000000 : ℝ)^3261
        have hw : |(1310351829/2500000000 : ℝ)|=(1310351829/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2147673547/10000000000 : ℝ)|^4285 ≤ (6624710206297/50000000000000 : ℝ)^3261
        have hw : |(-2147673547/10000000000 : ℝ)|=(2147673547/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s4_3 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4330883127/10000000000 : ℝ)*x 0 + (4152320539/10000000000 : ℝ)*x 1 + (4516661137/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330883127/10000000000 : ℝ)^4285 ≤ (33300928847897/100000000000000 : ℝ)^3261 := by
    have hnat : (4330883127 : ℕ)^4285*100000000000000^3261 ≤ 33300928847897^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330883127 10000000000 33300928847897 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4152320539/10000000000 : ℝ)^4285 ≤ (15754289621899/50000000000000 : ℝ)^3261 := by
    have hnat : (4152320539 : ℕ)^4285*50000000000000^3261 ≤ 15754289621899^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4152320539 10000000000 15754289621899 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4516661137/10000000000 : ℝ)^4285 ≤ (1759524594341/5000000000000 : ℝ)^3261 := by
    have hnat : (4516661137 : ℕ)^4285*5000000000000^3261 ≤ 1759524594341^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4516661137 10000000000 1759524594341 5000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330883127/10000000000 : ℝ), (4152320539/10000000000 : ℝ), (4516661137/10000000000 : ℝ)] ![(33300928847897/100000000000000 : ℝ), (15754289621899/50000000000000 : ℝ), (1759524594341/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330883127/10000000000 : ℝ)|^4285 ≤ (33300928847897/100000000000000 : ℝ)^3261
        have hw : |(4330883127/10000000000 : ℝ)|=(4330883127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4152320539/10000000000 : ℝ)|^4285 ≤ (15754289621899/50000000000000 : ℝ)^3261
        have hw : |(4152320539/10000000000 : ℝ)|=(4152320539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4516661137/10000000000 : ℝ)|^4285 ≤ (1759524594341/5000000000000 : ℝ)^3261
        have hw : |(4516661137/10000000000 : ℝ)|=(4516661137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s4_4 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-411684311/2000000000 : ℝ)*x 0 + (209682153/400000000 : ℝ)*x 1 + (5415821951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (411684311/2000000000 : ℝ)^4285 ≤ (12530673508619/100000000000000 : ℝ)^3261 := by
    have hnat : (411684311 : ℕ)^4285*100000000000000^3261 ≤ 12530673508619^3261*2000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      411684311 2000000000 12530673508619 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (209682153/400000000 : ℝ)^4285 ≤ (2674859652939/6250000000000 : ℝ)^3261 := by
    have hnat : (209682153 : ℕ)^4285*6250000000000^3261 ≤ 2674859652939^3261*400000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      209682153 400000000 2674859652939 6250000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5415821951/10000000000 : ℝ)^4285 ≤ (223357860167/500000000000 : ℝ)^3261 := by
    have hnat : (5415821951 : ℕ)^4285*500000000000^3261 ≤ 223357860167^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5415821951 10000000000 223357860167 500000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-411684311/2000000000 : ℝ), (209682153/400000000 : ℝ), (5415821951/10000000000 : ℝ)] ![(12530673508619/100000000000000 : ℝ), (2674859652939/6250000000000 : ℝ), (223357860167/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-411684311/2000000000 : ℝ)|^4285 ≤ (12530673508619/100000000000000 : ℝ)^3261
        have hw : |(-411684311/2000000000 : ℝ)|=(411684311/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(209682153/400000000 : ℝ)|^4285 ≤ (2674859652939/6250000000000 : ℝ)^3261
        have hw : |(209682153/400000000 : ℝ)|=(209682153/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5415821951/10000000000 : ℝ)|^4285 ≤ (223357860167/500000000000 : ℝ)^3261
        have hw : |(5415821951/10000000000 : ℝ)|=(5415821951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s4_5 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652509119/5000000000 : ℝ)*x 0 + (-493314773/2500000000 : ℝ)*x 1 + (1353955487/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652509119/5000000000 : ℝ)^4285 ≤ (43474508262197/100000000000000 : ℝ)^3261 := by
    have hnat : (2652509119 : ℕ)^4285*100000000000000^3261 ≤ 43474508262197^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652509119 5000000000 43474508262197 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (493314773/2500000000 : ℝ)^4285 ≤ (11853919719837/100000000000000 : ℝ)^3261 := by
    have hnat : (493314773 : ℕ)^4285*100000000000000^3261 ≤ 11853919719837^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      493314773 2500000000 11853919719837 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1353955487/2500000000 : ℝ)^4285 ≤ (11167893000221/25000000000000 : ℝ)^3261 := by
    have hnat : (1353955487 : ℕ)^4285*25000000000000^3261 ≤ 11167893000221^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353955487 2500000000 11167893000221 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652509119/5000000000 : ℝ), (-493314773/2500000000 : ℝ), (1353955487/2500000000 : ℝ)] ![(43474508262197/100000000000000 : ℝ), (11853919719837/100000000000000 : ℝ), (11167893000221/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652509119/5000000000 : ℝ)|^4285 ≤ (43474508262197/100000000000000 : ℝ)^3261
        have hw : |(2652509119/5000000000 : ℝ)|=(2652509119/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-493314773/2500000000 : ℝ)|^4285 ≤ (11853919719837/100000000000000 : ℝ)^3261
        have hw : |(-493314773/2500000000 : ℝ)|=(493314773/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1353955487/2500000000 : ℝ)|^4285 ≤ (11167893000221/25000000000000 : ℝ)^3261
        have hw : |(1353955487/2500000000 : ℝ)|=(1353955487/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s4_6 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652509127/5000000000 : ℝ)*x 0 + (676977741/1250000000 : ℝ)*x 1 + (-986629549/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652509127/5000000000 : ℝ)^4285 ≤ (4347450843449/10000000000000 : ℝ)^3261 := by
    have hnat : (2652509127 : ℕ)^4285*10000000000000^3261 ≤ 4347450843449^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652509127 5000000000 4347450843449 10000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (676977741/1250000000 : ℝ)^4285 ≤ (11167892946029/25000000000000 : ℝ)^3261 := by
    have hnat : (676977741 : ℕ)^4285*25000000000000^3261 ≤ 11167892946029^3261*1250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      676977741 1250000000 11167892946029 25000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (986629549/5000000000 : ℝ)^4285 ≤ (11853919767199/100000000000000 : ℝ)^3261 := by
    have hnat : (986629549 : ℕ)^4285*100000000000000^3261 ≤ 11853919767199^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      986629549 5000000000 11853919767199 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652509127/5000000000 : ℝ), (676977741/1250000000 : ℝ), (-986629549/5000000000 : ℝ)] ![(4347450843449/10000000000000 : ℝ), (11167892946029/25000000000000 : ℝ), (11853919767199/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652509127/5000000000 : ℝ)|^4285 ≤ (4347450843449/10000000000000 : ℝ)^3261
        have hw : |(2652509127/5000000000 : ℝ)|=(2652509127/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(676977741/1250000000 : ℝ)|^4285 ≤ (11167892946029/25000000000000 : ℝ)^3261
        have hw : |(676977741/1250000000 : ℝ)|=(676977741/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-986629549/5000000000 : ℝ)|^4285 ≤ (11853919767199/100000000000000 : ℝ)^3261
        have hw : |(-986629549/5000000000 : ℝ)|=(986629549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s4_7 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4330911467/10000000000 : ℝ)*x 0 + (4515316031/10000000000 : ℝ)*x 1 + (4153672793/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4330911467/10000000000 : ℝ)^4285 ≤ (33301215186699/100000000000000 : ℝ)^3261 := by
    have hnat : (4330911467 : ℕ)^4285*100000000000000^3261 ≤ 33301215186699^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4330911467 10000000000 33301215186699 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4515316031/10000000000 : ℝ)^4285 ≤ (35176721566041/100000000000000 : ℝ)^3261 := by
    have hnat : (4515316031 : ℕ)^4285*100000000000000^3261 ≤ 35176721566041^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4515316031 10000000000 35176721566041 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4153672793/10000000000 : ℝ)^4285 ≤ (31522063234839/100000000000000 : ℝ)^3261 := by
    have hnat : (4153672793 : ℕ)^4285*100000000000000^3261 ≤ 31522063234839^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153672793 10000000000 31522063234839 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4330911467/10000000000 : ℝ), (4515316031/10000000000 : ℝ), (4153672793/10000000000 : ℝ)] ![(33301215186699/100000000000000 : ℝ), (35176721566041/100000000000000 : ℝ), (31522063234839/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4330911467/10000000000 : ℝ)|^4285 ≤ (33301215186699/100000000000000 : ℝ)^3261
        have hw : |(4330911467/10000000000 : ℝ)|=(4330911467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4515316031/10000000000 : ℝ)|^4285 ≤ (35176721566041/100000000000000 : ℝ)^3261
        have hw : |(4515316031/10000000000 : ℝ)|=(4515316031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4153672793/10000000000 : ℝ)|^4285 ≤ (31522063234839/100000000000000 : ℝ)^3261
        have hw : |(4153672793/10000000000 : ℝ)|=(4153672793/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1325_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5399/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11051/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14757/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5399/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15027/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5399/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5399/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15027/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5399/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5399/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15027/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5399/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5399/50000 : ℝ) ^ (1071/256 : ℝ) ≤ (2258609637496369/25000000000000000000 : ℝ) := by
    have hpowers : (5399/50000 : ℝ)^1071 ≤ (2258609637496369/25000000000000000000 : ℝ)^256 := by
      have hnat : (5399 : ℕ)^1071*25000000000000000000^256 ≤ 2258609637496369^256*50000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5399 50000 2258609637496369 25000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5399/50000 : ℝ)) (X := (2258609637496369/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hpowhi : (15027/100000 : ℝ) ^ (1071/256 : ℝ) ≤ (36005433321010991/100000000000000000000 : ℝ) := by
    have hpowers : (15027/100000 : ℝ)^1071 ≤ (36005433321010991/100000000000000000000 : ℝ)^256 := by
      have hnat : (15027 : ℕ)^1071*100000000000000000000^256 ≤ 36005433321010991^256*100000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15027 100000 36005433321010991 100000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15027/100000 : ℝ)) (X := (36005433321010991/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502258609637496369/12500000000000000000 : ℝ) ≤ (1250053983596657/1250000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (12502258609637496369/12500000000000000000 : ℝ)^256 ≤ (1250053983596657/1250000000000000 : ℝ)^1071 := by
      have hnat : (12502258609637496369 : ℕ)^256*1250000000000000^1071 ≤ 1250053983596657^1071*12500000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502258609637496369 12500000000000000000 1250053983596657 1250000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250053983596657/1250000000000000 : ℝ)) (X := (12502258609637496369/12500000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (100045039871870996467/100000000000000000000 : ℝ) ≤ (5000538199429849/5000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (100045039871870996467/100000000000000000000 : ℝ)^256 ≤ (5000538199429849/5000000000000000 : ℝ)^1071 := by
      have hnat : (100045039871870996467 : ℕ)^256*5000000000000000^1071 ≤ 5000538199429849^1071*100000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100045039871870996467 100000000000000000000 5000538199429849 5000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000538199429849/5000000000000000 : ℝ)) (X := (100045039871870996467/100000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50036005433321010991/50000000000000000000 : ℝ) ≤ (500086046447307/500000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (50036005433321010991/50000000000000000000 : ℝ)^256 ≤ (500086046447307/500000000000000 : ℝ)^1071 := by
      have hnat : (50036005433321010991 : ℕ)^256*500000000000000^1071 ≤ 500086046447307^1071*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50036005433321010991 50000000000000000000 500086046447307 500000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500086046447307/500000000000000 : ℝ)) (X := (50036005433321010991/50000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2258609637496369/25000000000000000000 : ℝ) ≤ ((2642369193830956137/2643125000000000000 : ℝ)+2*(322265043221/211450000000000 : ℝ)*(5399/50000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (2642369193830956137/2643125000000000000 : ℝ)+2*(322265043221/211450000000000 : ℝ)*(5399/50000 : ℝ)=(1250053983596657/1250000000000000 : ℝ) by norm_num, show 1+2*(2258609637496369/25000000000000000000 : ℝ)=(12502258609637496369/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(36005433321010991/100000000000000000000 : ℝ)+(2258609637496369/25000000000000000000 : ℝ) ≤ ((2642369193830956137/2643125000000000000 : ℝ)+(322265043221/211450000000000 : ℝ)*((15027/100000 : ℝ)+(5399/50000 : ℝ)))^(1071/256 : ℝ) := by
    rw [show (2642369193830956137/2643125000000000000 : ℝ)+(322265043221/211450000000000 : ℝ)*((15027/100000 : ℝ)+(5399/50000 : ℝ))=(5000538199429849/5000000000000000 : ℝ) by norm_num, show 1+(36005433321010991/100000000000000000000 : ℝ)+(2258609637496369/25000000000000000000 : ℝ)=(100045039871870996467/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(36005433321010991/100000000000000000000 : ℝ) ≤ ((2642369193830956137/2643125000000000000 : ℝ)+2*(322265043221/211450000000000 : ℝ)*(15027/100000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (2642369193830956137/2643125000000000000 : ℝ)+2*(322265043221/211450000000000 : ℝ)*(15027/100000 : ℝ)=(500086046447307/500000000000000 : ℝ) by norm_num, show 1+2*(36005433321010991/100000000000000000000 : ℝ)=(50036005433321010991/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2642369193830956137/2643125000000000000 : ℝ)*(X 1 0+X 2 0)+(322265043221/211450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (5399/50000 : ℝ)) (hi := (15027/100000 : ℝ)) (c := (2642369193830956137/2643125000000000000 : ℝ)) (alpha := (322265043221/211450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2642369193830956137/2643125000000000000 : ℝ)*(X 0 1+X 2 1)+(322265043221/211450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (5399/50000 : ℝ)) (hi := (15027/100000 : ℝ)) (c := (2642369193830956137/2643125000000000000 : ℝ)) (alpha := (322265043221/211450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2642369193830956137/2643125000000000000 : ℝ)*(X 0 2+X 1 2)+(322265043221/211450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (5399/50000 : ℝ)) (hi := (15027/100000 : ℝ)) (c := (2642369193830956137/2643125000000000000 : ℝ)) (alpha := (322265043221/211450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2058407883/10000000000 : ℝ)*X 0 0+(5416471537/10000000000 : ℝ)*X 0 1+(2620703861/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1337505341/2500000000 : ℝ)*X 1 0+(-53691831/250000000 : ℝ)*X 1 1+(2620703791/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2675010699/5000000000 : ℝ)*X 2 0+(1310351829/2500000000 : ℝ)*X 2 1+(-2147673547/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4330883127/10000000000 : ℝ)*X 0 0+(4152320539/10000000000 : ℝ)*X 0 1+(4516661137/10000000000 : ℝ)*X 0 2+(4330883127/10000000000 : ℝ)*X 1 0+(4152320539/10000000000 : ℝ)*X 1 1+(4516661137/10000000000 : ℝ)*X 1 2+(4330883127/10000000000 : ℝ)*X 2 0+(4152320539/10000000000 : ℝ)*X 2 1+(4516661137/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-411684311/2000000000 : ℝ)*X 0 0+(209682153/400000000 : ℝ)*X 0 1+(5415821951/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652509119/5000000000 : ℝ)*X 1 0+(-493314773/2500000000 : ℝ)*X 1 1+(1353955487/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652509127/5000000000 : ℝ)*X 2 0+(676977741/1250000000 : ℝ)*X 2 1+(-986629549/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4330911467/10000000000 : ℝ)*X 0 0+(4515316031/10000000000 : ℝ)*X 0 1+(4153672793/10000000000 : ℝ)*X 0 2+(4330911467/10000000000 : ℝ)*X 1 0+(4515316031/10000000000 : ℝ)*X 1 1+(4153672793/10000000000 : ℝ)*X 1 2+(4330911467/10000000000 : ℝ)*X 2 0+(4515316031/10000000000 : ℝ)*X 2 1+(4153672793/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (118356489235801735777486749/13215625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (244642337/12500000000000 : ℝ)*(base19) + (1008600089/50000000000000 : ℝ)*(base23) + (19105191/50000000000000 : ℝ)*(lower2) + (42249549/12500000000000 : ℝ)*(upper3) + (636521/1250000000000 : ℝ)*(lower4) + (211424958802467/5000000000000 : ℝ)*(major0) + (211424958802467/5000000000000 : ℝ)*(major1) + (211424958802467/5000000000000 : ℝ)*(major2) + (1142448838823853/20000000000000 : ℝ)*(sp0) + (5712271670032911/100000000000000 : ℝ)*(sp1) + (571227160997143/10000000000000 : ℝ)*(sp2) + (171543873885589/6250000000000 : ℝ)*(sp3) + (14716526171/50000000000000 : ℝ)*(sp4) + (22444230989/100000000000000 : ℝ)*(sp7) + (2744724426400413/100000000000000 : ℝ)*(f.failure) + (5712273627171607/100000000000000 : ℝ)*(f.sum) + (3923842054591/2114500000000000000000000000 : ℝ)*base65 + (46647488274321229/13215625000000000000000000000000 : ℝ)*base67 + (47166604184281573/6607812500000000000000000000000 : ℝ)*base70 + (11305652611326401/3303906250000000000000000000000 : ℝ)*base71 + (1871068115439/4229000000000000000000000000 : ℝ)*base74 + (12798363884847737/1651953125000000000000000000000 : ℝ)*base76 + (15903827668942349/3303906250000000000000000000000 : ℝ)*base78 + (52073166973861099/3303906250000000000000000000000 : ℝ)*base80 + (18289367399161/4229000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2451861/625000000000000000000 : ℝ)*base89 + (2451861/625000000000000000000 : ℝ)*base91 + (2451861/625000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1275608283138024179706174561/132156250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1708883709/100000000000000 : ℝ)*(base19) + (1861075113/100000000000000 : ℝ)*(base23) + (98193293/50000000000000 : ℝ)*(upper3) + (62589119/100000000000000 : ℝ)*(lower4) + (206710461/100000000000000 : ℝ)*(upper5) + (4259975231612151/100000000000000 : ℝ)*(major0) + (4259975231612151/100000000000000 : ℝ)*(major1) + (4259975231612151/100000000000000 : ℝ)*(major2) + (16778139001/50000000000000 : ℝ)*(sp1) + (3554302131/10000000000000 : ℝ)*(sp2) + (2877397282823411/50000000000000 : ℝ)*(sp4) + (719344912560639/12500000000000 : ℝ)*(sp5) + (5754757161550399/100000000000000 : ℝ)*(sp6) + (1382577787917511/50000000000000 : ℝ)*(sp7) + (1382577787917511/50000000000000 : ℝ)*(f.failure) + (2877397282823411/50000000000000 : ℝ)*(f.sum) + (4742892700769/10572500000000000000000000000 : ℝ)*base66 + (423369372588641813/264312500000000000000000000000000 : ℝ)*base68 + (1146484500727358187/264312500000000000000000000000000 : ℝ)*base69 + (2585676321410766813/264312500000000000000000000000000 : ℝ)*base72 + (7283344392867/5286250000000000000000000000 : ℝ)*base74 + (909010392944733187/264312500000000000000000000000000 : ℝ)*base75 + (808245420743141813/264312500000000000000000000000000 : ℝ)*base78 + (289907176199766813/264312500000000000000000000000000 : ℝ)*base80 + (7738945098189/2643125000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (2538167/312500000000000000000 : ℝ)*base89 + (2538167/312500000000000000000 : ℝ)*base91 + (2538167/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1325_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15027/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5399/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1325_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1325_s5_0 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-514673437/2500000000 : ℝ)*x 0 + (5414036769/10000000000 : ℝ)*x 1 + (5243654253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514673437/2500000000 : ℝ)^4285 ≤ (12532850847809/100000000000000 : ℝ)^3261 := by
    have hnat : (514673437 : ℕ)^4285*100000000000000^3261 ≤ 12532850847809^3261*2500000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514673437 2500000000 12532850847809 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414036769/10000000000 : ℝ)^4285 ≤ (22326112221021/50000000000000 : ℝ)^3261 := by
    have hnat : (5414036769 : ℕ)^4285*50000000000000^3261 ≤ 22326112221021^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414036769 10000000000 22326112221021 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243654253/10000000000 : ℝ)^4285 ≤ (21407462345991/50000000000000 : ℝ)^3261 := by
    have hnat : (5243654253 : ℕ)^4285*50000000000000^3261 ≤ 21407462345991^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243654253 10000000000 21407462345991 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-514673437/2500000000 : ℝ), (5414036769/10000000000 : ℝ), (5243654253/10000000000 : ℝ)] ![(12532850847809/100000000000000 : ℝ), (22326112221021/50000000000000 : ℝ), (21407462345991/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-514673437/2500000000 : ℝ)|^4285 ≤ (12532850847809/100000000000000 : ℝ)^3261
        have hw : |(-514673437/2500000000 : ℝ)|=(514673437/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414036769/10000000000 : ℝ)|^4285 ≤ (22326112221021/50000000000000 : ℝ)^3261
        have hw : |(5414036769/10000000000 : ℝ)|=(5414036769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243654253/10000000000 : ℝ)|^4285 ≤ (21407462345991/50000000000000 : ℝ)^3261
        have hw : |(5243654253/10000000000 : ℝ)|=(5243654253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s5_1 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349400177/10000000000 : ℝ)*x 0 + (-2145526671/10000000000 : ℝ)*x 1 + (131091361/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349400177/10000000000 : ℝ)^4285 ≤ (43953053604237/100000000000000 : ℝ)^3261 := by
    have hnat : (5349400177 : ℕ)^4285*100000000000000^3261 ≤ 43953053604237^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349400177 10000000000 43953053604237 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2145526671/10000000000 : ℝ)^4285 ≤ (6616009842297/50000000000000 : ℝ)^3261 := by
    have hnat : (2145526671 : ℕ)^4285*50000000000000^3261 ≤ 6616009842297^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145526671 10000000000 6616009842297 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131091361/250000000 : ℝ)^4285 ≤ (21407463349157/50000000000000 : ℝ)^3261 := by
    have hnat : (131091361 : ℕ)^4285*50000000000000^3261 ≤ 21407463349157^3261*250000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131091361 250000000 21407463349157 50000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349400177/10000000000 : ℝ), (-2145526671/10000000000 : ℝ), (131091361/250000000 : ℝ)] ![(43953053604237/100000000000000 : ℝ), (6616009842297/50000000000000 : ℝ), (21407463349157/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349400177/10000000000 : ℝ)|^4285 ≤ (43953053604237/100000000000000 : ℝ)^3261
        have hw : |(5349400177/10000000000 : ℝ)|=(5349400177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2145526671/10000000000 : ℝ)|^4285 ≤ (6616009842297/50000000000000 : ℝ)^3261
        have hw : |(-2145526671/10000000000 : ℝ)|=(2145526671/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131091361/250000000 : ℝ)|^4285 ≤ (21407463349157/50000000000000 : ℝ)^3261
        have hw : |(131091361/250000000 : ℝ)|=(131091361/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s5_2 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349399779/10000000000 : ℝ)*x 0 + (5243654621/10000000000 : ℝ)*x 1 + (-2145526961/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349399779/10000000000 : ℝ)^4285 ≤ (2197652465361/5000000000000 : ℝ)^3261 := by
    have hnat : (5349399779 : ℕ)^4285*5000000000000^3261 ≤ 2197652465361^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349399779 10000000000 2197652465361 5000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243654621/10000000000 : ℝ)^4285 ≤ (2675933040017/6250000000000 : ℝ)^3261 := by
    have hnat : (5243654621 : ℕ)^4285*6250000000000^3261 ≤ 2675933040017^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243654621 10000000000 2675933040017 6250000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2145526961/10000000000 : ℝ)^4285 ≤ (2646404406943/20000000000000 : ℝ)^3261 := by
    have hnat : (2145526961 : ℕ)^4285*20000000000000^3261 ≤ 2646404406943^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2145526961 10000000000 2646404406943 20000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349399779/10000000000 : ℝ), (5243654621/10000000000 : ℝ), (-2145526961/10000000000 : ℝ)] ![(2197652465361/5000000000000 : ℝ), (2675933040017/6250000000000 : ℝ), (2646404406943/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349399779/10000000000 : ℝ)|^4285 ≤ (2197652465361/5000000000000 : ℝ)^3261
        have hw : |(5349399779/10000000000 : ℝ)|=(5349399779/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243654621/10000000000 : ℝ)|^4285 ≤ (2675933040017/6250000000000 : ℝ)^3261
        have hw : |(5243654621/10000000000 : ℝ)|=(5243654621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2145526961/10000000000 : ℝ)|^4285 ≤ (2646404406943/20000000000000 : ℝ)^3261
        have hw : |(-2145526961/10000000000 : ℝ)|=(2145526961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s5_3 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4331052041/10000000000 : ℝ)*x 0 + (831434301/2000000000 : ℝ)*x 1 + (451176821/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331052041/10000000000 : ℝ)^4285 ≤ (33302635512639/100000000000000 : ℝ)^3261 := by
    have hnat : (4331052041 : ℕ)^4285*100000000000000^3261 ≤ 33302635512639^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331052041 10000000000 33302635512639 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (831434301/2000000000 : ℝ)^4285 ≤ (31556957013073/100000000000000 : ℝ)^3261 := by
    have hnat : (831434301 : ℕ)^4285*100000000000000^3261 ≤ 31556957013073^3261*2000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      831434301 2000000000 31556957013073 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (451176821/1000000000 : ℝ)^4285 ≤ (35140407460909/100000000000000 : ℝ)^3261 := by
    have hnat : (451176821 : ℕ)^4285*100000000000000^3261 ≤ 35140407460909^3261*1000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      451176821 1000000000 35140407460909 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331052041/10000000000 : ℝ), (831434301/2000000000 : ℝ), (451176821/1000000000 : ℝ)] ![(33302635512639/100000000000000 : ℝ), (31556957013073/100000000000000 : ℝ), (35140407460909/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331052041/10000000000 : ℝ)|^4285 ≤ (33302635512639/100000000000000 : ℝ)^3261
        have hw : |(4331052041/10000000000 : ℝ)|=(4331052041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(831434301/2000000000 : ℝ)|^4285 ≤ (31556957013073/100000000000000 : ℝ)^3261
        have hw : |(831434301/2000000000 : ℝ)|=(831434301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(451176821/1000000000 : ℝ)|^4285 ≤ (35140407460909/100000000000000 : ℝ)^3261
        have hw : |(451176821/1000000000 : ℝ)|=(451176821/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s5_4 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1029352919/5000000000 : ℝ)*x 0 + (5244266739/10000000000 : ℝ)*x 1 + (338338841/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1029352919/5000000000 : ℝ)^4285 ≤ (12532947560809/100000000000000 : ℝ)^3261 := by
    have hnat : (1029352919 : ℕ)^4285*100000000000000^3261 ≤ 12532947560809^3261*5000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1029352919 5000000000 12532947560809 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5244266739/10000000000 : ℝ)^4285 ≤ (5352687025477/12500000000000 : ℝ)^3261 := by
    have hnat : (5244266739 : ℕ)^4285*12500000000000^3261 ≤ 5352687025477^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5244266739 10000000000 5352687025477 12500000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338338841/625000000 : ℝ)^4285 ≤ (558069452709/1250000000000 : ℝ)^3261 := by
    have hnat : (338338841 : ℕ)^4285*1250000000000^3261 ≤ 558069452709^3261*625000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338338841 625000000 558069452709 1250000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1029352919/5000000000 : ℝ), (5244266739/10000000000 : ℝ), (338338841/625000000 : ℝ)] ![(12532947560809/100000000000000 : ℝ), (5352687025477/12500000000000 : ℝ), (558069452709/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1029352919/5000000000 : ℝ)|^4285 ≤ (12532947560809/100000000000000 : ℝ)^3261
        have hw : |(-1029352919/5000000000 : ℝ)|=(1029352919/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5244266739/10000000000 : ℝ)|^4285 ≤ (5352687025477/12500000000000 : ℝ)^3261
        have hw : |(5244266739/10000000000 : ℝ)|=(5244266739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338338841/625000000 : ℝ)|^4285 ≤ (558069452709/1250000000000 : ℝ)^3261
        have hw : |(338338841/625000000 : ℝ)|=(338338841/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s5_5 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212224033/400000000 : ℝ)*x 0 + (-1975759617/10000000000 : ℝ)*x 1 + (338338841/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212224033/400000000 : ℝ)^4285 ≤ (43480781851753/100000000000000 : ℝ)^3261 := by
    have hnat : (212224033 : ℕ)^4285*100000000000000^3261 ≤ 43480781851753^3261*400000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212224033 400000000 43480781851753 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1975759617/10000000000 : ℝ)^4285 ≤ (11873661916381/100000000000000 : ℝ)^3261 := by
    have hnat : (1975759617 : ℕ)^4285*100000000000000^3261 ≤ 11873661916381^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975759617 10000000000 11873661916381 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (338338841/625000000 : ℝ)^4285 ≤ (558069452709/1250000000000 : ℝ)^3261 := by
    have hnat : (338338841 : ℕ)^4285*1250000000000^3261 ≤ 558069452709^3261*625000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338338841 625000000 558069452709 1250000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212224033/400000000 : ℝ), (-1975759617/10000000000 : ℝ), (338338841/625000000 : ℝ)] ![(43480781851753/100000000000000 : ℝ), (11873661916381/100000000000000 : ℝ), (558069452709/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212224033/400000000 : ℝ)|^4285 ≤ (43480781851753/100000000000000 : ℝ)^3261
        have hw : |(212224033/400000000 : ℝ)|=(212224033/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1975759617/10000000000 : ℝ)|^4285 ≤ (11873661916381/100000000000000 : ℝ)^3261
        have hw : |(-1975759617/10000000000 : ℝ)|=(1975759617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(338338841/625000000 : ℝ)|^4285 ≤ (558069452709/1250000000000 : ℝ)^3261
        have hw : |(338338841/625000000 : ℝ)|=(338338841/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s5_6 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (212224033/400000000 : ℝ)*x 0 + (338338841/625000000 : ℝ)*x 1 + (-1975759617/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (212224033/400000000 : ℝ)^4285 ≤ (43480781851753/100000000000000 : ℝ)^3261 := by
    have hnat : (212224033 : ℕ)^4285*100000000000000^3261 ≤ 43480781851753^3261*400000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      212224033 400000000 43480781851753 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338338841/625000000 : ℝ)^4285 ≤ (558069452709/1250000000000 : ℝ)^3261 := by
    have hnat : (338338841 : ℕ)^4285*1250000000000^3261 ≤ 558069452709^3261*625000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338338841 625000000 558069452709 1250000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1975759617/10000000000 : ℝ)^4285 ≤ (11873661916381/100000000000000 : ℝ)^3261 := by
    have hnat : (1975759617 : ℕ)^4285*100000000000000^3261 ≤ 11873661916381^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1975759617 10000000000 11873661916381 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(212224033/400000000 : ℝ), (338338841/625000000 : ℝ), (-1975759617/10000000000 : ℝ)] ![(43480781851753/100000000000000 : ℝ), (558069452709/1250000000000 : ℝ), (11873661916381/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(212224033/400000000 : ℝ)|^4285 ≤ (43480781851753/100000000000000 : ℝ)^3261
        have hw : |(212224033/400000000 : ℝ)|=(212224033/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338338841/625000000 : ℝ)|^4285 ≤ (558069452709/1250000000000 : ℝ)^3261
        have hw : |(338338841/625000000 : ℝ)|=(338338841/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1975759617/10000000000 : ℝ)|^4285 ≤ (11873661916381/100000000000000 : ℝ)^3261
        have hw : |(-1975759617/10000000000 : ℝ)|=(1975759617/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1325_s5_7 (p : ℝ) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4331078361/10000000000 : ℝ)*x 0 + (4510494019/10000000000 : ℝ)*x 1 + (4158452091/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331078361/10000000000 : ℝ)^4285 ≤ (4162862680651/12500000000000 : ℝ)^3261 := by
    have hnat : (4331078361 : ℕ)^4285*12500000000000^3261 ≤ 4162862680651^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331078361 10000000000 4162862680651 12500000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4510494019/10000000000 : ℝ)^4285 ≤ (35127367529261/100000000000000 : ℝ)^3261 := by
    have hnat : (4510494019 : ℕ)^4285*100000000000000^3261 ≤ 35127367529261^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4510494019 10000000000 35127367529261 100000000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4158452091/10000000000 : ℝ)^4285 ≤ (50511569623/160000000000 : ℝ)^3261 := by
    have hnat : (4158452091 : ℕ)^4285*160000000000^3261 ≤ 50511569623^3261*10000000000^4285 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158452091 10000000000 50511569623 160000000000 4285 3261 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4285/1024 : ℝ)) 4285 3261 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331078361/10000000000 : ℝ), (4510494019/10000000000 : ℝ), (4158452091/10000000000 : ℝ)] ![(4162862680651/12500000000000 : ℝ), (35127367529261/100000000000000 : ℝ), (50511569623/160000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331078361/10000000000 : ℝ)|^4285 ≤ (4162862680651/12500000000000 : ℝ)^3261
        have hw : |(4331078361/10000000000 : ℝ)|=(4331078361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4510494019/10000000000 : ℝ)|^4285 ≤ (35127367529261/100000000000000 : ℝ)^3261
        have hw : |(4510494019/10000000000 : ℝ)|=(4510494019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4158452091/10000000000 : ℝ)|^4285 ≤ (50511569623/160000000000 : ℝ)^3261
        have hw : |(4158452091/10000000000 : ℝ)|=(4158452091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1325_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11099/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7353/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11051/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14757/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11051/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14757/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11051/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11051/100000 : ℝ) ^ (1071/256 : ℝ) ≤ (1990722934887403/20000000000000000000 : ℝ) := by
    have hpowers : (11051/100000 : ℝ)^1071 ≤ (1990722934887403/20000000000000000000 : ℝ)^256 := by
      have hnat : (11051 : ℕ)^1071*20000000000000000000^256 ≤ 1990722934887403^256*100000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11051 100000 1990722934887403 20000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11051/100000 : ℝ)) (X := (1990722934887403/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hpowhi : (14757/100000 : ℝ) ^ (1071/256 : ℝ) ≤ (6675065713617543/20000000000000000000 : ℝ) := by
    have hpowers : (14757/100000 : ℝ)^1071 ≤ (6675065713617543/20000000000000000000 : ℝ)^256 := by
      have hnat : (14757 : ℕ)^1071*20000000000000000000^256 ≤ 6675065713617543^256*100000^1071 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14757 100000 6675065713617543 20000000000000000000 1071 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14757/100000 : ℝ)) (X := (6675065713617543/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10001990722934887403/10000000000000000000 : ℝ) ≤ (10000475804364833/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (10001990722934887403/10000000000000000000 : ℝ)^256 ≤ (10000475804364833/10000000000000000 : ℝ)^1071 := by
      have hnat : (10001990722934887403 : ℕ)^256*10000000000000000^1071 ≤ 10000475804364833^1071*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10001990722934887403 10000000000000000000 10000475804364833 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000475804364833/10000000000000000 : ℝ)) (X := (10001990722934887403/10000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004332894324252473/10000000000000000000 : ℝ) ≤ (2500258879114599/2500000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (10004332894324252473/10000000000000000000 : ℝ)^256 ≤ (2500258879114599/2500000000000000 : ℝ)^1071 := by
      have hnat : (10004332894324252473 : ℕ)^256*2500000000000000^1071 ≤ 2500258879114599^1071*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004332894324252473 10000000000000000000 2500258879114599 2500000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500258879114599/2500000000000000 : ℝ)) (X := (10004332894324252473/10000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (10006675065713617543/10000000000000000000 : ℝ) ≤ (10001595228551959/10000000000000000 : ℝ) ^ (1071/256 : ℝ) := by
    have hpowers : (10006675065713617543/10000000000000000000 : ℝ)^256 ≤ (10001595228551959/10000000000000000 : ℝ)^1071 := by
      have hnat : (10006675065713617543 : ℕ)^256*10000000000000000^1071 ≤ 10001595228551959^1071*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10006675065713617543 10000000000000000000 10001595228551959 10000000000000000 256 1071 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001595228551959/10000000000000000 : ℝ)) (X := (10006675065713617543/10000000000000000000 : ℝ)) (by norm_num) 1071 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1990722934887403/20000000000000000000 : ℝ) ≤ ((4631174071785517709/4632500000000000000 : ℝ)+2*(559712093563/370600000000000 : ℝ)*(11051/100000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (4631174071785517709/4632500000000000000 : ℝ)+2*(559712093563/370600000000000 : ℝ)*(11051/100000 : ℝ)=(10000475804364833/10000000000000000 : ℝ) by norm_num, show 1+2*(1990722934887403/20000000000000000000 : ℝ)=(10001990722934887403/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(6675065713617543/20000000000000000000 : ℝ)+(1990722934887403/20000000000000000000 : ℝ) ≤ ((4631174071785517709/4632500000000000000 : ℝ)+(559712093563/370600000000000 : ℝ)*((14757/100000 : ℝ)+(11051/100000 : ℝ)))^(1071/256 : ℝ) := by
    rw [show (4631174071785517709/4632500000000000000 : ℝ)+(559712093563/370600000000000 : ℝ)*((14757/100000 : ℝ)+(11051/100000 : ℝ))=(2500258879114599/2500000000000000 : ℝ) by norm_num, show 1+(6675065713617543/20000000000000000000 : ℝ)+(1990722934887403/20000000000000000000 : ℝ)=(10004332894324252473/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(6675065713617543/20000000000000000000 : ℝ) ≤ ((4631174071785517709/4632500000000000000 : ℝ)+2*(559712093563/370600000000000 : ℝ)*(14757/100000 : ℝ))^(1071/256 : ℝ) := by
    rw [show (4631174071785517709/4632500000000000000 : ℝ)+2*(559712093563/370600000000000 : ℝ)*(14757/100000 : ℝ)=(10001595228551959/10000000000000000 : ℝ) by norm_num, show 1+2*(6675065713617543/20000000000000000000 : ℝ)=(10006675065713617543/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4631174071785517709/4632500000000000000 : ℝ)*(X 1 0+X 2 0)+(559712093563/370600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (11051/100000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (4631174071785517709/4632500000000000000 : ℝ)) (alpha := (559712093563/370600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4631174071785517709/4632500000000000000 : ℝ)*(X 0 1+X 2 1)+(559712093563/370600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (11051/100000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (4631174071785517709/4632500000000000000 : ℝ)) (alpha := (559712093563/370600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4631174071785517709/4632500000000000000 : ℝ)*(X 0 2+X 1 2)+(559712093563/370600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1071/256 : ℝ)) (lo := (11051/100000 : ℝ)) (hi := (14757/100000 : ℝ)) (c := (4631174071785517709/4632500000000000000 : ℝ)) (alpha := (559712093563/370600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-514673437/2500000000 : ℝ)*X 0 0+(5414036769/10000000000 : ℝ)*X 0 1+(5243654253/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349400177/10000000000 : ℝ)*X 1 0+(-2145526671/10000000000 : ℝ)*X 1 1+(131091361/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5349399779/10000000000 : ℝ)*X 2 0+(5243654621/10000000000 : ℝ)*X 2 1+(-2145526961/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4331052041/10000000000 : ℝ)*X 0 0+(831434301/2000000000 : ℝ)*X 0 1+(451176821/1000000000 : ℝ)*X 0 2+(4331052041/10000000000 : ℝ)*X 1 0+(831434301/2000000000 : ℝ)*X 1 1+(451176821/1000000000 : ℝ)*X 1 2+(4331052041/10000000000 : ℝ)*X 2 0+(831434301/2000000000 : ℝ)*X 2 1+(451176821/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1029352919/5000000000 : ℝ)*X 0 0+(5244266739/10000000000 : ℝ)*X 0 1+(338338841/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((212224033/400000000 : ℝ)*X 1 0+(-1975759617/10000000000 : ℝ)*X 1 1+(338338841/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((212224033/400000000 : ℝ)*X 2 0+(338338841/625000000 : ℝ)*X 2 1+(-1975759617/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4331078361/10000000000 : ℝ)*X 0 0+(4510494019/10000000000 : ℝ)*X 0 1+(4158452091/10000000000 : ℝ)*X 0 2+(4331078361/10000000000 : ℝ)*X 1 0+(4510494019/10000000000 : ℝ)*X 1 1+(4158452091/10000000000 : ℝ)*X 1 2+(4331078361/10000000000 : ℝ)*X 2 0+(4510494019/10000000000 : ℝ)*X 2 1+(4158452091/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1325_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (21730027765745863935333/2316250000000000000000000000 : ℝ) := by norm_num
    linear_combination (20197967/1000000000000 : ℝ)*(base19) + (83472483/6250000000000 : ℝ)*(base23) + (64652597/100000000000000 : ℝ)*(upper2) + (606129943/100000000000000 : ℝ)*(upper3) + (24635409/12500000000000 : ℝ)*(upper4) + (2172340697959117/50000000000000 : ℝ)*(major0) + (2172340697959117/50000000000000 : ℝ)*(major1) + (2172340697959117/50000000000000 : ℝ)*(major2) + (5869196669841523/100000000000000 : ℝ)*(sp0) + (58692219998299/1000000000000 : ℝ)*(sp1) + (733652835508359/12500000000000 : ℝ)*(sp2) + (88128676926677/3125000000000 : ℝ)*(sp3) + (27349785077/100000000000000 : ℝ)*(sp4) + (5199459421/25000000000000 : ℝ)*(sp7) + (705034614872837/25000000000000 : ℝ)*(f.failure) + (5869224019626599/100000000000000 : ℝ)*(f.sum) + (5706591598899/9265000000000000000000000000 : ℝ)*base66 + (1013807176804859547/231625000000000000000000000000000 : ℝ)*base68 + (818923618473015453/231625000000000000000000000000000 : ℝ)*base69 + (1079177854591890453/231625000000000000000000000000000 : ℝ)*base71 + (3445495864631/9265000000000000000000000000 : ℝ)*base73 + (2109834736821609547/231625000000000000000000000000000 : ℝ)*base76 + (878097477746390453/231625000000000000000000000000000 : ℝ)*base77 + (875110687800609547/231625000000000000000000000000000 : ℝ)*base80 + (35785077722491/9265000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (378389/156250000000000000000 : ℝ)*base89 + (378389/156250000000000000000 : ℝ)*base91 + (378389/156250000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1833099097772981719878363/212890625000000000000000000000 : ℝ) := by norm_num
    linear_combination (1508349081/100000000000000 : ℝ)*(base19) + (1639868137/100000000000000 : ℝ)*(base23) + (175093197/100000000000000 : ℝ)*(upper3) + (29834049/50000000000000 : ℝ)*(lower4) + (176647189/100000000000000 : ℝ)*(upper5) + (547019818526283/12500000000000 : ℝ)*(major0) + (547019818526283/12500000000000 : ℝ)*(major1) + (547019818526283/12500000000000 : ℝ)*(major2) + (30437181987/100000000000000 : ℝ)*(sp1) + (16372942067/50000000000000 : ℝ)*(sp2) + (738968311073603/12500000000000 : ℝ)*(sp4) + (1477928635764439/25000000000000 : ℝ)*(sp5) + (738964012854569/12500000000000 : ℝ)*(sp6) + (710142580203587/25000000000000 : ℝ)*(sp7) + (710142580203587/25000000000000 : ℝ)*(f.failure) + (738968311073603/12500000000000 : ℝ)*(f.sum) + (302846274959/68125000000000000000000000 : ℝ)*base66 + (2325571140804891/3406250000000000000000000000000 : ℝ)*base67 + (23585680979054891/3406250000000000000000000000000 : ℝ)*base69 + (23614979428288859/3406250000000000000000000000000 : ℝ)*base72 + (574783882313/545000000000000000000000000 : ℝ)*base73 + (22240970896304891/3406250000000000000000000000000 : ℝ)*base75 + (17889150222242391/3406250000000000000000000000000 : ℝ)*base77 + (21784734862367391/3406250000000000000000000000000 : ℝ)*base79 + (181437340201/272500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (36139/156250000000000000000 : ℝ)*base89 + (36139/156250000000000000000 : ℝ)*base91 + (36139/156250000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1325_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14757/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11051/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11099/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1325_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1325_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16173/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4869/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11099/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1325_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1325_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1325_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1071/256 : ℝ) ≤ p) (hpb : p ≤ (4285/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (9628697/6250000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16173/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4869/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11099/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7353/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1325_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
