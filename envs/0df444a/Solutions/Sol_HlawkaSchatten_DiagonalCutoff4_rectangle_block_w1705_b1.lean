-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1705_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:49:55.916119+00:00
-- url     : https://prove2.me/submissions/41f6c842-adb7-48ef-8c8b-51cfda914fb6

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
theorem support_rectangle_w1705_s3_0 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1430345419/10000000000 : ℝ)*x 0 + (1094649633/2000000000 : ℝ)*x 1 + (5137645163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1430345419/10000000000 : ℝ)^5263 ≤ (4470888441419/50000000000000 : ℝ)^4239 := by
    have hnat : (1430345419 : ℕ)^5263*50000000000000^4239 ≤ 4470888441419^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1430345419 10000000000 4470888441419 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094649633/2000000000 : ℝ)^5263 ≤ (47316646720979/100000000000000 : ℝ)^4239 := by
    have hnat : (1094649633 : ℕ)^5263*100000000000000^4239 ≤ 47316646720979^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094649633 2000000000 47316646720979 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5137645163/10000000000 : ℝ)^5263 ≤ (273384852313/625000000000 : ℝ)^4239 := by
    have hnat : (5137645163 : ℕ)^5263*625000000000^4239 ≤ 273384852313^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5137645163 10000000000 273384852313 625000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1430345419/10000000000 : ℝ), (1094649633/2000000000 : ℝ), (5137645163/10000000000 : ℝ)] ![(4470888441419/50000000000000 : ℝ), (47316646720979/100000000000000 : ℝ), (273384852313/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1430345419/10000000000 : ℝ)|^5263 ≤ (4470888441419/50000000000000 : ℝ)^4239
        have hw : |(-1430345419/10000000000 : ℝ)|=(1430345419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094649633/2000000000 : ℝ)|^5263 ≤ (47316646720979/100000000000000 : ℝ)^4239
        have hw : |(1094649633/2000000000 : ℝ)|=(1094649633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5137645163/10000000000 : ℝ)|^5263 ≤ (273384852313/625000000000 : ℝ)^4239
        have hw : |(5137645163/10000000000 : ℝ)|=(5137645163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s3_1 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345196679/10000000000 : ℝ)*x 0 + (-100277367/625000000 : ℝ)*x 1 + (2568822601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345196679/10000000000 : ℝ)^5263 ≤ (45946121411207/100000000000000 : ℝ)^4239 := by
    have hnat : (5345196679 : ℕ)^5263*100000000000000^4239 ≤ 45946121411207^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345196679 10000000000 45946121411207 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (100277367/625000000 : ℝ)^5263 ≤ (2062460357077/20000000000000 : ℝ)^4239 := by
    have hnat : (100277367 : ℕ)^5263*20000000000000^4239 ≤ 2062460357077^4239*625000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      100277367 625000000 2062460357077 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568822601/5000000000 : ℝ)^5263 ≤ (21870788391167/50000000000000 : ℝ)^4239 := by
    have hnat : (2568822601 : ℕ)^5263*50000000000000^4239 ≤ 21870788391167^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568822601 5000000000 21870788391167 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345196679/10000000000 : ℝ), (-100277367/625000000 : ℝ), (2568822601/5000000000 : ℝ)] ![(45946121411207/100000000000000 : ℝ), (2062460357077/20000000000000 : ℝ), (21870788391167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345196679/10000000000 : ℝ)|^5263 ≤ (45946121411207/100000000000000 : ℝ)^4239
        have hw : |(5345196679/10000000000 : ℝ)|=(5345196679/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-100277367/625000000 : ℝ)|^5263 ≤ (2062460357077/20000000000000 : ℝ)^4239
        have hw : |(-100277367/625000000 : ℝ)|=(100277367/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568822601/5000000000 : ℝ)|^5263 ≤ (21870788391167/50000000000000 : ℝ)^4239
        have hw : |(2568822601/5000000000 : ℝ)|=(2568822601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s3_2 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336299187/2500000000 : ℝ)*x 0 + (513764523/1000000000 : ℝ)*x 1 + (-1604437743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336299187/2500000000 : ℝ)^5263 ≤ (45946122147591/100000000000000 : ℝ)^4239 := by
    have hnat : (1336299187 : ℕ)^5263*100000000000000^4239 ≤ 45946122147591^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336299187 2500000000 45946122147591 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513764523/1000000000 : ℝ)^5263 ≤ (43741577078311/100000000000000 : ℝ)^4239 := by
    have hnat : (513764523 : ℕ)^5263*100000000000000^4239 ≤ 43741577078311^4239*1000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513764523 1000000000 43741577078311 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1604437743/10000000000 : ℝ)^5263 ≤ (5156150377983/50000000000000 : ℝ)^4239 := by
    have hnat : (1604437743 : ℕ)^5263*50000000000000^4239 ≤ 5156150377983^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604437743 10000000000 5156150377983 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336299187/2500000000 : ℝ), (513764523/1000000000 : ℝ), (-1604437743/10000000000 : ℝ)] ![(45946122147591/100000000000000 : ℝ), (43741577078311/100000000000000 : ℝ), (5156150377983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336299187/2500000000 : ℝ)|^5263 ≤ (45946122147591/100000000000000 : ℝ)^4239
        have hw : |(1336299187/2500000000 : ℝ)|=(1336299187/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513764523/1000000000 : ℝ)|^5263 ≤ (43741577078311/100000000000000 : ℝ)^4239
        have hw : |(513764523/1000000000 : ℝ)|=(513764523/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1604437743/10000000000 : ℝ)|^5263 ≤ (5156150377983/50000000000000 : ℝ)^4239
        have hw : |(-1604437743/10000000000 : ℝ)|=(1604437743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s3_3 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4111178587/10000000000 : ℝ)*x 0 + (3648259803/10000000000 : ℝ)*x 1 + (4610159887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4111178587/10000000000 : ℝ)^5263 ≤ (1658378212199/5000000000000 : ℝ)^4239 := by
    have hnat : (4111178587 : ℕ)^5263*5000000000000^4239 ≤ 1658378212199^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4111178587 10000000000 1658378212199 5000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3648259803/10000000000 : ℝ)^5263 ≤ (2859567733969/10000000000000 : ℝ)^4239 := by
    have hnat : (3648259803 : ℕ)^5263*10000000000000^4239 ≤ 2859567733969^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3648259803 10000000000 2859567733969 10000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4610159887/10000000000 : ℝ)^5263 ≤ (19118379199709/50000000000000 : ℝ)^4239 := by
    have hnat : (4610159887 : ℕ)^5263*50000000000000^4239 ≤ 19118379199709^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4610159887 10000000000 19118379199709 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4111178587/10000000000 : ℝ), (3648259803/10000000000 : ℝ), (4610159887/10000000000 : ℝ)] ![(1658378212199/5000000000000 : ℝ), (2859567733969/10000000000000 : ℝ), (19118379199709/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4111178587/10000000000 : ℝ)|^5263 ≤ (1658378212199/5000000000000 : ℝ)^4239
        have hw : |(4111178587/10000000000 : ℝ)|=(4111178587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3648259803/10000000000 : ℝ)|^5263 ≤ (2859567733969/10000000000000 : ℝ)^4239
        have hw : |(3648259803/10000000000 : ℝ)|=(3648259803/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4610159887/10000000000 : ℝ)|^5263 ≤ (19118379199709/50000000000000 : ℝ)^4239
        have hw : |(4610159887/10000000000 : ℝ)|=(4610159887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s3_4 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-715249163/5000000000 : ℝ)*x 0 + (1028269063/2000000000 : ℝ)*x 1 + (5469492943/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (715249163/5000000000 : ℝ)^5263 ≤ (4471481852747/50000000000000 : ℝ)^4239 := by
    have hnat : (715249163 : ℕ)^5263*50000000000000^4239 ≤ 4471481852747^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      715249163 5000000000 4471481852747 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1028269063/2000000000 : ℝ)^5263 ≤ (21890346328039/50000000000000 : ℝ)^4239 := by
    have hnat : (1028269063 : ℕ)^5263*50000000000000^4239 ≤ 21890346328039^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1028269063 2000000000 21890346328039 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469492943/10000000000 : ℝ)^5263 ≤ (23638171813313/50000000000000 : ℝ)^4239 := by
    have hnat : (5469492943 : ℕ)^5263*50000000000000^4239 ≤ 23638171813313^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469492943 10000000000 23638171813313 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-715249163/5000000000 : ℝ), (1028269063/2000000000 : ℝ), (5469492943/10000000000 : ℝ)] ![(4471481852747/50000000000000 : ℝ), (21890346328039/50000000000000 : ℝ), (23638171813313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-715249163/5000000000 : ℝ)|^5263 ≤ (4471481852747/50000000000000 : ℝ)^4239
        have hw : |(-715249163/5000000000 : ℝ)|=(715249163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1028269063/2000000000 : ℝ)|^5263 ≤ (21890346328039/50000000000000 : ℝ)^4239
        have hw : |(1028269063/2000000000 : ℝ)|=(1028269063/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469492943/10000000000 : ℝ)|^5263 ≤ (23638171813313/50000000000000 : ℝ)^4239
        have hw : |(5469492943/10000000000 : ℝ)|=(5469492943/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s3_5 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164230601/312500000 : ℝ)*x 0 + (-254518171/2000000000 : ℝ)*x 1 + (683686613/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164230601/312500000 : ℝ)^5263 ≤ (22494761428647/50000000000000 : ℝ)^4239 := by
    have hnat : (164230601 : ℕ)^5263*50000000000000^4239 ≤ 22494761428647^4239*312500000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164230601 312500000 22494761428647 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (254518171/2000000000 : ℝ)^5263 ≤ (3867066958631/50000000000000 : ℝ)^4239 := by
    have hnat : (254518171 : ℕ)^5263*50000000000000^4239 ≤ 3867066958631^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      254518171 2000000000 3867066958631 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (683686613/1250000000 : ℝ)^5263 ≤ (47276343208091/100000000000000 : ℝ)^4239 := by
    have hnat : (683686613 : ℕ)^5263*100000000000000^4239 ≤ 47276343208091^4239*1250000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      683686613 1250000000 47276343208091 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164230601/312500000 : ℝ), (-254518171/2000000000 : ℝ), (683686613/1250000000 : ℝ)] ![(22494761428647/50000000000000 : ℝ), (3867066958631/50000000000000 : ℝ), (47276343208091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164230601/312500000 : ℝ)|^5263 ≤ (22494761428647/50000000000000 : ℝ)^4239
        have hw : |(164230601/312500000 : ℝ)|=(164230601/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-254518171/2000000000 : ℝ)|^5263 ≤ (3867066958631/50000000000000 : ℝ)^4239
        have hw : |(-254518171/2000000000 : ℝ)|=(254518171/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(683686613/1250000000 : ℝ)|^5263 ≤ (47276343208091/100000000000000 : ℝ)^4239
        have hw : |(683686613/1250000000 : ℝ)|=(683686613/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s3_6 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328461249/625000000 : ℝ)*x 0 + (2734746173/5000000000 : ℝ)*x 1 + (-127259059/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328461249/625000000 : ℝ)^5263 ≤ (5623691356253/12500000000000 : ℝ)^4239 := by
    have hnat : (328461249 : ℕ)^5263*12500000000000^4239 ≤ 5623691356253^4239*625000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328461249 625000000 5623691356253 12500000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2734746173/5000000000 : ℝ)^5263 ≤ (47276337219827/100000000000000 : ℝ)^4239 := by
    have hnat : (2734746173 : ℕ)^5263*100000000000000^4239 ≤ 47276337219827^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2734746173 5000000000 47276337219827 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127259059/1000000000 : ℝ)^5263 ≤ (7734131917683/100000000000000 : ℝ)^4239 := by
    have hnat : (127259059 : ℕ)^5263*100000000000000^4239 ≤ 7734131917683^4239*1000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127259059 1000000000 7734131917683 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328461249/625000000 : ℝ), (2734746173/5000000000 : ℝ), (-127259059/1000000000 : ℝ)] ![(5623691356253/12500000000000 : ℝ), (47276337219827/100000000000000 : ℝ), (7734131917683/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328461249/625000000 : ℝ)|^5263 ≤ (5623691356253/12500000000000 : ℝ)^4239
        have hw : |(328461249/625000000 : ℝ)|=(328461249/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2734746173/5000000000 : ℝ)|^5263 ≤ (47276337219827/100000000000000 : ℝ)^4239
        have hw : |(2734746173/5000000000 : ℝ)|=(2734746173/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127259059/1000000000 : ℝ)|^5263 ≤ (7734131917683/100000000000000 : ℝ)^4239
        have hw : |(-127259059/1000000000 : ℝ)|=(127259059/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s3_7 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164464707/400000000 : ℝ)*x 0 + (1149888451/2500000000 : ℝ)*x 1 + (3659023811/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164464707/400000000 : ℝ)^5263 ≤ (33171962437763/100000000000000 : ℝ)^4239 := by
    have hnat : (164464707 : ℕ)^5263*100000000000000^4239 ≤ 33171962437763^4239*400000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164464707 400000000 33171962437763 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1149888451/2500000000 : ℝ)^5263 ≤ (38127571812959/100000000000000 : ℝ)^4239 := by
    have hnat : (1149888451 : ℕ)^5263*100000000000000^4239 ≤ 38127571812959^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1149888451 2500000000 38127571812959 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3659023811/10000000000 : ℝ)^5263 ≤ (28700465742217/100000000000000 : ℝ)^4239 := by
    have hnat : (3659023811 : ℕ)^5263*100000000000000^4239 ≤ 28700465742217^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3659023811 10000000000 28700465742217 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164464707/400000000 : ℝ), (1149888451/2500000000 : ℝ), (3659023811/10000000000 : ℝ)] ![(33171962437763/100000000000000 : ℝ), (38127571812959/100000000000000 : ℝ), (28700465742217/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164464707/400000000 : ℝ)|^5263 ≤ (33171962437763/100000000000000 : ℝ)^4239
        have hw : |(164464707/400000000 : ℝ)|=(164464707/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1149888451/2500000000 : ℝ)|^5263 ≤ (38127571812959/100000000000000 : ℝ)^4239
        have hw : |(1149888451/2500000000 : ℝ)|=(1149888451/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3659023811/10000000000 : ℝ)|^5263 ≤ (28700465742217/100000000000000 : ℝ)^4239
        have hw : |(3659023811/10000000000 : ℝ)|=(3659023811/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1705_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4979/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (9969/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (17129/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8571/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4979/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8571/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4979/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8571/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4979/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8571/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4979/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8571/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4979/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8571/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4979/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4979/50000 : ℝ) ^ (5255/1024 : ℝ) ≤ (722409905330721/100000000000000000000 : ℝ) := by
    have hpowers : (4979/50000 : ℝ)^5255 ≤ (722409905330721/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4979 : ℕ)^5255*100000000000000000000^1024 ≤ 722409905330721^1024*50000^5255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4979 50000 722409905330721 100000000000000000000 5255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4979/50000 : ℝ)) (X := (722409905330721/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8571/50000 : ℝ) ^ (5255/1024 : ℝ) ≤ (5865421634527683/50000000000000000000 : ℝ) := by
    have hpowers : (8571/50000 : ℝ)^5255 ≤ (5865421634527683/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8571 : ℕ)^5255*50000000000000000000^1024 ≤ 5865421634527683^1024*50000^5255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8571 50000 5865421634527683 50000000000000000000 5255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8571/50000 : ℝ)) (X := (5865421634527683/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000722409905330721/50000000000000000000 : ℝ) ≤ (2000005630777853/2000000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (50000722409905330721/50000000000000000000 : ℝ)^1024 ≤ (2000005630777853/2000000000000000 : ℝ)^5255 := by
      have hnat : (50000722409905330721 : ℕ)^1024*2000000000000000^5255 ≤ 2000005630777853^5255*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000722409905330721 50000000000000000000 2000005630777853 2000000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000005630777853/2000000000000000 : ℝ)) (X := (50000722409905330721/50000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100012453253174386087/100000000000000000000 : ℝ) ≤ (2000048530892471/2000000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (100012453253174386087/100000000000000000000 : ℝ)^1024 ≤ (2000048530892471/2000000000000000 : ℝ)^5255 := by
      have hnat : (100012453253174386087 : ℕ)^1024*2000000000000000^5255 ≤ 2000048530892471^5255*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100012453253174386087 100000000000000000000 2000048530892471 2000000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000048530892471/2000000000000000 : ℝ)) (X := (100012453253174386087/100000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25005865421634527683/25000000000000000000 : ℝ) ≤ (2000091431007089/2000000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (25005865421634527683/25000000000000000000 : ℝ)^1024 ≤ (2000091431007089/2000000000000000 : ℝ)^5255 := by
      have hnat : (25005865421634527683 : ℕ)^1024*2000000000000000^5255 ≤ 2000091431007089^5255*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25005865421634527683 25000000000000000000 2000091431007089 2000000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000091431007089/2000000000000000 : ℝ)) (X := (25005865421634527683/25000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(722409905330721/100000000000000000000 : ℝ) ≤ ((1795898256603170483/1796000000000000000 : ℝ)+2*(21450057309/71840000000000 : ℝ)*(4979/50000 : ℝ))^(5255/1024 : ℝ) := by
    rw [show (1795898256603170483/1796000000000000000 : ℝ)+2*(21450057309/71840000000000 : ℝ)*(4979/50000 : ℝ)=(2000005630777853/2000000000000000 : ℝ) by norm_num, show 1+2*(722409905330721/100000000000000000000 : ℝ)=(50000722409905330721/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5865421634527683/50000000000000000000 : ℝ)+(722409905330721/100000000000000000000 : ℝ) ≤ ((1795898256603170483/1796000000000000000 : ℝ)+(21450057309/71840000000000 : ℝ)*((8571/50000 : ℝ)+(4979/50000 : ℝ)))^(5255/1024 : ℝ) := by
    rw [show (1795898256603170483/1796000000000000000 : ℝ)+(21450057309/71840000000000 : ℝ)*((8571/50000 : ℝ)+(4979/50000 : ℝ))=(2000048530892471/2000000000000000 : ℝ) by norm_num, show 1+(5865421634527683/50000000000000000000 : ℝ)+(722409905330721/100000000000000000000 : ℝ)=(100012453253174386087/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5865421634527683/50000000000000000000 : ℝ) ≤ ((1795898256603170483/1796000000000000000 : ℝ)+2*(21450057309/71840000000000 : ℝ)*(8571/50000 : ℝ))^(5255/1024 : ℝ) := by
    rw [show (1795898256603170483/1796000000000000000 : ℝ)+2*(21450057309/71840000000000 : ℝ)*(8571/50000 : ℝ)=(2000091431007089/2000000000000000 : ℝ) by norm_num, show 1+2*(5865421634527683/50000000000000000000 : ℝ)=(25005865421634527683/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1795898256603170483/1796000000000000000 : ℝ)*(X 1 0+X 2 0)+(21450057309/71840000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (4979/50000 : ℝ)) (hi := (8571/50000 : ℝ)) (c := (1795898256603170483/1796000000000000000 : ℝ)) (alpha := (21450057309/71840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1795898256603170483/1796000000000000000 : ℝ)*(X 0 1+X 2 1)+(21450057309/71840000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (4979/50000 : ℝ)) (hi := (8571/50000 : ℝ)) (c := (1795898256603170483/1796000000000000000 : ℝ)) (alpha := (21450057309/71840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1795898256603170483/1796000000000000000 : ℝ)*(X 0 2+X 1 2)+(21450057309/71840000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (4979/50000 : ℝ)) (hi := (8571/50000 : ℝ)) (c := (1795898256603170483/1796000000000000000 : ℝ)) (alpha := (21450057309/71840000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1430345419/10000000000 : ℝ)*X 0 0+(1094649633/2000000000 : ℝ)*X 0 1+(5137645163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345196679/10000000000 : ℝ)*X 1 0+(-100277367/625000000 : ℝ)*X 1 1+(2568822601/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336299187/2500000000 : ℝ)*X 2 0+(513764523/1000000000 : ℝ)*X 2 1+(-1604437743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4111178587/10000000000 : ℝ)*X 0 0+(3648259803/10000000000 : ℝ)*X 0 1+(4610159887/10000000000 : ℝ)*X 0 2+(4111178587/10000000000 : ℝ)*X 1 0+(3648259803/10000000000 : ℝ)*X 1 1+(4610159887/10000000000 : ℝ)*X 1 2+(4111178587/10000000000 : ℝ)*X 2 0+(3648259803/10000000000 : ℝ)*X 2 1+(4610159887/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-715249163/5000000000 : ℝ)*X 0 0+(1028269063/2000000000 : ℝ)*X 0 1+(5469492943/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((164230601/312500000 : ℝ)*X 1 0+(-254518171/2000000000 : ℝ)*X 1 1+(683686613/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((328461249/625000000 : ℝ)*X 2 0+(2734746173/5000000000 : ℝ)*X 2 1+(-127259059/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((164464707/400000000 : ℝ)*X 0 0+(1149888451/2500000000 : ℝ)*X 0 1+(3659023811/10000000000 : ℝ)*X 0 2+(164464707/400000000 : ℝ)*X 1 0+(1149888451/2500000000 : ℝ)*X 1 1+(3659023811/10000000000 : ℝ)*X 1 2+(164464707/400000000 : ℝ)*X 2 0+(1149888451/2500000000 : ℝ)*X 2 1+(3659023811/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (198372030536884529605195839/22450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1379180969/100000000000000 : ℝ)*(base19) + (1390218783/100000000000000 : ℝ)*(base23) + (14660267/100000000000000 : ℝ)*(lower2) + (85697037/50000000000000 : ℝ)*(upper3) + (238230941/100000000000000 : ℝ)*(upper5) + (1004839776662611/50000000000000 : ℝ)*(major0) + (1004839776662611/50000000000000 : ℝ)*(major1) + (1004839776662611/50000000000000 : ℝ)*(major2) + (2979724597670323/100000000000000 : ℝ)*(sp0) + (1489869306051223/50000000000000 : ℝ)*(sp1) + (372467325133079/12500000000000 : ℝ)*(sp2) + (519807001702733/50000000000000 : ℝ)*(sp3) + (3848403273/25000000000000 : ℝ)*(sp4) + (2408711269/50000000000000 : ℝ)*(sp7) + (259904705207001/25000000000000 : ℝ)*(f.failure) + (595947998256683/20000000000000 : ℝ)*(f.sum) + (6156492354149/1796000000000000000000000000 : ℝ)*base66 + (320440529895113887/89800000000000000000000000000000 : ℝ)*base68 + (920548160887113887/89800000000000000000000000000000 : ℝ)*base70 + (2387204284913887/89800000000000000000000000000000 : ℝ)*base72 + (115020403249/1796000000000000000000000000 : ℝ)*base74 + (96934591379713887/89800000000000000000000000000000 : ℝ)*base76 + (607391347484513887/89800000000000000000000000000000 : ℝ)*base78 + (630996389271886113/89800000000000000000000000000000 : ℝ)*base79 + (1614729284213/359200000000000000000000000 : ℝ)*base82 + (1219927/250000000000000000000 : ℝ)*base89 + (1219927/250000000000000000000 : ℝ)*base91 + (1219927/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7312513029516795084390189/561250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (640127827/50000000000000 : ℝ)*(base19) + (124468637/6250000000000 : ℝ)*(base23) + (372794747/100000000000000 : ℝ)*(lower1) + (97670561/50000000000000 : ℝ)*(upper3) + (61056633/50000000000000 : ℝ)*(lower4) + (370310879/100000000000000 : ℝ)*(upper5) + (12845708196739/625000000000 : ℝ)*(major0) + (12845708196739/625000000000 : ℝ)*(major1) + (12845708196739/625000000000 : ℝ)*(major2) + (626477263/25000000000000 : ℝ)*(sp2) + (1523700380805303/50000000000000 : ℝ)*(sp4) + (380924935169369/12500000000000 : ℝ)*(sp5) + (3047396264203363/100000000000000 : ℝ)*(sp6) + (531612713523319/50000000000000 : ℝ)*(sp7) + (531612713523319/50000000000000 : ℝ)*(f.failure) + (1523700380805303/50000000000000 : ℝ)*(f.sum) + (584182547907/224500000000000000000000000 : ℝ)*base65 + (5786055262215063/1122500000000000000000000000000 : ℝ)*base68 + (16435932397119937/1122500000000000000000000000000 : ℝ)*base69 + (80876323239035063/1122500000000000000000000000000 : ℝ)*base72 + (239236576903/112250000000000000000000000 : ℝ)*base73 + (10331432621244937/1122500000000000000000000000000 : ℝ)*base75 + (9834369739524937/1122500000000000000000000000000 : ℝ)*base77 + (11584440662954937/1122500000000000000000000000000 : ℝ)*base79 + (5684318363/7015625000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (7613287/500000000000000000000 : ℝ)*base90 + (7613287/500000000000000000000 : ℝ)*base92 + (7613287/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1705_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4979/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9969/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (17129/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1705_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1705_s4_0 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-357587923/2500000000 : ℝ)*x 0 + (5473224651/10000000000 : ℝ)*x 1 + (2568832217/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (357587923/2500000000 : ℝ)^5263 ≤ (223545639289/2500000000000 : ℝ)^4239 := by
    have hnat : (357587923 : ℕ)^5263*2500000000000^4239 ≤ 223545639289^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357587923 2500000000 223545639289 2500000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5473224651/10000000000 : ℝ)^5263 ≤ (9463278867019/20000000000000 : ℝ)^4239 := by
    have hnat : (5473224651 : ℕ)^5263*20000000000000^4239 ≤ 9463278867019^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5473224651 10000000000 9463278867019 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568832217/5000000000 : ℝ)^5263 ≤ (8748356015301/20000000000000 : ℝ)^4239 := by
    have hnat : (2568832217 : ℕ)^5263*20000000000000^4239 ≤ 8748356015301^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568832217 5000000000 8748356015301 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-357587923/2500000000 : ℝ), (5473224651/10000000000 : ℝ), (2568832217/5000000000 : ℝ)] ![(223545639289/2500000000000 : ℝ), (9463278867019/20000000000000 : ℝ), (8748356015301/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-357587923/2500000000 : ℝ)|^5263 ≤ (223545639289/2500000000000 : ℝ)^4239
        have hw : |(-357587923/2500000000 : ℝ)|=(357587923/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5473224651/10000000000 : ℝ)|^5263 ≤ (9463278867019/20000000000000 : ℝ)^4239
        have hw : |(5473224651/10000000000 : ℝ)|=(5473224651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568832217/5000000000 : ℝ)|^5263 ≤ (8748356015301/20000000000000 : ℝ)^4239
        have hw : |(2568832217/5000000000 : ℝ)|=(2568832217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s4_1 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5345190763/10000000000 : ℝ)*x 0 + (-1604421023/10000000000 : ℝ)*x 1 + (1027532779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345190763/10000000000 : ℝ)^5263 ≤ (45946058274311/100000000000000 : ℝ)^4239 := by
    have hnat : (5345190763 : ℕ)^5263*100000000000000^4239 ≤ 45946058274311^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345190763 10000000000 45946058274311 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1604421023/10000000000 : ℝ)^5263 ≤ (5156083665303/50000000000000 : ℝ)^4239 := by
    have hnat : (1604421023 : ℕ)^5263*50000000000000^4239 ≤ 5156083665303^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1604421023 10000000000 5156083665303 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1027532779/2000000000 : ℝ)^5263 ≤ (21870887189469/50000000000000 : ℝ)^4239 := by
    have hnat : (1027532779 : ℕ)^5263*50000000000000^4239 ≤ 21870887189469^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027532779 2000000000 21870887189469 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345190763/10000000000 : ℝ), (-1604421023/10000000000 : ℝ), (1027532779/2000000000 : ℝ)] ![(45946058274311/100000000000000 : ℝ), (5156083665303/50000000000000 : ℝ), (21870887189469/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345190763/10000000000 : ℝ)|^5263 ≤ (45946058274311/100000000000000 : ℝ)^4239
        have hw : |(5345190763/10000000000 : ℝ)|=(5345190763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1604421023/10000000000 : ℝ)|^5263 ≤ (5156083665303/50000000000000 : ℝ)^4239
        have hw : |(-1604421023/10000000000 : ℝ)|=(1604421023/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1027532779/2000000000 : ℝ)|^5263 ≤ (21870887189469/50000000000000 : ℝ)^4239
        have hw : |(1027532779/2000000000 : ℝ)|=(1027532779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s4_2 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069037879/2000000000 : ℝ)*x 0 + (102753307/200000000 : ℝ)*x 1 + (-802210463/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069037879/2000000000 : ℝ)^5263 ≤ (22973021837353/50000000000000 : ℝ)^4239 := by
    have hnat : (1069037879 : ℕ)^5263*50000000000000^4239 ≤ 22973021837353^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069037879 2000000000 22973021837353 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (102753307/200000000 : ℝ)^5263 ≤ (43741789759197/100000000000000 : ℝ)^4239 := by
    have hnat : (102753307 : ℕ)^5263*100000000000000^4239 ≤ 43741789759197^4239*200000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      102753307 200000000 43741789759197 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (802210463/5000000000 : ℝ)^5263 ≤ (10312166556549/100000000000000 : ℝ)^4239 := by
    have hnat : (802210463 : ℕ)^5263*100000000000000^4239 ≤ 10312166556549^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      802210463 5000000000 10312166556549 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069037879/2000000000 : ℝ), (102753307/200000000 : ℝ), (-802210463/5000000000 : ℝ)] ![(22973021837353/50000000000000 : ℝ), (43741789759197/100000000000000 : ℝ), (10312166556549/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069037879/2000000000 : ℝ)|^5263 ≤ (22973021837353/50000000000000 : ℝ)^4239
        have hw : |(1069037879/2000000000 : ℝ)|=(1069037879/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(102753307/200000000 : ℝ)|^5263 ≤ (43741789759197/100000000000000 : ℝ)^4239
        have hw : |(102753307/200000000 : ℝ)|=(102753307/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-802210463/5000000000 : ℝ)|^5263 ≤ (10312166556549/100000000000000 : ℝ)^4239
        have hw : |(-802210463/5000000000 : ℝ)|=(802210463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s4_3 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4111183883/10000000000 : ℝ)*x 0 + (3648320223/10000000000 : ℝ)*x 1 + (1152524409/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4111183883/10000000000 : ℝ)^5263 ≤ (16583808645759/50000000000000 : ℝ)^4239 := by
    have hnat : (4111183883 : ℕ)^5263*50000000000000^4239 ≤ 16583808645759^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4111183883 10000000000 16583808645759 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3648320223/10000000000 : ℝ)^5263 ≤ (2859626532459/10000000000000 : ℝ)^4239 := by
    have hnat : (3648320223 : ℕ)^5263*10000000000000^4239 ≤ 2859626532459^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3648320223 10000000000 2859626532459 10000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1152524409/2500000000 : ℝ)^5263 ≤ (1911805868301/5000000000000 : ℝ)^4239 := by
    have hnat : (1152524409 : ℕ)^5263*5000000000000^4239 ≤ 1911805868301^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1152524409 2500000000 1911805868301 5000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4111183883/10000000000 : ℝ), (3648320223/10000000000 : ℝ), (1152524409/2500000000 : ℝ)] ![(16583808645759/50000000000000 : ℝ), (2859626532459/10000000000000 : ℝ), (1911805868301/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4111183883/10000000000 : ℝ)|^5263 ≤ (16583808645759/50000000000000 : ℝ)^4239
        have hw : |(4111183883/10000000000 : ℝ)|=(4111183883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3648320223/10000000000 : ℝ)|^5263 ≤ (2859626532459/10000000000000 : ℝ)^4239
        have hw : |(3648320223/10000000000 : ℝ)|=(3648320223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1152524409/2500000000 : ℝ)|^5263 ≤ (1911805868301/5000000000000 : ℝ)^4239
        have hw : |(1152524409/2500000000 : ℝ)|=(1152524409/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s4_4 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1430503849/10000000000 : ℝ)*x 0 + (642670497/1250000000 : ℝ)*x 1 + (1367367641/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1430503849/10000000000 : ℝ)^5263 ≤ (1788601314819/20000000000000 : ℝ)^4239 := by
    have hnat : (1430503849 : ℕ)^5263*20000000000000^4239 ≤ 1788601314819^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1430503849 10000000000 1788601314819 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (642670497/1250000000 : ℝ)^5263 ≤ (4378088994873/10000000000000 : ℝ)^4239 := by
    have hnat : (642670497 : ℕ)^5263*10000000000000^4239 ≤ 4378088994873^4239*1250000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642670497 1250000000 4378088994873 10000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1367367641/2500000000 : ℝ)^5263 ≤ (47276103463001/100000000000000 : ℝ)^4239 := by
    have hnat : (1367367641 : ℕ)^5263*100000000000000^4239 ≤ 47276103463001^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367367641 2500000000 47276103463001 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1430503849/10000000000 : ℝ), (642670497/1250000000 : ℝ), (1367367641/2500000000 : ℝ)] ![(1788601314819/20000000000000 : ℝ), (4378088994873/10000000000000 : ℝ), (47276103463001/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1430503849/10000000000 : ℝ)|^5263 ≤ (1788601314819/20000000000000 : ℝ)^4239
        have hw : |(-1430503849/10000000000 : ℝ)|=(1430503849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(642670497/1250000000 : ℝ)|^5263 ≤ (4378088994873/10000000000000 : ℝ)^4239
        have hw : |(642670497/1250000000 : ℝ)|=(642670497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1367367641/2500000000 : ℝ)|^5263 ≤ (47276103463001/100000000000000 : ℝ)^4239
        have hw : |(1367367641/2500000000 : ℝ)|=(1367367641/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s4_5 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262769237/500000000 : ℝ)*x 0 + (-127261459/1000000000 : ℝ)*x 1 + (5469470761/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262769237/500000000 : ℝ)^5263 ≤ (22494790699897/50000000000000 : ℝ)^4239 := by
    have hnat : (262769237 : ℕ)^5263*50000000000000^4239 ≤ 22494790699897^4239*500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262769237 500000000 22494790699897 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (127261459/1000000000 : ℝ)^5263 ≤ (60424320407/781250000000 : ℝ)^4239 := by
    have hnat : (127261459 : ℕ)^5263*781250000000^4239 ≤ 60424320407^4239*1000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127261459 1000000000 60424320407 781250000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5469470761/10000000000 : ℝ)^5263 ≤ (9455221115427/20000000000000 : ℝ)^4239 := by
    have hnat : (5469470761 : ℕ)^5263*20000000000000^4239 ≤ 9455221115427^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5469470761 10000000000 9455221115427 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262769237/500000000 : ℝ), (-127261459/1000000000 : ℝ), (5469470761/10000000000 : ℝ)] ![(22494790699897/50000000000000 : ℝ), (60424320407/781250000000 : ℝ), (9455221115427/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262769237/500000000 : ℝ)|^5263 ≤ (22494790699897/50000000000000 : ℝ)^4239
        have hw : |(262769237/500000000 : ℝ)|=(262769237/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-127261459/1000000000 : ℝ)|^5263 ≤ (60424320407/781250000000 : ℝ)^4239
        have hw : |(-127261459/1000000000 : ℝ)|=(127261459/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5469470761/10000000000 : ℝ)|^5263 ≤ (9455221115427/20000000000000 : ℝ)^4239
        have hw : |(5469470761/10000000000 : ℝ)|=(5469470761/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s4_6 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1051077099/2000000000 : ℝ)*x 0 + (1367367419/2500000000 : ℝ)*x 1 + (-127261507/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1051077099/2000000000 : ℝ)^5263 ≤ (11247397356103/25000000000000 : ℝ)^4239 := by
    have hnat : (1051077099 : ℕ)^5263*25000000000000^4239 ≤ 11247397356103^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051077099 2000000000 11247397356103 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1367367419/2500000000 : ℝ)^5263 ≤ (472760939333/1000000000000 : ℝ)^4239 := by
    have hnat : (1367367419 : ℕ)^5263*1000000000000^4239 ≤ 472760939333^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367367419 2500000000 472760939333 1000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (127261507/1000000000 : ℝ)^5263 ≤ (966789579249/12500000000000 : ℝ)^4239 := by
    have hnat : (127261507 : ℕ)^5263*12500000000000^4239 ≤ 966789579249^4239*1000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      127261507 1000000000 966789579249 12500000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1051077099/2000000000 : ℝ), (1367367419/2500000000 : ℝ), (-127261507/1000000000 : ℝ)] ![(11247397356103/25000000000000 : ℝ), (472760939333/1000000000000 : ℝ), (966789579249/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1051077099/2000000000 : ℝ)|^5263 ≤ (11247397356103/25000000000000 : ℝ)^4239
        have hw : |(1051077099/2000000000 : ℝ)|=(1051077099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1367367419/2500000000 : ℝ)|^5263 ≤ (472760939333/1000000000000 : ℝ)^4239
        have hw : |(1367367419/2500000000 : ℝ)|=(1367367419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-127261507/1000000000 : ℝ)|^5263 ≤ (966789579249/12500000000000 : ℝ)^4239
        have hw : |(-127261507/1000000000 : ℝ)|=(127261507/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_s4_7 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (205581063/500000000 : ℝ)*x 0 + (574936673/1250000000 : ℝ)*x 1 + (146363359/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (205581063/500000000 : ℝ)^5263 ≤ (4146499793493/12500000000000 : ℝ)^4239 := by
    have hnat : (205581063 : ℕ)^5263*12500000000000^4239 ≤ 4146499793493^4239*500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      205581063 500000000 4146499793493 12500000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (574936673/1250000000 : ℝ)^5263 ≤ (953173749511/2500000000000 : ℝ)^4239 := by
    have hnat : (574936673 : ℕ)^5263*2500000000000^4239 ≤ 953173749511^4239*1250000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      574936673 1250000000 953173749511 2500000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (146363359/400000000 : ℝ)^5263 ≤ (7175262913161/25000000000000 : ℝ)^4239 := by
    have hnat : (146363359 : ℕ)^5263*25000000000000^4239 ≤ 7175262913161^4239*400000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      146363359 400000000 7175262913161 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(205581063/500000000 : ℝ), (574936673/1250000000 : ℝ), (146363359/400000000 : ℝ)] ![(4146499793493/12500000000000 : ℝ), (953173749511/2500000000000 : ℝ), (7175262913161/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(205581063/500000000 : ℝ)|^5263 ≤ (4146499793493/12500000000000 : ℝ)^4239
        have hw : |(205581063/500000000 : ℝ)|=(205581063/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(574936673/1250000000 : ℝ)|^5263 ≤ (953173749511/2500000000000 : ℝ)^4239
        have hw : |(574936673/1250000000 : ℝ)|=(574936673/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(146363359/400000000 : ℝ)|^5263 ≤ (7175262913161/25000000000000 : ℝ)^4239
        have hw : |(146363359/400000000 : ℝ)|=(146363359/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1705_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (997/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2141/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (17129/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9969/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (17129/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9969/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (17129/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9969/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (17129/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9969/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (17129/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9969/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (17129/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9969/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9969/100000 : ℝ) ^ (5255/1024 : ℝ) ≤ (726514479729449/100000000000000000000 : ℝ) := by
    have hpowers : (9969/100000 : ℝ)^5255 ≤ (726514479729449/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9969 : ℕ)^5255*100000000000000000000^1024 ≤ 726514479729449^1024*100000^5255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9969 100000 726514479729449 100000000000000000000 5255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9969/100000 : ℝ)) (X := (726514479729449/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (17129/100000 : ℝ) ^ (5255/1024 : ℝ) ≤ (467410408513791/4000000000000000000 : ℝ) := by
    have hpowers : (17129/100000 : ℝ)^5255 ≤ (467410408513791/4000000000000000000 : ℝ)^1024 := by
      have hnat : (17129 : ℕ)^5255*4000000000000000000^1024 ≤ 467410408513791^1024*100000^5255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        17129 100000 467410408513791 4000000000000000000 5255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (17129/100000 : ℝ)) (X := (467410408513791/4000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000726514479729449/50000000000000000000 : ℝ) ≤ (78125221201973/78125000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (50000726514479729449/50000000000000000000 : ℝ)^1024 ≤ (78125221201973/78125000000000 : ℝ)^5255 := by
      have hnat : (50000726514479729449 : ℕ)^1024*78125000000000^5255 ≤ 78125221201973^5255*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000726514479729449 50000000000000000000 78125221201973 78125000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78125221201973/78125000000000 : ℝ)) (X := (50000726514479729449/50000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6250775735918285889/6250000000000000000 : ℝ) ≤ (10000241846285109/10000000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (6250775735918285889/6250000000000000000 : ℝ)^1024 ≤ (10000241846285109/10000000000000000 : ℝ)^5255 := by
      have hnat : (6250775735918285889 : ℕ)^1024*10000000000000000^5255 ≤ 10000241846285109^5255*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250775735918285889 6250000000000000000 10000241846285109 10000000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000241846285109/10000000000000000 : ℝ)) (X := (6250775735918285889/6250000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2000467410408513791/2000000000000000000 : ℝ) ≤ (5000227689358837/5000000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (2000467410408513791/2000000000000000000 : ℝ)^1024 ≤ (5000227689358837/5000000000000000 : ℝ)^5255 := by
      have hnat : (2000467410408513791 : ℕ)^1024*5000000000000000^5255 ≤ 5000227689358837^5255*2000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2000467410408513791 2000000000000000000 5000227689358837 5000000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000227689358837/5000000000000000 : ℝ)) (X := (2000467410408513791/2000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(726514479729449/100000000000000000000 : ℝ) ≤ ((7159594531754373407/7160000000000000000 : ℝ)+2*(42706486513/143200000000000 : ℝ)*(9969/100000 : ℝ))^(5255/1024 : ℝ) := by
    rw [show (7159594531754373407/7160000000000000000 : ℝ)+2*(42706486513/143200000000000 : ℝ)*(9969/100000 : ℝ)=(78125221201973/78125000000000 : ℝ) by norm_num, show 1+2*(726514479729449/100000000000000000000 : ℝ)=(50000726514479729449/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(467410408513791/4000000000000000000 : ℝ)+(726514479729449/100000000000000000000 : ℝ) ≤ ((7159594531754373407/7160000000000000000 : ℝ)+(42706486513/143200000000000 : ℝ)*((17129/100000 : ℝ)+(9969/100000 : ℝ)))^(5255/1024 : ℝ) := by
    rw [show (7159594531754373407/7160000000000000000 : ℝ)+(42706486513/143200000000000 : ℝ)*((17129/100000 : ℝ)+(9969/100000 : ℝ))=(10000241846285109/10000000000000000 : ℝ) by norm_num, show 1+(467410408513791/4000000000000000000 : ℝ)+(726514479729449/100000000000000000000 : ℝ)=(6250775735918285889/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(467410408513791/4000000000000000000 : ℝ) ≤ ((7159594531754373407/7160000000000000000 : ℝ)+2*(42706486513/143200000000000 : ℝ)*(17129/100000 : ℝ))^(5255/1024 : ℝ) := by
    rw [show (7159594531754373407/7160000000000000000 : ℝ)+2*(42706486513/143200000000000 : ℝ)*(17129/100000 : ℝ)=(5000227689358837/5000000000000000 : ℝ) by norm_num, show 1+2*(467410408513791/4000000000000000000 : ℝ)=(2000467410408513791/2000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7159594531754373407/7160000000000000000 : ℝ)*(X 1 0+X 2 0)+(42706486513/143200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (9969/100000 : ℝ)) (hi := (17129/100000 : ℝ)) (c := (7159594531754373407/7160000000000000000 : ℝ)) (alpha := (42706486513/143200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7159594531754373407/7160000000000000000 : ℝ)*(X 0 1+X 2 1)+(42706486513/143200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (9969/100000 : ℝ)) (hi := (17129/100000 : ℝ)) (c := (7159594531754373407/7160000000000000000 : ℝ)) (alpha := (42706486513/143200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7159594531754373407/7160000000000000000 : ℝ)*(X 0 2+X 1 2)+(42706486513/143200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (9969/100000 : ℝ)) (hi := (17129/100000 : ℝ)) (c := (7159594531754373407/7160000000000000000 : ℝ)) (alpha := (42706486513/143200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-357587923/2500000000 : ℝ)*X 0 0+(5473224651/10000000000 : ℝ)*X 0 1+(2568832217/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345190763/10000000000 : ℝ)*X 1 0+(-1604421023/10000000000 : ℝ)*X 1 1+(1027532779/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069037879/2000000000 : ℝ)*X 2 0+(102753307/200000000 : ℝ)*X 2 1+(-802210463/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4111183883/10000000000 : ℝ)*X 0 0+(3648320223/10000000000 : ℝ)*X 0 1+(1152524409/2500000000 : ℝ)*X 0 2+(4111183883/10000000000 : ℝ)*X 1 0+(3648320223/10000000000 : ℝ)*X 1 1+(1152524409/2500000000 : ℝ)*X 1 2+(4111183883/10000000000 : ℝ)*X 2 0+(3648320223/10000000000 : ℝ)*X 2 1+(1152524409/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1430503849/10000000000 : ℝ)*X 0 0+(642670497/1250000000 : ℝ)*X 0 1+(1367367641/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((262769237/500000000 : ℝ)*X 1 0+(-127261459/1000000000 : ℝ)*X 1 1+(5469470761/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1051077099/2000000000 : ℝ)*X 2 0+(1367367419/2500000000 : ℝ)*X 2 1+(-127261507/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((205581063/500000000 : ℝ)*X 0 0+(574936673/1250000000 : ℝ)*X 0 1+(146363359/400000000 : ℝ)*X 0 2+(205581063/500000000 : ℝ)*X 1 0+(574936673/1250000000 : ℝ)*X 1 1+(146363359/400000000 : ℝ)*X 1 2+(205581063/500000000 : ℝ)*X 2 0+(574936673/1250000000 : ℝ)*X 2 1+(146363359/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (6244402886928682833039/3580000000000000000000000000 : ℝ) := by norm_num
    linear_combination (494411911/50000000000000 : ℝ)*(base19) + (86962551/100000000000000 : ℝ)*(base23) + (74384037/100000000000000 : ℝ)*(lower2) + (9662063/5000000000000 : ℝ)*(upper3) + (5654141/10000000000000 : ℝ)*(upper5) + (1004961958771719/50000000000000 : ℝ)*(major0) + (1004961958771719/50000000000000 : ℝ)*(major1) + (1004961958771719/50000000000000 : ℝ)*(major2) + (372512339956731/12500000000000 : ℝ)*(sp0) + (596020311254879/20000000000000 : ℝ)*(sp1) + (1490051229067833/50000000000000 : ℝ)*(sp2) + (1039743292832379/100000000000000 : ℝ)*(sp3) + (239090273/6250000000000 : ℝ)*(sp4) + (969507361/50000000000000 : ℝ)*(sp7) + (1039745231847101/100000000000000 : ℝ)*(f.failure) + (372512818137277/12500000000000 : ℝ)*(f.sum) + (8838385544027/3580000000000000000000000000 : ℝ)*base65 + (524962325291626633/358000000000000000000000000000000 : ℝ)*base67 + (1775396325565626633/358000000000000000000000000000000 : ℝ)*base69 + (686328397693626633/358000000000000000000000000000000 : ℝ)*base71 + (9007340048553/3580000000000000000000000000 : ℝ)*base74 + (2967403047312373367/358000000000000000000000000000000 : ℝ)*base76 + (218355031536373367/358000000000000000000000000000000 : ℝ)*base78 + (162211115180373367/358000000000000000000000000000000 : ℝ)*base80 + (13989879710607/3580000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (4592627/1000000000000000000000 : ℝ)*base89 + (4592627/1000000000000000000000 : ℝ)*base91 + (4592627/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1135626812341862721104582493/179000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31333463/6250000000000 : ℝ)*(base19) + (68937413/5000000000000 : ℝ)*(base23) + (535226181/100000000000000 : ℝ)*(lower1) + (29077351/12500000000000 : ℝ)*(lower4) + (25246661/100000000000000 : ℝ)*(upper5) + (2055574192176233/100000000000000 : ℝ)*(major0) + (2055574192176233/100000000000000 : ℝ)*(major1) + (2055574192176233/100000000000000 : ℝ)*(major2) + (7655400911/100000000000000 : ℝ)*(sp0) + (17955043/10000000000000 : ℝ)*(sp1) + (380972516917433/12500000000000 : ℝ)*(sp4) + (3047787109854537/100000000000000 : ℝ)*(sp5) + (609557282398423/20000000000000 : ℝ)*(sp6) + (1063360382135959/100000000000000 : ℝ)*(sp7) + (1063360382135959/100000000000000 : ℝ)*(f.failure) + (24382302325923/800000000000 : ℝ)*(f.sum) + (5554177702809/7160000000000000000000000000 : ℝ)*base65 + (895213982686914169/716000000000000000000000000000000 : ℝ)*base68 + (2001500509110914169/716000000000000000000000000000000 : ℝ)*base70 + (1646463113050914169/716000000000000000000000000000000 : ℝ)*base72 + (1536445792231/7160000000000000000000000000 : ℝ)*base74 + (2526497497997085831/716000000000000000000000000000000 : ℝ)*base75 + (162287086830914169/716000000000000000000000000000000 : ℝ)*base78 + (2062149934226914169/716000000000000000000000000000000 : ℝ)*base80 + (30586368384529/7160000000000000000000000000 : ℝ)*base81 + (2496007/1000000000000000000000 : ℝ)*base90 + (2496007/1000000000000000000000 : ℝ)*base92 + (2496007/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1705_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (17129/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9969/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (997/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2141/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1705_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1705_box_0 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-276951609/2500000000 : ℝ)*x 0 + (338742897/625000000 : ℝ)*x 1 + (5419886723/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (276951609/2500000000 : ℝ)^5263 ≤ (1627715376419/25000000000000 : ℝ)^4239 := by
    have hnat : (276951609 : ℕ)^5263*25000000000000^4239 ≤ 1627715376419^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276951609 2500000000 1627715376419 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (338742897/625000000 : ℝ)^5263 ≤ (4674456725213/10000000000000 : ℝ)^4239 := by
    have hnat : (338742897 : ℕ)^5263*10000000000000^4239 ≤ 4674456725213^4239*625000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      338742897 625000000 4674456725213 10000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419886723/10000000000 : ℝ)^5263 ≤ (46744571224821/100000000000000 : ℝ)^4239 := by
    have hnat : (5419886723 : ℕ)^5263*100000000000000^4239 ≤ 46744571224821^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419886723 10000000000 46744571224821 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-276951609/2500000000 : ℝ), (338742897/625000000 : ℝ), (5419886723/10000000000 : ℝ)] ![(1627715376419/25000000000000 : ℝ), (4674456725213/10000000000000 : ℝ), (46744571224821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-276951609/2500000000 : ℝ)|^5263 ≤ (1627715376419/25000000000000 : ℝ)^4239
        have hw : |(-276951609/2500000000 : ℝ)|=(276951609/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(338742897/625000000 : ℝ)|^5263 ≤ (4674456725213/10000000000000 : ℝ)^4239
        have hw : |(338742897/625000000 : ℝ)|=(338742897/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419886723/10000000000 : ℝ)|^5263 ≤ (46744571224821/100000000000000 : ℝ)^4239
        have hw : |(5419886723/10000000000 : ℝ)|=(5419886723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_1 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5225624643/10000000000 : ℝ)*x 0 + (-1383799223/10000000000 : ℝ)*x 1 + (5419887227/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5225624643/10000000000 : ℝ)^5263 ≤ (44673488922349/100000000000000 : ℝ)^4239 := by
    have hnat : (5225624643 : ℕ)^5263*100000000000000^4239 ≤ 44673488922349^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5225624643 10000000000 44673488922349 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1383799223/10000000000 : ℝ)^5263 ≤ (1716386889603/20000000000000 : ℝ)^4239 := by
    have hnat : (1383799223 : ℕ)^5263*20000000000000^4239 ≤ 1716386889603^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1383799223 10000000000 1716386889603 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5419887227/10000000000 : ℝ)^5263 ≤ (9348915324337/20000000000000 : ℝ)^4239 := by
    have hnat : (5419887227 : ℕ)^5263*20000000000000^4239 ≤ 9348915324337^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419887227 10000000000 9348915324337 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5225624643/10000000000 : ℝ), (-1383799223/10000000000 : ℝ), (5419887227/10000000000 : ℝ)] ![(44673488922349/100000000000000 : ℝ), (1716386889603/20000000000000 : ℝ), (9348915324337/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5225624643/10000000000 : ℝ)|^5263 ≤ (44673488922349/100000000000000 : ℝ)^4239
        have hw : |(5225624643/10000000000 : ℝ)|=(5225624643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1383799223/10000000000 : ℝ)|^5263 ≤ (1716386889603/20000000000000 : ℝ)^4239
        have hw : |(-1383799223/10000000000 : ℝ)|=(1383799223/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5419887227/10000000000 : ℝ)|^5263 ≤ (9348915324337/20000000000000 : ℝ)^4239
        have hw : |(5419887227/10000000000 : ℝ)|=(5419887227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_2 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2612812479/5000000000 : ℝ)*x 0 + (5419887123/10000000000 : ℝ)*x 1 + (-345949733/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2612812479/5000000000 : ℝ)^5263 ≤ (22336746132889/50000000000000 : ℝ)^4239 := by
    have hnat : (2612812479 : ℕ)^5263*50000000000000^4239 ≤ 22336746132889^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2612812479 5000000000 22336746132889 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5419887123/10000000000 : ℝ)^5263 ≤ (46744575508047/100000000000000 : ℝ)^4239 := by
    have hnat : (5419887123 : ℕ)^5263*100000000000000^4239 ≤ 46744575508047^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5419887123 10000000000 46744575508047 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345949733/2500000000 : ℝ)^5263 ≤ (6704634537/78125000000 : ℝ)^4239 := by
    have hnat : (345949733 : ℕ)^5263*78125000000^4239 ≤ 6704634537^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345949733 2500000000 6704634537 78125000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2612812479/5000000000 : ℝ), (5419887123/10000000000 : ℝ), (-345949733/2500000000 : ℝ)] ![(22336746132889/50000000000000 : ℝ), (46744575508047/100000000000000 : ℝ), (6704634537/78125000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2612812479/5000000000 : ℝ)|^5263 ≤ (22336746132889/50000000000000 : ℝ)^4239
        have hw : |(2612812479/5000000000 : ℝ)|=(2612812479/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5419887123/10000000000 : ℝ)|^5263 ≤ (46744575508047/100000000000000 : ℝ)^4239
        have hw : |(5419887123/10000000000 : ℝ)|=(5419887123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-345949733/2500000000 : ℝ)|^5263 ≤ (6704634537/78125000000 : ℝ)^4239
        have hw : |(-345949733/2500000000 : ℝ)|=(345949733/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_3 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4493592193/10000000000 : ℝ)*x 0 + (3941845077/10000000000 : ℝ)*x 1 + (492730643/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4493592193/10000000000 : ℝ)^5263 ≤ (37040083246537/100000000000000 : ℝ)^4239 := by
    have hnat : (4493592193 : ℕ)^5263*100000000000000^4239 ≤ 37040083246537^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4493592193 10000000000 37040083246537 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3941845077/10000000000 : ℝ)^5263 ≤ (31479958041033/100000000000000 : ℝ)^4239 := by
    have hnat : (3941845077 : ℕ)^5263*100000000000000^4239 ≤ 31479958041033^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3941845077 10000000000 31479958041033 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (492730643/1250000000 : ℝ)^5263 ≤ (7869989676339/25000000000000 : ℝ)^4239 := by
    have hnat : (492730643 : ℕ)^5263*25000000000000^4239 ≤ 7869989676339^4239*1250000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      492730643 1250000000 7869989676339 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4493592193/10000000000 : ℝ), (3941845077/10000000000 : ℝ), (492730643/1250000000 : ℝ)] ![(37040083246537/100000000000000 : ℝ), (31479958041033/100000000000000 : ℝ), (7869989676339/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4493592193/10000000000 : ℝ)|^5263 ≤ (37040083246537/100000000000000 : ℝ)^4239
        have hw : |(4493592193/10000000000 : ℝ)|=(4493592193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3941845077/10000000000 : ℝ)|^5263 ≤ (31479958041033/100000000000000 : ℝ)^4239
        have hw : |(3941845077/10000000000 : ℝ)|=(3941845077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(492730643/1250000000 : ℝ)|^5263 ≤ (7869989676339/25000000000000 : ℝ)^4239
        have hw : |(492730643/1250000000 : ℝ)|=(492730643/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_4 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-44340223/250000000 : ℝ)*x 0 + (5177237409/10000000000 : ℝ)*x 1 + (5177237459/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (44340223/250000000 : ℝ)^5263 ≤ (93432322461/800000000000 : ℝ)^4239 := by
    have hnat : (44340223 : ℕ)^5263*800000000000^4239 ≤ 93432322461^4239*250000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44340223 250000000 93432322461 800000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177237409/10000000000 : ℝ)^5263 ≤ (5520059946811/12500000000000 : ℝ)^4239 := by
    have hnat : (5177237409 : ℕ)^5263*12500000000000^4239 ≤ 5520059946811^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177237409 10000000000 5520059946811 12500000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5177237459/10000000000 : ℝ)^5263 ≤ (5520060013/12500000000 : ℝ)^4239 := by
    have hnat : (5177237459 : ℕ)^5263*12500000000^4239 ≤ 5520060013^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177237459 10000000000 5520060013 12500000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-44340223/250000000 : ℝ), (5177237409/10000000000 : ℝ), (5177237459/10000000000 : ℝ)] ![(93432322461/800000000000 : ℝ), (5520059946811/12500000000000 : ℝ), (5520060013/12500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-44340223/250000000 : ℝ)|^5263 ≤ (93432322461/800000000000 : ℝ)^4239
        have hw : |(-44340223/250000000 : ℝ)|=(44340223/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177237409/10000000000 : ℝ)|^5263 ≤ (5520059946811/12500000000000 : ℝ)^4239
        have hw : |(5177237409/10000000000 : ℝ)|=(5177237409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5177237459/10000000000 : ℝ)|^5263 ≤ (5520060013/12500000000 : ℝ)^4239
        have hw : |(5177237459/10000000000 : ℝ)|=(5177237459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_5 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5390382361/10000000000 : ℝ)*x 0 + (-745227869/5000000000 : ℝ)*x 1 + (2588618771/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5390382361/10000000000 : ℝ)^5263 ≤ (9285768933967/20000000000000 : ℝ)^4239 := by
    have hnat : (5390382361 : ℕ)^5263*20000000000000^4239 ≤ 9285768933967^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390382361 10000000000 9285768933967 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (745227869/5000000000 : ℝ)^5263 ≤ (4705337166421/50000000000000 : ℝ)^4239 := by
    have hnat : (745227869 : ℕ)^5263*50000000000000^4239 ≤ 4705337166421^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745227869 5000000000 4705337166421 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2588618771/5000000000 : ℝ)^5263 ≤ (44160480982989/100000000000000 : ℝ)^4239 := by
    have hnat : (2588618771 : ℕ)^5263*100000000000000^4239 ≤ 44160480982989^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588618771 5000000000 44160480982989 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5390382361/10000000000 : ℝ), (-745227869/5000000000 : ℝ), (2588618771/5000000000 : ℝ)] ![(9285768933967/20000000000000 : ℝ), (4705337166421/50000000000000 : ℝ), (44160480982989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5390382361/10000000000 : ℝ)|^5263 ≤ (9285768933967/20000000000000 : ℝ)^4239
        have hw : |(5390382361/10000000000 : ℝ)|=(5390382361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-745227869/5000000000 : ℝ)|^5263 ≤ (4705337166421/50000000000000 : ℝ)^4239
        have hw : |(-745227869/5000000000 : ℝ)|=(745227869/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2588618771/5000000000 : ℝ)|^5263 ≤ (44160480982989/100000000000000 : ℝ)^4239
        have hw : |(2588618771/5000000000 : ℝ)|=(2588618771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_6 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2695191387/5000000000 : ℝ)*x 0 + (5177237293/10000000000 : ℝ)*x 1 + (-149045551/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2695191387/5000000000 : ℝ)^5263 ≤ (23214424543219/50000000000000 : ℝ)^4239 := by
    have hnat : (2695191387 : ℕ)^5263*50000000000000^4239 ≤ 23214424543219^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695191387 5000000000 23214424543219 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177237293/10000000000 : ℝ)^5263 ≤ (44160478346021/100000000000000 : ℝ)^4239 := by
    have hnat : (5177237293 : ℕ)^5263*100000000000000^4239 ≤ 44160478346021^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177237293 10000000000 44160478346021 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (149045551/1000000000 : ℝ)^5263 ≤ (1882134509101/20000000000000 : ℝ)^4239 := by
    have hnat : (149045551 : ℕ)^5263*20000000000000^4239 ≤ 1882134509101^4239*1000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      149045551 1000000000 1882134509101 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2695191387/5000000000 : ℝ), (5177237293/10000000000 : ℝ), (-149045551/1000000000 : ℝ)] ![(23214424543219/50000000000000 : ℝ), (44160478346021/100000000000000 : ℝ), (1882134509101/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2695191387/5000000000 : ℝ)|^5263 ≤ (23214424543219/50000000000000 : ℝ)^4239
        have hw : |(2695191387/5000000000 : ℝ)|=(2695191387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177237293/10000000000 : ℝ)|^5263 ≤ (44160478346021/100000000000000 : ℝ)^4239
        have hw : |(5177237293/10000000000 : ℝ)|=(5177237293/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-149045551/1000000000 : ℝ)|^5263 ≤ (1882134509101/20000000000000 : ℝ)^4239
        have hw : |(-149045551/1000000000 : ℝ)|=(149045551/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_7 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3713384329/10000000000 : ℝ)*x 0 + (1082778387/2500000000 : ℝ)*x 1 + (4331114071/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3713384329/10000000000 : ℝ)^5263 ≤ (7307700999381/25000000000000 : ℝ)^4239 := by
    have hnat : (3713384329 : ℕ)^5263*25000000000000^4239 ≤ 7307700999381^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3713384329 10000000000 7307700999381 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082778387/2500000000 : ℝ)^5263 ≤ (35384595342261/100000000000000 : ℝ)^4239 := by
    have hnat : (1082778387 : ℕ)^5263*100000000000000^4239 ≤ 35384595342261^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082778387 2500000000 35384595342261 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4331114071/10000000000 : ℝ)^5263 ≤ (4423075080909/12500000000000 : ℝ)^4239 := by
    have hnat : (4331114071 : ℕ)^5263*12500000000000^4239 ≤ 4423075080909^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331114071 10000000000 4423075080909 12500000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3713384329/10000000000 : ℝ), (1082778387/2500000000 : ℝ), (4331114071/10000000000 : ℝ)] ![(7307700999381/25000000000000 : ℝ), (35384595342261/100000000000000 : ℝ), (4423075080909/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3713384329/10000000000 : ℝ)|^5263 ≤ (7307700999381/25000000000000 : ℝ)^4239
        have hw : |(3713384329/10000000000 : ℝ)|=(3713384329/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082778387/2500000000 : ℝ)|^5263 ≤ (35384595342261/100000000000000 : ℝ)^4239
        have hw : |(1082778387/2500000000 : ℝ)|=(1082778387/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4331114071/10000000000 : ℝ)|^5263 ≤ (4423075080909/12500000000000 : ℝ)^4239
        have hw : |(4331114071/10000000000 : ℝ)|=(4331114071/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_8 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-65219391/400000000 : ℝ)*x 0 + (4998399613/10000000000 : ℝ)*x 1 + (5462836651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (65219391/400000000 : ℝ)^5263 ≤ (10520561867487/100000000000000 : ℝ)^4239 := by
    have hnat : (65219391 : ℕ)^5263*100000000000000^4239 ≤ 10520561867487^4239*400000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65219391 400000000 10520561867487 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4998399613/10000000000 : ℝ)^5263 ≤ (10568629259427/25000000000000 : ℝ)^4239 := by
    have hnat : (4998399613 : ℕ)^5263*25000000000000^4239 ≤ 10568629259427^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4998399613 10000000000 10568629259427 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5462836651/10000000000 : ℝ)^5263 ≤ (11801230272463/25000000000000 : ℝ)^4239 := by
    have hnat : (5462836651 : ℕ)^5263*25000000000000^4239 ≤ 11801230272463^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462836651 10000000000 11801230272463 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-65219391/400000000 : ℝ), (4998399613/10000000000 : ℝ), (5462836651/10000000000 : ℝ)] ![(10520561867487/100000000000000 : ℝ), (10568629259427/25000000000000 : ℝ), (11801230272463/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-65219391/400000000 : ℝ)|^5263 ≤ (10520561867487/100000000000000 : ℝ)^4239
        have hw : |(-65219391/400000000 : ℝ)|=(65219391/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4998399613/10000000000 : ℝ)|^5263 ≤ (10568629259427/25000000000000 : ℝ)^4239
        have hw : |(4998399613/10000000000 : ℝ)|=(4998399613/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5462836651/10000000000 : ℝ)|^5263 ≤ (11801230272463/25000000000000 : ℝ)^4239
        have hw : |(5462836651/10000000000 : ℝ)|=(5462836651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_9 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1039295927/2000000000 : ℝ)*x 0 + (-1364127453/10000000000 : ℝ)*x 1 + (546283687/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1039295927/2000000000 : ℝ)^5263 ≤ (44364350690219/100000000000000 : ℝ)^4239 := by
    have hnat : (1039295927 : ℕ)^5263*100000000000000^4239 ≤ 44364350690219^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039295927 2000000000 44364350690219 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1364127453/10000000000 : ℝ)^5263 ≤ (8430725857689/100000000000000 : ℝ)^4239 := by
    have hnat : (1364127453 : ℕ)^5263*100000000000000^4239 ≤ 8430725857689^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1364127453 10000000000 8430725857689 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (546283687/1000000000 : ℝ)^5263 ≤ (47204923439393/100000000000000 : ℝ)^4239 := by
    have hnat : (546283687 : ℕ)^5263*100000000000000^4239 ≤ 47204923439393^4239*1000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      546283687 1000000000 47204923439393 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1039295927/2000000000 : ℝ), (-1364127453/10000000000 : ℝ), (546283687/1000000000 : ℝ)] ![(44364350690219/100000000000000 : ℝ), (8430725857689/100000000000000 : ℝ), (47204923439393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1039295927/2000000000 : ℝ)|^5263 ≤ (44364350690219/100000000000000 : ℝ)^4239
        have hw : |(1039295927/2000000000 : ℝ)|=(1039295927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1364127453/10000000000 : ℝ)|^5263 ≤ (8430725857689/100000000000000 : ℝ)^4239
        have hw : |(-1364127453/10000000000 : ℝ)|=(1364127453/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(546283687/1000000000 : ℝ)|^5263 ≤ (47204923439393/100000000000000 : ℝ)^4239
        have hw : |(546283687/1000000000 : ℝ)|=(546283687/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_10 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196480011/10000000000 : ℝ)*x 0 + (5462836441/10000000000 : ℝ)*x 1 + (-682063767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196480011/10000000000 : ℝ)^5263 ≤ (22182177337859/50000000000000 : ℝ)^4239 := by
    have hnat : (5196480011 : ℕ)^5263*50000000000000^4239 ≤ 22182177337859^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196480011 10000000000 22182177337859 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5462836441/10000000000 : ℝ)^5263 ≤ (47204918836867/100000000000000 : ℝ)^4239 := by
    have hnat : (5462836441 : ℕ)^5263*100000000000000^4239 ≤ 47204918836867^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5462836441 10000000000 47204918836867 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (682063767/5000000000 : ℝ)^5263 ≤ (8430726479223/100000000000000 : ℝ)^4239 := by
    have hnat : (682063767 : ℕ)^5263*100000000000000^4239 ≤ 8430726479223^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      682063767 5000000000 8430726479223 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196480011/10000000000 : ℝ), (5462836441/10000000000 : ℝ), (-682063767/5000000000 : ℝ)] ![(22182177337859/50000000000000 : ℝ), (47204918836867/100000000000000 : ℝ), (8430726479223/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196480011/10000000000 : ℝ)|^5263 ≤ (22182177337859/50000000000000 : ℝ)^4239
        have hw : |(5196480011/10000000000 : ℝ)|=(5196480011/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5462836441/10000000000 : ℝ)|^5263 ≤ (47204918836867/100000000000000 : ℝ)^4239
        have hw : |(5462836441/10000000000 : ℝ)|=(5462836441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-682063767/5000000000 : ℝ)|^5263 ≤ (8430726479223/100000000000000 : ℝ)^4239
        have hw : |(-682063767/5000000000 : ℝ)|=(682063767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_11 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (72292167/156250000 : ℝ)*x 0 + (1936380399/5000000000 : ℝ)*x 1 + (968190397/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (72292167/156250000 : ℝ)^5263 ≤ (38407141699523/100000000000000 : ℝ)^4239 := by
    have hnat : (72292167 : ℕ)^5263*100000000000000^4239 ≤ 38407141699523^4239*156250000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      72292167 156250000 38407141699523 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1936380399/5000000000 : ℝ)^5263 ≤ (7699106310081/25000000000000 : ℝ)^4239 := by
    have hnat : (1936380399 : ℕ)^5263*25000000000000^4239 ≤ 7699106310081^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1936380399 5000000000 7699106310081 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (968190397/2500000000 : ℝ)^5263 ≤ (15398216520001/50000000000000 : ℝ)^4239 := by
    have hnat : (968190397 : ℕ)^5263*50000000000000^4239 ≤ 15398216520001^4239*2500000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      968190397 2500000000 15398216520001 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(72292167/156250000 : ℝ), (1936380399/5000000000 : ℝ), (968190397/2500000000 : ℝ)] ![(38407141699523/100000000000000 : ℝ), (7699106310081/25000000000000 : ℝ), (15398216520001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(72292167/156250000 : ℝ)|^5263 ≤ (38407141699523/100000000000000 : ℝ)^4239
        have hw : |(72292167/156250000 : ℝ)|=(72292167/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1936380399/5000000000 : ℝ)|^5263 ≤ (7699106310081/25000000000000 : ℝ)^4239
        have hw : |(1936380399/5000000000 : ℝ)|=(1936380399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(968190397/2500000000 : ℝ)|^5263 ≤ (15398216520001/50000000000000 : ℝ)^4239
        have hw : |(968190397/2500000000 : ℝ)|=(968190397/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_12 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-249125027/2000000000 : ℝ)*x 0 + (2795081991/5000000000 : ℝ)*x 1 + (5152063527/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (249125027/2000000000 : ℝ)^5263 ≤ (1506237078269/20000000000000 : ℝ)^4239 := by
    have hnat : (249125027 : ℕ)^5263*20000000000000^4239 ≤ 1506237078269^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249125027 2000000000 1506237078269 20000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2795081991/5000000000 : ℝ)^5263 ≤ (48574775616361/100000000000000 : ℝ)^4239 := by
    have hnat : (2795081991 : ℕ)^5263*100000000000000^4239 ≤ 48574775616361^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2795081991 5000000000 48574775616361 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152063527/10000000000 : ℝ)^5263 ≤ (43894038978497/100000000000000 : ℝ)^4239 := by
    have hnat : (5152063527 : ℕ)^5263*100000000000000^4239 ≤ 43894038978497^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152063527 10000000000 43894038978497 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-249125027/2000000000 : ℝ), (2795081991/5000000000 : ℝ), (5152063527/10000000000 : ℝ)] ![(1506237078269/20000000000000 : ℝ), (48574775616361/100000000000000 : ℝ), (43894038978497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-249125027/2000000000 : ℝ)|^5263 ≤ (1506237078269/20000000000000 : ℝ)^4239
        have hw : |(-249125027/2000000000 : ℝ)|=(249125027/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2795081991/5000000000 : ℝ)|^5263 ≤ (48574775616361/100000000000000 : ℝ)^4239
        have hw : |(2795081991/5000000000 : ℝ)|=(2795081991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152063527/10000000000 : ℝ)|^5263 ≤ (43894038978497/100000000000000 : ℝ)^4239
        have hw : |(5152063527/10000000000 : ℝ)|=(5152063527/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_13 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5407505619/10000000000 : ℝ)*x 0 + (-93816703/625000000 : ℝ)*x 1 + (5152063467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5407505619/10000000000 : ℝ)^5263 ≤ (23306015091269/50000000000000 : ℝ)^4239 := by
    have hnat : (5407505619 : ℕ)^5263*50000000000000^4239 ≤ 23306015091269^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407505619 10000000000 23306015091269 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (93816703/625000000 : ℝ)^5263 ≤ (9493931462909/100000000000000 : ℝ)^4239 := by
    have hnat : (93816703 : ℕ)^5263*100000000000000^4239 ≤ 9493931462909^4239*625000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      93816703 625000000 9493931462909 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152063467/10000000000 : ℝ)^5263 ≤ (4389403834383/10000000000000 : ℝ)^4239 := by
    have hnat : (5152063467 : ℕ)^5263*10000000000000^4239 ≤ 4389403834383^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152063467 10000000000 4389403834383 10000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5407505619/10000000000 : ℝ), (-93816703/625000000 : ℝ), (5152063467/10000000000 : ℝ)] ![(23306015091269/50000000000000 : ℝ), (9493931462909/100000000000000 : ℝ), (4389403834383/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5407505619/10000000000 : ℝ)|^5263 ≤ (23306015091269/50000000000000 : ℝ)^4239
        have hw : |(5407505619/10000000000 : ℝ)|=(5407505619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-93816703/625000000 : ℝ)|^5263 ≤ (9493931462909/100000000000000 : ℝ)^4239
        have hw : |(-93816703/625000000 : ℝ)|=(93816703/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152063467/10000000000 : ℝ)|^5263 ≤ (4389403834383/10000000000000 : ℝ)^4239
        have hw : |(5152063467/10000000000 : ℝ)|=(5152063467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_14 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1081501077/2000000000 : ℝ)*x 0 + (5152063539/10000000000 : ℝ)*x 1 + (-150106747/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1081501077/2000000000 : ℝ)^5263 ≤ (11653006919559/25000000000000 : ℝ)^4239 := by
    have hnat : (1081501077 : ℕ)^5263*25000000000000^4239 ≤ 11653006919559^4239*2000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1081501077 2000000000 11653006919559 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152063539/10000000000 : ℝ)^5263 ≤ (4389403910543/10000000000000 : ℝ)^4239 := by
    have hnat : (5152063539 : ℕ)^5263*10000000000000^4239 ≤ 4389403910543^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152063539 10000000000 4389403910543 10000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (150106747/1000000000 : ℝ)^5263 ≤ (2373483301549/25000000000000 : ℝ)^4239 := by
    have hnat : (150106747 : ℕ)^5263*25000000000000^4239 ≤ 2373483301549^4239*1000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      150106747 1000000000 2373483301549 25000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1081501077/2000000000 : ℝ), (5152063539/10000000000 : ℝ), (-150106747/1000000000 : ℝ)] ![(11653006919559/25000000000000 : ℝ), (4389403910543/10000000000000 : ℝ), (2373483301549/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1081501077/2000000000 : ℝ)|^5263 ≤ (11653006919559/25000000000000 : ℝ)^4239
        have hw : |(1081501077/2000000000 : ℝ)|=(1081501077/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152063539/10000000000 : ℝ)|^5263 ≤ (4389403910543/10000000000000 : ℝ)^4239
        have hw : |(5152063539/10000000000 : ℝ)|=(5152063539/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-150106747/1000000000 : ℝ)|^5263 ≤ (2373483301549/25000000000000 : ℝ)^4239
        have hw : |(-150106747/1000000000 : ℝ)|=(150106747/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1705_box_15 (p : ℝ) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (3629456933/10000000000 : ℝ)*x 0 + (2185695217/5000000000 : ℝ)*x 1 + (2185694887/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (3629456933/10000000000 : ℝ)^5263 ≤ (28412809246023/100000000000000 : ℝ)^4239 := by
    have hnat : (3629456933 : ℕ)^5263*100000000000000^4239 ≤ 28412809246023^4239*10000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3629456933 10000000000 28412809246023 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2185695217/5000000000 : ℝ)^5263 ≤ (35793598719709/100000000000000 : ℝ)^4239 := by
    have hnat : (2185695217 : ℕ)^5263*100000000000000^4239 ≤ 35793598719709^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185695217 5000000000 35793598719709 100000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2185694887/5000000000 : ℝ)^5263 ≤ (17896796005031/50000000000000 : ℝ)^4239 := by
    have hnat : (2185694887 : ℕ)^5263*50000000000000^4239 ≤ 17896796005031^4239*5000000000^5263 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2185694887 5000000000 17896796005031 50000000000000 5263 4239 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5263/1024 : ℝ)) 5263 4239 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(3629456933/10000000000 : ℝ), (2185695217/5000000000 : ℝ), (2185694887/5000000000 : ℝ)] ![(28412809246023/100000000000000 : ℝ), (35793598719709/100000000000000 : ℝ), (17896796005031/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(3629456933/10000000000 : ℝ)|^5263 ≤ (28412809246023/100000000000000 : ℝ)^4239
        have hw : |(3629456933/10000000000 : ℝ)|=(3629456933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2185695217/5000000000 : ℝ)|^5263 ≤ (35793598719709/100000000000000 : ℝ)^4239
        have hw : |(2185695217/5000000000 : ℝ)|=(2185695217/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2185694887/5000000000 : ℝ)|^5263 ≤ (17896796005031/50000000000000 : ℝ)^4239
        have hw : |(2185694887/5000000000 : ℝ)|=(2185694887/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1705_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2141/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (997/10000 : ℝ)*pair X i i ≤ pair X i h) :
    -(66701/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11657/20000 : ℝ) ∧ (40659/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (5647/6250 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2141/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (997/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2141/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (997/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2141/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (997/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2141/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (997/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2141/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (997/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2141/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (997/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (997/10000 : ℝ) ^ (5255/1024 : ℝ) ≤ (726888551937239/100000000000000000000 : ℝ) := by
    have hpowers : (997/10000 : ℝ)^5255 ≤ (726888551937239/100000000000000000000 : ℝ)^1024 := by
      have hnat : (997 : ℕ)^5255*100000000000000000000^1024 ≤ 726888551937239^1024*10000^5255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        997 10000 726888551937239 100000000000000000000 5255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (997/10000 : ℝ)) (X := (726888551937239/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2141/12500 : ℝ) ^ (5255/1024 : ℝ) ≤ (1460219967450237/12500000000000000000 : ℝ) := by
    have hpowers : (2141/12500 : ℝ)^5255 ≤ (1460219967450237/12500000000000000000 : ℝ)^1024 := by
      have hnat : (2141 : ℕ)^5255*12500000000000000000^1024 ≤ 1460219967450237^1024*12500^5255 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2141 12500 1460219967450237 12500000000000000000 5255 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2141/12500 : ℝ)) (X := (1460219967450237/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000726888551937239/50000000000000000000 : ℝ) ≤ (2500007082107717/2500000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (50000726888551937239/50000000000000000000 : ℝ)^1024 ≤ (2500007082107717/2500000000000000 : ℝ)^5255 := by
      have hnat : (50000726888551937239 : ℕ)^1024*2500000000000000^5255 ≤ 2500007082107717^5255*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000726888551937239 50000000000000000000 2500007082107717 2500000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500007082107717/2500000000000000 : ℝ)) (X := (50000726888551937239/50000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20002481729658307827/20000000000000000000 : ℝ) ≤ (2500060446342377/2500000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (20002481729658307827/20000000000000000000 : ℝ)^1024 ≤ (2500060446342377/2500000000000000 : ℝ)^5255 := by
      have hnat : (20002481729658307827 : ℕ)^1024*2500000000000000^5255 ≤ 2500060446342377^5255*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20002481729658307827 20000000000000000000 2500060446342377 2500000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500060446342377/2500000000000000 : ℝ)) (X := (20002481729658307827/20000000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (6251460219967450237/6250000000000000000 : ℝ) ≤ (2500113810577037/2500000000000000 : ℝ) ^ (5255/1024 : ℝ) := by
    have hpowers : (6251460219967450237/6250000000000000000 : ℝ)^1024 ≤ (2500113810577037/2500000000000000 : ℝ)^5255 := by
      have hnat : (6251460219967450237 : ℕ)^1024*2500000000000000^5255 ≤ 2500113810577037^5255*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251460219967450237 6250000000000000000 2500113810577037 2500000000000000 1024 5255 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500113810577037/2500000000000000 : ℝ)) (X := (6251460219967450237/6250000000000000000 : ℝ)) (by norm_num) 5255 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(726888551937239/100000000000000000000 : ℝ) ≤ ((2982331101814652981/2982500000000000000 : ℝ)+2*(889403911/2982500000000 : ℝ)*(997/10000 : ℝ))^(5255/1024 : ℝ) := by
    rw [show (2982331101814652981/2982500000000000000 : ℝ)+2*(889403911/2982500000000 : ℝ)*(997/10000 : ℝ)=(2500007082107717/2500000000000000 : ℝ) by norm_num, show 1+2*(726888551937239/100000000000000000000 : ℝ)=(50000726888551937239/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1460219967450237/12500000000000000000 : ℝ)+(726888551937239/100000000000000000000 : ℝ) ≤ ((2982331101814652981/2982500000000000000 : ℝ)+(889403911/2982500000000 : ℝ)*((2141/12500 : ℝ)+(997/10000 : ℝ)))^(5255/1024 : ℝ) := by
    rw [show (2982331101814652981/2982500000000000000 : ℝ)+(889403911/2982500000000 : ℝ)*((2141/12500 : ℝ)+(997/10000 : ℝ))=(2500060446342377/2500000000000000 : ℝ) by norm_num, show 1+(1460219967450237/12500000000000000000 : ℝ)+(726888551937239/100000000000000000000 : ℝ)=(20002481729658307827/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1460219967450237/12500000000000000000 : ℝ) ≤ ((2982331101814652981/2982500000000000000 : ℝ)+2*(889403911/2982500000000 : ℝ)*(2141/12500 : ℝ))^(5255/1024 : ℝ) := by
    rw [show (2982331101814652981/2982500000000000000 : ℝ)+2*(889403911/2982500000000 : ℝ)*(2141/12500 : ℝ)=(2500113810577037/2500000000000000 : ℝ) by norm_num, show 1+2*(1460219967450237/12500000000000000000 : ℝ)=(6251460219967450237/6250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2982331101814652981/2982500000000000000 : ℝ)*(X 1 0+X 2 0)+(889403911/2982500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (997/10000 : ℝ)) (hi := (2141/12500 : ℝ)) (c := (2982331101814652981/2982500000000000000 : ℝ)) (alpha := (889403911/2982500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2982331101814652981/2982500000000000000 : ℝ)*(X 0 1+X 2 1)+(889403911/2982500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (997/10000 : ℝ)) (hi := (2141/12500 : ℝ)) (c := (2982331101814652981/2982500000000000000 : ℝ)) (alpha := (889403911/2982500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2982331101814652981/2982500000000000000 : ℝ)*(X 0 2+X 1 2)+(889403911/2982500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5255/1024 : ℝ)) (lo := (997/10000 : ℝ)) (hi := (2141/12500 : ℝ)) (c := (2982331101814652981/2982500000000000000 : ℝ)) (alpha := (889403911/2982500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-276951609/2500000000 : ℝ)*X 0 0+(338742897/625000000 : ℝ)*X 0 1+(5419886723/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5225624643/10000000000 : ℝ)*X 1 0+(-1383799223/10000000000 : ℝ)*X 1 1+(5419887227/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2612812479/5000000000 : ℝ)*X 2 0+(5419887123/10000000000 : ℝ)*X 2 1+(-345949733/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4493592193/10000000000 : ℝ)*X 0 0+(3941845077/10000000000 : ℝ)*X 0 1+(492730643/1250000000 : ℝ)*X 0 2+(4493592193/10000000000 : ℝ)*X 1 0+(3941845077/10000000000 : ℝ)*X 1 1+(492730643/1250000000 : ℝ)*X 1 2+(4493592193/10000000000 : ℝ)*X 2 0+(3941845077/10000000000 : ℝ)*X 2 1+(492730643/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-44340223/250000000 : ℝ)*X 0 0+(5177237409/10000000000 : ℝ)*X 0 1+(5177237459/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5390382361/10000000000 : ℝ)*X 1 0+(-745227869/5000000000 : ℝ)*X 1 1+(2588618771/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2695191387/5000000000 : ℝ)*X 2 0+(5177237293/10000000000 : ℝ)*X 2 1+(-149045551/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((3713384329/10000000000 : ℝ)*X 0 0+(1082778387/2500000000 : ℝ)*X 0 1+(4331114071/10000000000 : ℝ)*X 0 2+(3713384329/10000000000 : ℝ)*X 1 0+(1082778387/2500000000 : ℝ)*X 1 1+(4331114071/10000000000 : ℝ)*X 1 2+(3713384329/10000000000 : ℝ)*X 2 0+(1082778387/2500000000 : ℝ)*X 2 1+(4331114071/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-65219391/400000000 : ℝ)*X 0 0+(4998399613/10000000000 : ℝ)*X 0 1+(5462836651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1039295927/2000000000 : ℝ)*X 1 0+(-1364127453/10000000000 : ℝ)*X 1 1+(546283687/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196480011/10000000000 : ℝ)*X 2 0+(5462836441/10000000000 : ℝ)*X 2 1+(-682063767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((72292167/156250000 : ℝ)*X 0 0+(1936380399/5000000000 : ℝ)*X 0 1+(968190397/2500000000 : ℝ)*X 0 2+(72292167/156250000 : ℝ)*X 1 0+(1936380399/5000000000 : ℝ)*X 1 1+(968190397/2500000000 : ℝ)*X 1 2+(72292167/156250000 : ℝ)*X 2 0+(1936380399/5000000000 : ℝ)*X 2 1+(968190397/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-249125027/2000000000 : ℝ)*X 0 0+(2795081991/5000000000 : ℝ)*X 0 1+(5152063527/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5407505619/10000000000 : ℝ)*X 1 0+(-93816703/625000000 : ℝ)*X 1 1+(5152063467/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((1081501077/2000000000 : ℝ)*X 2 0+(5152063539/10000000000 : ℝ)*X 2 1+(-150106747/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((3629456933/10000000000 : ℝ)*X 0 0+(2185695217/5000000000 : ℝ)*X 0 1+(2185694887/5000000000 : ℝ)*X 0 2+(3629456933/10000000000 : ℝ)*X 1 0+(2185695217/5000000000 : ℝ)*X 1 1+(2185694887/5000000000 : ℝ)*X 1 2+(3629456933/10000000000 : ℝ)*X 2 0+(2185695217/5000000000 : ℝ)*X 2 1+(2185694887/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1705_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-66701/100000 : ℝ) ≤ (-99463795317253816629750768471189/149125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (55969573/100000000000000 : ℝ)*(upper0) + (70918277/100000000000000 : ℝ)*(lower2) + (1406709/25000000000000 : ℝ)*(lower3) + (28325557/100000000000000 : ℝ)*(upper5) + (1343960732852841/100000000000000 : ℝ)*(major0) + (1343960732852841/100000000000000 : ℝ)*(major1) + (1343960732852841/100000000000000 : ℝ)*(major2) + (374060951/100000000000000 : ℝ)*(sp3) + (1007457792988141/50000000000000 : ℝ)*(sp4) + (2014906707542651/100000000000000 : ℝ)*(sp5) + (16119311114957/800000000000 : ℝ)*(sp6) + (173809565593821/25000000000000 : ℝ)*(sp7) + (277451051/3125000000000 : ℝ)*(sp13) + (1696606657/100000000000000 : ℝ)*(sp14) + (139047727287247/20000000000000 : ℝ)*(f.failure) + (1007457792988141/50000000000000 : ℝ)*(f.sum) + (7148059954181/1193000000000000000000000000 : ℝ)*base65 + (403409850700719021/298250000000000000000000000000000 : ℝ)*base67 + (2224950445861469021/298250000000000000000000000000000 : ℝ)*base69 + (712436219402469021/298250000000000000000000000000000 : ℝ)*base71 + (5273247444997/1193000000000000000000000000 : ℝ)*base74 + (829504743920469021/298250000000000000000000000000000 : ℝ)*base75 + (4378217879935469021/298250000000000000000000000000000 : ℝ)*base77 + (2369273751793219021/298250000000000000000000000000000 : ℝ)*base79 + (162255307677/149125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (2212031/200000000000000000000 : ℝ)*base90 + (2212031/200000000000000000000 : ℝ)*base92 + (2212031/200000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (11657/20000 : ℝ) ≤ (86921406920569092243713094594699/149125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30533869/100000000000000 : ℝ)*(lower1) + (27596599/100000000000000 : ℝ)*(lower3) + (5033019/6250000000000 : ℝ)*(upper4) + (1447323301902969/100000000000000 : ℝ)*(major0) + (1447323301902969/100000000000000 : ℝ)*(major1) + (1447323301902969/100000000000000 : ℝ)*(major2) + (1063253900706979/50000000000000 : ℝ)*(sp0) + (2126503411385161/100000000000000 : ℝ)*(sp1) + (2126502589376937/100000000000000 : ℝ)*(sp2) + (374354271784387/50000000000000 : ℝ)*(sp3) + (82777923/1562500000000 : ℝ)*(sp5) + (191243603/3125000000000 : ℝ)*(sp6) + (145829809/100000000000000 : ℝ)*(sp7) + (36310331/4000000000000 : ℝ)*(sp12) + (93588586174823/12500000000000 : ℝ)*(f.failure) + (2126508709172233/100000000000000 : ℝ)*(f.sum) + (3029427399591/596500000000000000000000000 : ℝ)*base65 + (791850316470600589/298250000000000000000000000000000 : ℝ)*base67 + (15283531121272100589/298250000000000000000000000000000 : ℝ)*base69 + (2472049487129100589/298250000000000000000000000000000 : ℝ)*base71 + (1614858027109/1193000000000000000000000000 : ℝ)*base73 + (1083586157693100589/298250000000000000000000000000000 : ℝ)*base75 + (1788262080790350589/298250000000000000000000000000000 : ℝ)*base77 + (1125083934068350589/298250000000000000000000000000000 : ℝ)*base79 + (19465794858429/1193000000000000000000000000 : ℝ)*base81 + (1400921/125000000000000000000 : ℝ)*base89 + (1400921/125000000000000000000 : ℝ)*base91 + (1400921/125000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (40659/50000 : ℝ) ≤ (242537349351972677033269797/298250000000000000000000000 : ℝ) := by norm_num
    linear_combination (8697781/50000000000000 : ℝ)*(upper0) + (9314997/100000000000000 : ℝ)*(lower1) + (70295593/100000000000000 : ℝ)*(lower3) + (430223/100000000000000 : ℝ)*(upper4) + (367616915882767/25000000000000 : ℝ)*(major0) + (367616915882767/25000000000000 : ℝ)*(major1) + (367616915882767/25000000000000 : ℝ)*(major2) + (2453092343/100000000000000 : ℝ)*(sp0) + (5526031227/20000000000000 : ℝ)*(sp1) + (4110242341/50000000000000 : ℝ)*(sp3) + (269143094495257/12500000000000 : ℝ)*(sp8) + (269139947362283/12500000000000 : ℝ)*(sp9) + (2153147209054399/100000000000000 : ℝ)*(sp10) + (380336590317717/50000000000000 : ℝ)*(sp11) + (190170350280029/25000000000000 : ℝ)*(f.failure) + (2153147209054399/100000000000000 : ℝ)*(f.sum) + (23205000237/596500000000000000000000000 : ℝ)*base65 + (125557153955703427/74562500000000000000000000000000 : ℝ)*base67 + (11822802052265927/74562500000000000000000000000000 : ℝ)*base69 + (173533370689859073/74562500000000000000000000000000 : ℝ)*base72 + (3151332108173/1193000000000000000000000000 : ℝ)*base74 + (290716013187265927/74562500000000000000000000000000 : ℝ)*base75 + (99614340889359073/74562500000000000000000000000000 : ℝ)*base78 + (309445458902734073/74562500000000000000000000000000 : ℝ)*base80 + (754937477061/596500000000000000000000000 : ℝ)*base81 + (156883/250000000000000000000 : ℝ)*base89 + (156883/250000000000000000000 : ℝ)*base91 + (156883/250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (-5647/6250 : ℝ) ≤ (-13473301626075066997685444277147/14912500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (11425789/25000000000000 : ℝ)*(upper1) + (60000253/100000000000000 : ℝ)*(upper3) + (12076749/25000000000000 : ℝ)*(lower4) + (151917118515957/10000000000000 : ℝ)*(major0) + (151917118515957/10000000000000 : ℝ)*(major1) + (151917118515957/10000000000000 : ℝ)*(major2) + (330565593/50000000000000 : ℝ)*(sp4) + (1178073849/10000000000000 : ℝ)*(sp5) + (4399744673/50000000000000 : ℝ)*(sp6) + (7647990607/100000000000000 : ℝ)*(sp7) + (1141291022242757/50000000000000 : ℝ)*(sp12) + (228257092487821/10000000000000 : ℝ)*(sp13) + (1141286953063677/50000000000000 : ℝ)*(sp14) + (785868365694391/100000000000000 : ℝ)*(sp15) + (392938006842499/50000000000000 : ℝ)*(f.failure) + (22825827056167/1000000000000 : ℝ)*(f.sum) + (573767165017/298250000000000000000000000 : ℝ)*base66 + (27168941265282183/29825000000000000000000000000000 : ℝ)*base68 + (505068034224857183/29825000000000000000000000000000 : ℝ)*base70 + (276673087544332183/29825000000000000000000000000000 : ℝ)*base72 + (267271381357/119300000000000000000000000 : ℝ)*base73 + (220125990920207183/29825000000000000000000000000000 : ℝ)*base76 + (229259993176882183/29825000000000000000000000000000 : ℝ)*base78 + (33194556461932183/29825000000000000000000000000000 : ℝ)*base80 + (12311414217803/1193000000000000000000000000 : ℝ)*base82 + (1333427/500000000000000000000 : ℝ)*base90 + (1333427/500000000000000000000 : ℝ)*base92 + (1333427/500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1705_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2141/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (997/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66701/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11657/20000 : ℝ) else (40659/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5647/6250 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1705_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1705_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4979/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66701/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11657/20000 : ℝ) else (40659/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5647/6250 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1705_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1705_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1705_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5255/1024 : ℝ) ≤ p) (hpb : p ≤ (5263/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19330927/10000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8571/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4979/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(66701/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(11657/20000 : ℝ) else (40659/50000 : ℝ) ≤ X j i ∧ X j i ≤ (5647/6250 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1705_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
