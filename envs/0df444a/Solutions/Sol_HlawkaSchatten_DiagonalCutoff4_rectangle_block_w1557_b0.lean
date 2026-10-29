-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1557_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:23:51.728068+00:00
-- url     : https://prove2.me/submissions/e5f7e4c5-9a49-49e0-b731-77a1d84912dd

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
theorem support_rectangle_w1557_s0_0 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1639129343/10000000000 : ℝ)*x 0 + (2939505851/5000000000 : ℝ)*x 1 + (974819739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1639129343/10000000000 : ℝ)^4611 ≤ (9781482404463/100000000000000 : ℝ)^3587 := by
    have hnat : (1639129343 : ℕ)^4611*100000000000000^3587 ≤ 9781482404463^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1639129343 10000000000 9781482404463 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2939505851/5000000000 : ℝ)^4611 ≤ (2020721175211/4000000000000 : ℝ)^3587 := by
    have hnat : (2939505851 : ℕ)^4611*4000000000000^3587 ≤ 2020721175211^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2939505851 5000000000 2020721175211 4000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974819739/2000000000 : ℝ)^4611 ≤ (39700488201473/100000000000000 : ℝ)^3587 := by
    have hnat : (974819739 : ℕ)^4611*100000000000000^3587 ≤ 39700488201473^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974819739 2000000000 39700488201473 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1639129343/10000000000 : ℝ), (2939505851/5000000000 : ℝ), (974819739/2000000000 : ℝ)] ![(9781482404463/100000000000000 : ℝ), (2020721175211/4000000000000 : ℝ), (39700488201473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1639129343/10000000000 : ℝ)|^4611 ≤ (9781482404463/100000000000000 : ℝ)^3587
        have hw : |(-1639129343/10000000000 : ℝ)|=(1639129343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2939505851/5000000000 : ℝ)|^4611 ≤ (2020721175211/4000000000000 : ℝ)^3587
        have hw : |(2939505851/5000000000 : ℝ)|=(2939505851/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(974819739/2000000000 : ℝ)|^4611 ≤ (39700488201473/100000000000000 : ℝ)^3587
        have hw : |(974819739/2000000000 : ℝ)|=(974819739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s0_1 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1367064607/2500000000 : ℝ)*x 0 + (-549806871/2500000000 : ℝ)*x 1 + (974819739/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1367064607/2500000000 : ℝ)^4611 ≤ (11506716307533/25000000000000 : ℝ)^3587 := by
    have hnat : (1367064607 : ℕ)^4611*25000000000000^3587 ≤ 11506716307533^3587*2500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1367064607 2500000000 11506716307533 25000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (549806871/2500000000 : ℝ)^4611 ≤ (570905862199/4000000000000 : ℝ)^3587 := by
    have hnat : (549806871 : ℕ)^4611*4000000000000^3587 ≤ 570905862199^3587*2500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549806871 2500000000 570905862199 4000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (974819739/2000000000 : ℝ)^4611 ≤ (39700488201473/100000000000000 : ℝ)^3587 := by
    have hnat : (974819739 : ℕ)^4611*100000000000000^3587 ≤ 39700488201473^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      974819739 2000000000 39700488201473 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1367064607/2500000000 : ℝ), (-549806871/2500000000 : ℝ), (974819739/2000000000 : ℝ)] ![(11506716307533/25000000000000 : ℝ), (570905862199/4000000000000 : ℝ), (39700488201473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1367064607/2500000000 : ℝ)|^4611 ≤ (11506716307533/25000000000000 : ℝ)^3587
        have hw : |(1367064607/2500000000 : ℝ)|=(1367064607/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-549806871/2500000000 : ℝ)|^4611 ≤ (570905862199/4000000000000 : ℝ)^3587
        have hw : |(-549806871/2500000000 : ℝ)|=(549806871/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(974819739/2000000000 : ℝ)|^4611 ≤ (39700488201473/100000000000000 : ℝ)^3587
        have hw : |(974819739/2000000000 : ℝ)|=(974819739/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s0_2 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5468258469/10000000000 : ℝ)*x 0 + (609262331/1250000000 : ℝ)*x 1 + (-219922749/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5468258469/10000000000 : ℝ)^4611 ≤ (46026865673751/100000000000000 : ℝ)^3587 := by
    have hnat : (5468258469 : ℕ)^4611*100000000000000^3587 ≤ 46026865673751^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5468258469 10000000000 46026865673751 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (609262331/1250000000 : ℝ)^4611 ≤ (19850243854681/50000000000000 : ℝ)^3587 := by
    have hnat : (609262331 : ℕ)^4611*50000000000000^3587 ≤ 19850243854681^3587*1250000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      609262331 1250000000 19850243854681 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (219922749/1000000000 : ℝ)^4611 ≤ (14272646605031/100000000000000 : ℝ)^3587 := by
    have hnat : (219922749 : ℕ)^4611*100000000000000^3587 ≤ 14272646605031^3587*1000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219922749 1000000000 14272646605031 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5468258469/10000000000 : ℝ), (609262331/1250000000 : ℝ), (-219922749/1000000000 : ℝ)] ![(46026865673751/100000000000000 : ℝ), (19850243854681/50000000000000 : ℝ), (14272646605031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5468258469/10000000000 : ℝ)|^4611 ≤ (46026865673751/100000000000000 : ℝ)^3587
        have hw : |(5468258469/10000000000 : ℝ)|=(5468258469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(609262331/1250000000 : ℝ)|^4611 ≤ (19850243854681/50000000000000 : ℝ)^3587
        have hw : |(609262331/1250000000 : ℝ)|=(609262331/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-219922749/1000000000 : ℝ)|^4611 ≤ (14272646605031/100000000000000 : ℝ)^3587
        have hw : |(-219922749/1000000000 : ℝ)|=(219922749/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s0_3 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1033305207/2500000000 : ℝ)*x 0 + (309250033/1000000000 : ℝ)*x 1 + (2721833147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1033305207/2500000000 : ℝ)^4611 ≤ (32117998554873/100000000000000 : ℝ)^3587 := by
    have hnat : (1033305207 : ℕ)^4611*100000000000000^3587 ≤ 32117998554873^3587*2500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1033305207 2500000000 32117998554873 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (309250033/1000000000 : ℝ)^4611 ≤ (22121051400927/100000000000000 : ℝ)^3587 := by
    have hnat : (309250033 : ℕ)^4611*100000000000000^3587 ≤ 22121051400927^3587*1000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      309250033 1000000000 22121051400927 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2721833147/5000000000 : ℝ)^4611 ≤ (9152190007097/20000000000000 : ℝ)^3587 := by
    have hnat : (2721833147 : ℕ)^4611*20000000000000^3587 ≤ 9152190007097^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2721833147 5000000000 9152190007097 20000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1033305207/2500000000 : ℝ), (309250033/1000000000 : ℝ), (2721833147/5000000000 : ℝ)] ![(32117998554873/100000000000000 : ℝ), (22121051400927/100000000000000 : ℝ), (9152190007097/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1033305207/2500000000 : ℝ)|^4611 ≤ (32117998554873/100000000000000 : ℝ)^3587
        have hw : |(1033305207/2500000000 : ℝ)|=(1033305207/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(309250033/1000000000 : ℝ)|^4611 ≤ (22121051400927/100000000000000 : ℝ)^3587
        have hw : |(309250033/1000000000 : ℝ)|=(309250033/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2721833147/5000000000 : ℝ)|^4611 ≤ (9152190007097/20000000000000 : ℝ)^3587
        have hw : |(2721833147/5000000000 : ℝ)|=(2721833147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s0_4 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1642283143/10000000000 : ℝ)*x 0 + (4899497121/10000000000 : ℝ)*x 1 + (5852711207/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1642283143/10000000000 : ℝ)^4611 ≤ (9805682024661/100000000000000 : ℝ)^3587 := by
    have hnat : (1642283143 : ℕ)^4611*100000000000000^3587 ≤ 9805682024661^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1642283143 10000000000 9805682024661 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4899497121/10000000000 : ℝ)^4611 ≤ (3996661865977/10000000000000 : ℝ)^3587 := by
    have hnat : (4899497121 : ℕ)^4611*10000000000000^3587 ≤ 3996661865977^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4899497121 10000000000 3996661865977 10000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5852711207/10000000000 : ℝ)^4611 ≤ (50227699296917/100000000000000 : ℝ)^3587 := by
    have hnat : (5852711207 : ℕ)^4611*100000000000000^3587 ≤ 50227699296917^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5852711207 10000000000 50227699296917 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1642283143/10000000000 : ℝ), (4899497121/10000000000 : ℝ), (5852711207/10000000000 : ℝ)] ![(9805682024661/100000000000000 : ℝ), (3996661865977/10000000000000 : ℝ), (50227699296917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1642283143/10000000000 : ℝ)|^4611 ≤ (9805682024661/100000000000000 : ℝ)^3587
        have hw : |(-1642283143/10000000000 : ℝ)|=(1642283143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4899497121/10000000000 : ℝ)|^4611 ≤ (3996661865977/10000000000000 : ℝ)^3587
        have hw : |(4899497121/10000000000 : ℝ)|=(4899497121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5852711207/10000000000 : ℝ)|^4611 ≤ (50227699296917/100000000000000 : ℝ)^3587
        have hw : |(5852711207/10000000000 : ℝ)|=(5852711207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s0_5 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1038712539/2000000000 : ℝ)*x 0 + (-610307639/5000000000 : ℝ)*x 1 + (5852711133/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1038712539/2000000000 : ℝ)^4611 ≤ (21538118831571/50000000000000 : ℝ)^3587 := by
    have hnat : (1038712539 : ℕ)^4611*50000000000000^3587 ≤ 21538118831571^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1038712539 2000000000 21538118831571 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (610307639/5000000000 : ℝ)^4611 ≤ (3348031921353/50000000000000 : ℝ)^3587 := by
    have hnat : (610307639 : ℕ)^4611*50000000000000^3587 ≤ 3348031921353^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      610307639 5000000000 3348031921353 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5852711133/10000000000 : ℝ)^4611 ≤ (25113849240279/50000000000000 : ℝ)^3587 := by
    have hnat : (5852711133 : ℕ)^4611*50000000000000^3587 ≤ 25113849240279^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5852711133 10000000000 25113849240279 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1038712539/2000000000 : ℝ), (-610307639/5000000000 : ℝ), (5852711133/10000000000 : ℝ)] ![(21538118831571/50000000000000 : ℝ), (3348031921353/50000000000000 : ℝ), (25113849240279/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1038712539/2000000000 : ℝ)|^4611 ≤ (21538118831571/50000000000000 : ℝ)^3587
        have hw : |(1038712539/2000000000 : ℝ)|=(1038712539/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-610307639/5000000000 : ℝ)|^4611 ≤ (3348031921353/50000000000000 : ℝ)^3587
        have hw : |(-610307639/5000000000 : ℝ)|=(610307639/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5852711133/10000000000 : ℝ)|^4611 ≤ (25113849240279/50000000000000 : ℝ)^3587
        have hw : |(5852711133/10000000000 : ℝ)|=(5852711133/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s0_6 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1298390667/2500000000 : ℝ)*x 0 + (1170542279/2000000000 : ℝ)*x 1 + (-1220614909/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1298390667/2500000000 : ℝ)^4611 ≤ (43076237375269/100000000000000 : ℝ)^3587 := by
    have hnat : (1298390667 : ℕ)^4611*100000000000000^3587 ≤ 43076237375269^3587*2500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1298390667 2500000000 43076237375269 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1170542279/2000000000 : ℝ)^4611 ≤ (50227701370913/100000000000000 : ℝ)^3587 := by
    have hnat : (1170542279 : ℕ)^4611*100000000000000^3587 ≤ 50227701370913^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1170542279 2000000000 50227701370913 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1220614909/10000000000 : ℝ)^4611 ≤ (1339212248113/20000000000000 : ℝ)^3587 := by
    have hnat : (1220614909 : ℕ)^4611*20000000000000^3587 ≤ 1339212248113^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1220614909 10000000000 1339212248113 20000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1298390667/2500000000 : ℝ), (1170542279/2000000000 : ℝ), (-1220614909/10000000000 : ℝ)] ![(43076237375269/100000000000000 : ℝ), (50227701370913/100000000000000 : ℝ), (1339212248113/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1298390667/2500000000 : ℝ)|^4611 ≤ (43076237375269/100000000000000 : ℝ)^3587
        have hw : |(1298390667/2500000000 : ℝ)|=(1298390667/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1170542279/2000000000 : ℝ)|^4611 ≤ (50227701370913/100000000000000 : ℝ)^3587
        have hw : |(1170542279/2000000000 : ℝ)|=(1170542279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1220614909/10000000000 : ℝ)|^4611 ≤ (1339212248113/20000000000000 : ℝ)^3587
        have hw : |(-1220614909/10000000000 : ℝ)|=(1220614909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s0_7 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (517574857/1250000000 : ℝ)*x 0 + (1076848459/2000000000 : ℝ)*x 1 + (3154034633/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (517574857/1250000000 : ℝ)^4611 ≤ (804792917947/2500000000000 : ℝ)^3587 := by
    have hnat : (517574857 : ℕ)^4611*2500000000000^3587 ≤ 804792917947^3587*1250000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      517574857 1250000000 804792917947 2500000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1076848459/2000000000 : ℝ)^4611 ≤ (45119814033809/100000000000000 : ℝ)^3587 := by
    have hnat : (1076848459 : ℕ)^4611*100000000000000^3587 ≤ 45119814033809^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1076848459 2000000000 45119814033809 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3154034633/10000000000 : ℝ)^4611 ≤ (907538769753/4000000000000 : ℝ)^3587 := by
    have hnat : (3154034633 : ℕ)^4611*4000000000000^3587 ≤ 907538769753^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3154034633 10000000000 907538769753 4000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(517574857/1250000000 : ℝ), (1076848459/2000000000 : ℝ), (3154034633/10000000000 : ℝ)] ![(804792917947/2500000000000 : ℝ), (45119814033809/100000000000000 : ℝ), (907538769753/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(517574857/1250000000 : ℝ)|^4611 ≤ (804792917947/2500000000000 : ℝ)^3587
        have hw : |(517574857/1250000000 : ℝ)|=(517574857/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1076848459/2000000000 : ℝ)|^4611 ≤ (45119814033809/100000000000000 : ℝ)^3587
        have hw : |(1076848459/2000000000 : ℝ)|=(1076848459/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3154034633/10000000000 : ℝ)|^4611 ≤ (907538769753/4000000000000 : ℝ)^3587
        have hw : |(3154034633/10000000000 : ℝ)|=(3154034633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1557_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3389/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (12457/50000 : ℝ)*pair X 0 0 := by
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
  have base39 : ((-1 : ℝ)*N 0+(-1 : ℝ)*N 1+(1 : ℝ)*P 2) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 2, f.sum]
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
  have hpowlo : (0 : ℝ) ^ (4609/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4609 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4609*1^1024 ≤ 0^1024*1^4609 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4609 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4609/1024 : ℝ) ≤ (808819013576769727/50000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4609 ≤ (808819013576769727/50000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4609*50000000000000000000^1024 ≤ 808819013576769727^1024*5^4609 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 808819013576769727 50000000000000000000 4609 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (808819013576769727/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4609 := by
      have hnat : (1 : ℕ)^1024*1^4609 ≤ 1^4609*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50808819013576769727/50000000000000000000 : ℝ) ≤ (10035715751655161/10000000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (50808819013576769727/50000000000000000000 : ℝ)^1024 ≤ (10035715751655161/10000000000000000 : ℝ)^4609 := by
      have hnat : (50808819013576769727 : ℕ)^1024*10000000000000000^4609 ≤ 10035715751655161^4609*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50808819013576769727 50000000000000000000 10035715751655161 10000000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10035715751655161/10000000000000000 : ℝ)) (X := (50808819013576769727/50000000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25808819013576769727/25000000000000000000 : ℝ) ≤ (5035715751655161/5000000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (25808819013576769727/25000000000000000000 : ℝ)^1024 ≤ (5035715751655161/5000000000000000 : ℝ)^4609 := by
      have hnat : (25808819013576769727 : ℕ)^1024*5000000000000000^4609 ≤ 5035715751655161^4609*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25808819013576769727 25000000000000000000 5035715751655161 5000000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5035715751655161/5000000000000000 : ℝ)) (X := (25808819013576769727/25000000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(35715751655161/4000000000000000 : ℝ)*(0 : ℝ))^(4609/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35715751655161/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(808819013576769727/50000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(35715751655161/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4609/1024 : ℝ) := by
    rw [show (1 : ℝ)+(35715751655161/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10035715751655161/10000000000000000 : ℝ) by norm_num, show 1+(808819013576769727/50000000000000000000 : ℝ)+(0 : ℝ)=(50808819013576769727/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(808819013576769727/50000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(35715751655161/4000000000000000 : ℝ)*(2/5 : ℝ))^(4609/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(35715751655161/4000000000000000 : ℝ)*(2/5 : ℝ)=(5035715751655161/5000000000000000 : ℝ) by norm_num, show 1+2*(808819013576769727/50000000000000000000 : ℝ)=(25808819013576769727/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(35715751655161/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35715751655161/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(35715751655161/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35715751655161/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(35715751655161/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (35715751655161/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1639129343/10000000000 : ℝ)*X 0 0+(2939505851/5000000000 : ℝ)*X 0 1+(974819739/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1367064607/2500000000 : ℝ)*X 1 0+(-549806871/2500000000 : ℝ)*X 1 1+(974819739/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5468258469/10000000000 : ℝ)*X 2 0+(609262331/1250000000 : ℝ)*X 2 1+(-219922749/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1033305207/2500000000 : ℝ)*X 0 0+(309250033/1000000000 : ℝ)*X 0 1+(2721833147/5000000000 : ℝ)*X 0 2+(1033305207/2500000000 : ℝ)*X 1 0+(309250033/1000000000 : ℝ)*X 1 1+(2721833147/5000000000 : ℝ)*X 1 2+(1033305207/2500000000 : ℝ)*X 2 0+(309250033/1000000000 : ℝ)*X 2 1+(2721833147/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1642283143/10000000000 : ℝ)*X 0 0+(4899497121/10000000000 : ℝ)*X 0 1+(5852711207/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1038712539/2000000000 : ℝ)*X 1 0+(-610307639/5000000000 : ℝ)*X 1 1+(5852711133/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1298390667/2500000000 : ℝ)*X 2 0+(1170542279/2000000000 : ℝ)*X 2 1+(-1220614909/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((517574857/1250000000 : ℝ)*X 0 0+(1076848459/2000000000 : ℝ)*X 0 1+(3154034633/10000000000 : ℝ)*X 0 2+(517574857/1250000000 : ℝ)*X 1 0+(1076848459/2000000000 : ℝ)*X 1 1+(3154034633/10000000000 : ℝ)*X 1 2+(517574857/1250000000 : ℝ)*X 2 0+(1076848459/2000000000 : ℝ)*X 2 1+(3154034633/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (48739778438711845247793/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18904601/50000000000000 : ℝ)*(base1) + (202755613/25000000000000 : ℝ)*(base19) + (818483649/100000000000000 : ℝ)*(base23) + (52255879/50000000000000 : ℝ)*(upper3) + (52415303/50000000000000 : ℝ)*(upper5) + (88777520982929/12500000000000 : ℝ)*(major0) + (88777520982929/12500000000000 : ℝ)*(major1) + (88777520982929/12500000000000 : ℝ)*(major2) + (995113838860857/100000000000000 : ℝ)*(sp0) + (995115981834073/100000000000000 : ℝ)*(sp1) + (248778993593219/25000000000000 : ℝ)*(sp2) + (425322098080313/100000000000000 : ℝ)*(sp3) + (299180487/10000000000000 : ℝ)*(sp4) + (638504039/50000000000000 : ℝ)*(sp7) + (425323412897593/100000000000000 : ℝ)*(f.failure) + (39804671714261/4000000000000 : ℝ)*(f.sum) + (8880238528431/25000000000000000000000000000 : ℝ)*base66 + (99099866546569/50000000000000000000000000000 : ℝ)*base67 + (246224620696569/50000000000000000000000000000 : ℝ)*base69 + (138952616946569/50000000000000000000000000000 : ℝ)*base71 + (35010623453431/25000000000000000000000000000 : ℝ)*base74 + (60255869196569/50000000000000000000000000000 : ℝ)*base75 + (60399136946569/50000000000000000000000000000 : ℝ)*base77 + (111702678346569/50000000000000000000000000000 : ℝ)*base79 + (81682521846569/25000000000000000000000000000 : ℝ)*base81 + (15612053/5000000000000000000000 : ℝ)*base90 + (15612053/5000000000000000000000 : ℝ)*base92 + (15612053/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (72283303796838674013969/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (507519999/100000000000000 : ℝ)*(base19) + (626548323/100000000000000 : ℝ)*(base23) + (14942509/12500000000000 : ℝ)*(base39) + (4026111/6250000000000 : ℝ)*(upper3) + (129353919/100000000000000 : ℝ)*(upper5) + (14974703346983/2000000000000 : ℝ)*(major0) + (14974703346983/2000000000000 : ℝ)*(major1) + (374367523904539/50000000000000 : ℝ)*(major2) + (706624093/50000000000000 : ℝ)*(sp1) + (1545543453/100000000000000 : ℝ)*(sp2) + (524540780529219/50000000000000 : ℝ)*(sp4) + (1049079640290253/100000000000000 : ℝ)*(sp5) + (524539754253367/50000000000000 : ℝ)*(sp6) + (224194278861021/50000000000000 : ℝ)*(sp7) + (224194278861021/50000000000000 : ℝ)*(f.failure) + (1049081680598511/100000000000000 : ℝ)*(f.sum) + (34533295153677/100000000000000000000000000000 : ℝ)*base65 + (847237933075779/200000000000000000000000000000 : ℝ)*base67 + (1688783713263/8000000000000000000000000000 : ℝ)*base69 + (469161131675779/200000000000000000000000000000 : ℝ)*base71 + (159166923753677/100000000000000000000000000000 : ℝ)*base73 + (55179269689263/8000000000000000000000000000 : ℝ)*base75 + (30849195961263/8000000000000000000000000000 : ℝ)*base77 + (76258730817263/8000000000000000000000000000 : ℝ)*base79 + (4475495910737/4000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (12953641/2500000000000000000000 : ℝ)*base90 + (12953641/2500000000000000000000 : ℝ)*base92 + (12953641/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1557_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3389/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (12457/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1557_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1557_s1_0 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1781041967/10000000000 : ℝ)*x 0 + (2771170513/5000000000 : ℝ)*x 1 + (5119361717/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1781041967/10000000000 : ℝ)^4611 ≤ (10883287734637/100000000000000 : ℝ)^3587 := by
    have hnat : (1781041967 : ℕ)^4611*100000000000000^3587 ≤ 10883287734637^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1781041967 10000000000 10883287734637 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2771170513/5000000000 : ℝ)^4611 ≤ (11707495476371/25000000000000 : ℝ)^3587 := by
    have hnat : (2771170513 : ℕ)^4611*25000000000000^3587 ≤ 11707495476371^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2771170513 5000000000 11707495476371 25000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5119361717/10000000000 : ℝ)^4611 ≤ (8457346069811/20000000000000 : ℝ)^3587 := by
    have hnat : (5119361717 : ℕ)^4611*20000000000000^3587 ≤ 8457346069811^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5119361717 10000000000 8457346069811 20000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1781041967/10000000000 : ℝ), (2771170513/5000000000 : ℝ), (5119361717/10000000000 : ℝ)] ![(10883287734637/100000000000000 : ℝ), (11707495476371/25000000000000 : ℝ), (8457346069811/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1781041967/10000000000 : ℝ)|^4611 ≤ (10883287734637/100000000000000 : ℝ)^3587
        have hw : |(-1781041967/10000000000 : ℝ)|=(1781041967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2771170513/5000000000 : ℝ)|^4611 ≤ (11707495476371/25000000000000 : ℝ)^3587
        have hw : |(2771170513/5000000000 : ℝ)|=(2771170513/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5119361717/10000000000 : ℝ)|^4611 ≤ (8457346069811/20000000000000 : ℝ)^3587
        have hw : |(5119361717/10000000000 : ℝ)|=(5119361717/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s1_1 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689326323/5000000000 : ℝ)*x 0 + (-2002598529/10000000000 : ℝ)*x 1 + (2559680821/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689326323/5000000000 : ℝ)^4611 ≤ (22529804929167/50000000000000 : ℝ)^3587 := by
    have hnat : (2689326323 : ℕ)^4611*50000000000000^3587 ≤ 22529804929167^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689326323 5000000000 22529804929167 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002598529/10000000000 : ℝ)^4611 ≤ (12653660573283/100000000000000 : ℝ)^3587 := by
    have hnat : (2002598529 : ℕ)^4611*100000000000000^3587 ≤ 12653660573283^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002598529 10000000000 12653660573283 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2559680821/5000000000 : ℝ)^4611 ≤ (2642920597043/6250000000000 : ℝ)^3587 := by
    have hnat : (2559680821 : ℕ)^4611*6250000000000^3587 ≤ 2642920597043^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2559680821 5000000000 2642920597043 6250000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689326323/5000000000 : ℝ), (-2002598529/10000000000 : ℝ), (2559680821/5000000000 : ℝ)] ![(22529804929167/50000000000000 : ℝ), (12653660573283/100000000000000 : ℝ), (2642920597043/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689326323/5000000000 : ℝ)|^4611 ≤ (22529804929167/50000000000000 : ℝ)^3587
        have hw : |(2689326323/5000000000 : ℝ)|=(2689326323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2002598529/10000000000 : ℝ)|^4611 ≤ (12653660573283/100000000000000 : ℝ)^3587
        have hw : |(-2002598529/10000000000 : ℝ)|=(2002598529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2559680821/5000000000 : ℝ)|^4611 ≤ (2642920597043/6250000000000 : ℝ)^3587
        have hw : |(2559680821/5000000000 : ℝ)|=(2559680821/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s1_2 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2689326311/5000000000 : ℝ)*x 0 + (5119361471/10000000000 : ℝ)*x 1 + (-15645303/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2689326311/5000000000 : ℝ)^4611 ≤ (45059609599877/100000000000000 : ℝ)^3587 := by
    have hnat : (2689326311 : ℕ)^4611*100000000000000^3587 ≤ 45059609599877^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2689326311 5000000000 45059609599877 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5119361471/10000000000 : ℝ)^4611 ≤ (42286727736971/100000000000000 : ℝ)^3587 := by
    have hnat : (5119361471 : ℕ)^4611*100000000000000^3587 ≤ 42286727736971^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5119361471 10000000000 42286727736971 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (15645303/78125000 : ℝ)^4611 ≤ (12653662644503/100000000000000 : ℝ)^3587 := by
    have hnat : (15645303 : ℕ)^4611*100000000000000^3587 ≤ 12653662644503^3587*78125000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15645303 78125000 12653662644503 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2689326311/5000000000 : ℝ), (5119361471/10000000000 : ℝ), (-15645303/78125000 : ℝ)] ![(45059609599877/100000000000000 : ℝ), (42286727736971/100000000000000 : ℝ), (12653662644503/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2689326311/5000000000 : ℝ)|^4611 ≤ (45059609599877/100000000000000 : ℝ)^3587
        have hw : |(2689326311/5000000000 : ℝ)|=(2689326311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5119361471/10000000000 : ℝ)|^4611 ≤ (42286727736971/100000000000000 : ℝ)^3587
        have hw : |(5119361471/10000000000 : ℝ)|=(5119361471/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-15645303/78125000 : ℝ)|^4611 ≤ (12653662644503/100000000000000 : ℝ)^3587
        have hw : |(-15645303/78125000 : ℝ)|=(15645303/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s1_3 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4233195089/10000000000 : ℝ)*x 0 + (1880966003/5000000000 : ℝ)*x 1 + (9503129/20000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4233195089/10000000000 : ℝ)^4611 ≤ (33120073324403/100000000000000 : ℝ)^3587 := by
    have hnat : (4233195089 : ℕ)^4611*100000000000000^3587 ≤ 33120073324403^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4233195089 10000000000 33120073324403 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1880966003/5000000000 : ℝ)^4611 ≤ (28457794654093/100000000000000 : ℝ)^3587 := by
    have hnat : (1880966003 : ℕ)^4611*100000000000000^3587 ≤ 28457794654093^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1880966003 5000000000 28457794654093 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (9503129/20000000 : ℝ)^4611 ≤ (38422132005109/100000000000000 : ℝ)^3587 := by
    have hnat : (9503129 : ℕ)^4611*100000000000000^3587 ≤ 38422132005109^3587*20000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9503129 20000000 38422132005109 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4233195089/10000000000 : ℝ), (1880966003/5000000000 : ℝ), (9503129/20000000 : ℝ)] ![(33120073324403/100000000000000 : ℝ), (28457794654093/100000000000000 : ℝ), (38422132005109/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4233195089/10000000000 : ℝ)|^4611 ≤ (33120073324403/100000000000000 : ℝ)^3587
        have hw : |(4233195089/10000000000 : ℝ)|=(4233195089/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1880966003/5000000000 : ℝ)|^4611 ≤ (28457794654093/100000000000000 : ℝ)^3587
        have hw : |(1880966003/5000000000 : ℝ)|=(1880966003/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(9503129/20000000 : ℝ)|^4611 ≤ (38422132005109/100000000000000 : ℝ)^3587
        have hw : |(9503129/20000000 : ℝ)|=(9503129/20000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s1_4 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-111329401/625000000 : ℝ)*x 0 + (5123802899/10000000000 : ℝ)*x 1 + (2768916543/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (111329401/625000000 : ℝ)^4611 ≤ (10885082248907/100000000000000 : ℝ)^3587 := by
    have hnat : (111329401 : ℕ)^4611*100000000000000^3587 ≤ 10885082248907^3587*625000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      111329401 625000000 10885082248907 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5123802899/10000000000 : ℝ)^4611 ≤ (42333893669169/100000000000000 : ℝ)^3587 := by
    have hnat : (5123802899 : ℕ)^4611*100000000000000^3587 ≤ 42333893669169^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5123802899 10000000000 42333893669169 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2768916543/5000000000 : ℝ)^4611 ≤ (5847628009091/12500000000000 : ℝ)^3587 := by
    have hnat : (2768916543 : ℕ)^4611*12500000000000^3587 ≤ 5847628009091^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768916543 5000000000 5847628009091 12500000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-111329401/625000000 : ℝ), (5123802899/10000000000 : ℝ), (2768916543/5000000000 : ℝ)] ![(10885082248907/100000000000000 : ℝ), (42333893669169/100000000000000 : ℝ), (5847628009091/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-111329401/625000000 : ℝ)|^4611 ≤ (10885082248907/100000000000000 : ℝ)^3587
        have hw : |(-111329401/625000000 : ℝ)|=(111329401/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5123802899/10000000000 : ℝ)|^4611 ≤ (42333893669169/100000000000000 : ℝ)^3587
        have hw : |(5123802899/10000000000 : ℝ)|=(5123802899/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2768916543/5000000000 : ℝ)|^4611 ≤ (5847628009091/12500000000000 : ℝ)^3587
        have hw : |(2768916543/5000000000 : ℝ)|=(2768916543/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s1_5 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053336053/2000000000 : ℝ)*x 0 + (-1584129581/10000000000 : ℝ)*x 1 + (346114503/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053336053/2000000000 : ℝ)^4611 ≤ (43857373982139/100000000000000 : ℝ)^3587 := by
    have hnat : (1053336053 : ℕ)^4611*100000000000000^3587 ≤ 43857373982139^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053336053 2000000000 43857373982139 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1584129581/10000000000 : ℝ)^4611 ≤ (187232263863/2000000000000 : ℝ)^3587 := by
    have hnat : (1584129581 : ℕ)^4611*2000000000000^3587 ≤ 187232263863^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584129581 10000000000 187232263863 2000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (346114503/625000000 : ℝ)^4611 ≤ (11695253200247/25000000000000 : ℝ)^3587 := by
    have hnat : (346114503 : ℕ)^4611*25000000000000^3587 ≤ 11695253200247^3587*625000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      346114503 625000000 11695253200247 25000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053336053/2000000000 : ℝ), (-1584129581/10000000000 : ℝ), (346114503/625000000 : ℝ)] ![(43857373982139/100000000000000 : ℝ), (187232263863/2000000000000 : ℝ), (11695253200247/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053336053/2000000000 : ℝ)|^4611 ≤ (43857373982139/100000000000000 : ℝ)^3587
        have hw : |(1053336053/2000000000 : ℝ)|=(1053336053/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1584129581/10000000000 : ℝ)|^4611 ≤ (187232263863/2000000000000 : ℝ)^3587
        have hw : |(-1584129581/10000000000 : ℝ)|=(1584129581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(346114503/625000000 : ℝ)|^4611 ≤ (11695253200247/25000000000000 : ℝ)^3587
        have hw : |(346114503/625000000 : ℝ)|=(346114503/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s1_6 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5266682379/10000000000 : ℝ)*x 0 + (553783143/1000000000 : ℝ)*x 1 + (-1584127487/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5266682379/10000000000 : ℝ)^4611 ≤ (43857396611611/100000000000000 : ℝ)^3587 := by
    have hnat : (5266682379 : ℕ)^4611*100000000000000^3587 ≤ 43857396611611^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266682379 10000000000 43857396611611 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553783143/1000000000 : ℝ)^4611 ≤ (46781006090069/100000000000000 : ℝ)^3587 := by
    have hnat : (553783143 : ℕ)^4611*100000000000000^3587 ≤ 46781006090069^3587*1000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553783143 1000000000 46781006090069 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1584127487/10000000000 : ℝ)^4611 ≤ (9361597285709/100000000000000 : ℝ)^3587 := by
    have hnat : (1584127487 : ℕ)^4611*100000000000000^3587 ≤ 9361597285709^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1584127487 10000000000 9361597285709 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5266682379/10000000000 : ℝ), (553783143/1000000000 : ℝ), (-1584127487/10000000000 : ℝ)] ![(43857396611611/100000000000000 : ℝ), (46781006090069/100000000000000 : ℝ), (9361597285709/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5266682379/10000000000 : ℝ)|^4611 ≤ (43857396611611/100000000000000 : ℝ)^3587
        have hw : |(5266682379/10000000000 : ℝ)|=(5266682379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(553783143/1000000000 : ℝ)|^4611 ≤ (46781006090069/100000000000000 : ℝ)^3587
        have hw : |(553783143/1000000000 : ℝ)|=(553783143/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1584127487/10000000000 : ℝ)|^4611 ≤ (9361597285709/100000000000000 : ℝ)^3587
        have hw : |(-1584127487/10000000000 : ℝ)|=(1584127487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s1_7 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2116865243/5000000000 : ℝ)*x 0 + (2370585743/5000000000 : ℝ)*x 1 + (3772480103/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2116865243/5000000000 : ℝ)^4611 ≤ (8281364534037/25000000000000 : ℝ)^3587 := by
    have hnat : (2116865243 : ℕ)^4611*25000000000000^3587 ≤ 8281364534037^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2116865243 5000000000 8281364534037 25000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2370585743/5000000000 : ℝ)^4611 ≤ (3831413432993/10000000000000 : ℝ)^3587 := by
    have hnat : (2370585743 : ℕ)^4611*10000000000000^3587 ≤ 3831413432993^3587*5000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2370585743 5000000000 3831413432993 10000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3772480103/10000000000 : ℝ)^4611 ≤ (28560407521533/100000000000000 : ℝ)^3587 := by
    have hnat : (3772480103 : ℕ)^4611*100000000000000^3587 ≤ 28560407521533^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3772480103 10000000000 28560407521533 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2116865243/5000000000 : ℝ), (2370585743/5000000000 : ℝ), (3772480103/10000000000 : ℝ)] ![(8281364534037/25000000000000 : ℝ), (3831413432993/10000000000000 : ℝ), (28560407521533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2116865243/5000000000 : ℝ)|^4611 ≤ (8281364534037/25000000000000 : ℝ)^3587
        have hw : |(2116865243/5000000000 : ℝ)|=(2116865243/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2370585743/5000000000 : ℝ)|^4611 ≤ (3831413432993/10000000000000 : ℝ)^3587
        have hw : |(2370585743/5000000000 : ℝ)|=(2370585743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3772480103/10000000000 : ℝ)|^4611 ≤ (28560407521533/100000000000000 : ℝ)^3587
        have hw : |(3772480103/10000000000 : ℝ)|=(3772480103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1557_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12457/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (223/2500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4469/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (12457/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (12457/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3389/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (12457/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (12457/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3389/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (12457/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (12457/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3389/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3389/100000 : ℝ) ^ (4609/1024 : ℝ) ≤ (1512748044249/6250000000000000000 : ℝ) := by
    have hpowers : (3389/100000 : ℝ)^4609 ≤ (1512748044249/6250000000000000000 : ℝ)^1024 := by
      have hnat : (3389 : ℕ)^4609*6250000000000000000^1024 ≤ 1512748044249^1024*100000^4609 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3389 100000 1512748044249 6250000000000000000 4609 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3389/100000 : ℝ)) (X := (1512748044249/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (12457/50000 : ℝ) ^ (4609/1024 : ℝ) ≤ (48011598817002197/25000000000000000000 : ℝ) := by
    have hpowers : (12457/50000 : ℝ)^4609 ≤ (48011598817002197/25000000000000000000 : ℝ)^1024 := by
      have hnat : (12457 : ℕ)^4609*25000000000000000000^1024 ≤ 48011598817002197^1024*50000^4609 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12457 50000 48011598817002197 25000000000000000000 4609 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (12457/50000 : ℝ)) (X := (48011598817002197/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125001512748044249/3125000000000000000 : ℝ) ≤ (5000000537749171/5000000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (3125001512748044249/3125000000000000000 : ℝ)^1024 ≤ (5000000537749171/5000000000000000 : ℝ)^4609 := by
      have hnat : (3125001512748044249 : ℕ)^1024*5000000000000000^4609 ≤ 5000000537749171^4609*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125001512748044249 3125000000000000000 5000000537749171 5000000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000000537749171/5000000000000000 : ℝ)) (X := (3125001512748044249/3125000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25048017649809179193/25000000000000000000 : ℝ) ≤ (200085282509393/200000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (25048017649809179193/25000000000000000000 : ℝ)^1024 ≤ (200085282509393/200000000000000 : ℝ)^4609 := by
      have hnat : (25048017649809179193 : ℕ)^1024*200000000000000^4609 ≤ 200085282509393^4609*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25048017649809179193 25000000000000000000 200085282509393 200000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200085282509393/200000000000000 : ℝ)) (X := (25048017649809179193/25000000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12548011598817002197/12500000000000000000 : ℝ) ≤ (5004263587720479/5000000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (12548011598817002197/12500000000000000000 : ℝ)^1024 ≤ (5004263587720479/5000000000000000 : ℝ)^4609 := by
      have hnat : (12548011598817002197 : ℕ)^1024*5000000000000000^4609 ≤ 5004263587720479^4609*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12548011598817002197 12500000000000000000 5004263587720479 5000000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004263587720479/5000000000000000 : ℝ)) (X := (12548011598817002197/12500000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1512748044249/6250000000000000000 : ℝ) ≤ ((107610564098698142963/107625000000000000000 : ℝ)+2*(1065762492827/538125000000000 : ℝ)*(3389/100000 : ℝ))^(4609/1024 : ℝ) := by
    rw [show (107610564098698142963/107625000000000000000 : ℝ)+2*(1065762492827/538125000000000 : ℝ)*(3389/100000 : ℝ)=(5000000537749171/5000000000000000 : ℝ) by norm_num, show 1+2*(1512748044249/6250000000000000000 : ℝ)=(3125001512748044249/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(48011598817002197/25000000000000000000 : ℝ)+(1512748044249/6250000000000000000 : ℝ) ≤ ((107610564098698142963/107625000000000000000 : ℝ)+(1065762492827/538125000000000 : ℝ)*((12457/50000 : ℝ)+(3389/100000 : ℝ)))^(4609/1024 : ℝ) := by
    rw [show (107610564098698142963/107625000000000000000 : ℝ)+(1065762492827/538125000000000 : ℝ)*((12457/50000 : ℝ)+(3389/100000 : ℝ))=(200085282509393/200000000000000 : ℝ) by norm_num, show 1+(48011598817002197/25000000000000000000 : ℝ)+(1512748044249/6250000000000000000 : ℝ)=(25048017649809179193/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(48011598817002197/25000000000000000000 : ℝ) ≤ ((107610564098698142963/107625000000000000000 : ℝ)+2*(1065762492827/538125000000000 : ℝ)*(12457/50000 : ℝ))^(4609/1024 : ℝ) := by
    rw [show (107610564098698142963/107625000000000000000 : ℝ)+2*(1065762492827/538125000000000 : ℝ)*(12457/50000 : ℝ)=(5004263587720479/5000000000000000 : ℝ) by norm_num, show 1+2*(48011598817002197/25000000000000000000 : ℝ)=(12548011598817002197/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (107610564098698142963/107625000000000000000 : ℝ)*(X 1 0+X 2 0)+(1065762492827/538125000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (3389/100000 : ℝ)) (hi := (12457/50000 : ℝ)) (c := (107610564098698142963/107625000000000000000 : ℝ)) (alpha := (1065762492827/538125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (107610564098698142963/107625000000000000000 : ℝ)*(X 0 1+X 2 1)+(1065762492827/538125000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (3389/100000 : ℝ)) (hi := (12457/50000 : ℝ)) (c := (107610564098698142963/107625000000000000000 : ℝ)) (alpha := (1065762492827/538125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (107610564098698142963/107625000000000000000 : ℝ)*(X 0 2+X 1 2)+(1065762492827/538125000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (3389/100000 : ℝ)) (hi := (12457/50000 : ℝ)) (c := (107610564098698142963/107625000000000000000 : ℝ)) (alpha := (1065762492827/538125000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1781041967/10000000000 : ℝ)*X 0 0+(2771170513/5000000000 : ℝ)*X 0 1+(5119361717/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2689326323/5000000000 : ℝ)*X 1 0+(-2002598529/10000000000 : ℝ)*X 1 1+(2559680821/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2689326311/5000000000 : ℝ)*X 2 0+(5119361471/10000000000 : ℝ)*X 2 1+(-15645303/78125000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4233195089/10000000000 : ℝ)*X 0 0+(1880966003/5000000000 : ℝ)*X 0 1+(9503129/20000000 : ℝ)*X 0 2+(4233195089/10000000000 : ℝ)*X 1 0+(1880966003/5000000000 : ℝ)*X 1 1+(9503129/20000000 : ℝ)*X 1 2+(4233195089/10000000000 : ℝ)*X 2 0+(1880966003/5000000000 : ℝ)*X 2 1+(9503129/20000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-111329401/625000000 : ℝ)*X 0 0+(5123802899/10000000000 : ℝ)*X 0 1+(2768916543/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1053336053/2000000000 : ℝ)*X 1 0+(-1584129581/10000000000 : ℝ)*X 1 1+(346114503/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5266682379/10000000000 : ℝ)*X 2 0+(553783143/1000000000 : ℝ)*X 2 1+(-1584127487/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2116865243/5000000000 : ℝ)*X 0 0+(2370585743/5000000000 : ℝ)*X 0 1+(3772480103/10000000000 : ℝ)*X 0 2+(2116865243/5000000000 : ℝ)*X 1 0+(2370585743/5000000000 : ℝ)*X 1 1+(3772480103/10000000000 : ℝ)*X 1 2+(2116865243/5000000000 : ℝ)*X 2 0+(2370585743/5000000000 : ℝ)*X 2 1+(3772480103/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (702111616646161618162471659/64062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (109730057/100000000000000 : ℝ)*(base1) + (1813514999/100000000000000 : ℝ)*(base19) + (1802965711/100000000000000 : ℝ)*(base23) + (293661837/100000000000000 : ℝ)*(upper3) + (149858023/100000000000000 : ℝ)*(upper5) + (421837071419517/25000000000000 : ℝ)*(major0) + (421837071419517/25000000000000 : ℝ)*(major1) + (421837071419517/25000000000000 : ℝ)*(major2) + (295524533203107/12500000000000 : ℝ)*(sp0) + (591051677460599/25000000000000 : ℝ)*(sp1) + (591051680097921/25000000000000 : ℝ)*(sp2) + (202096273628631/20000000000000 : ℝ)*(sp3) + (3091865649/25000000000000 : ℝ)*(sp4) + (1240959831/20000000000000 : ℝ)*(sp7) + (1010487682672367/100000000000000 : ℝ)*(f.failure) + (472841704671479/20000000000000 : ℝ)*(f.sum) + (42475482094727/35875000000000000000000000000 : ℝ)*base66 + (3627266190999597043/896875000000000000000000000000000 : ℝ)*base68 + (3116386596971472043/896875000000000000000000000000000 : ℝ)*base70 + (8825072626083972043/896875000000000000000000000000000 : ℝ)*base72 + (787582400341/280273437500000000000000000 : ℝ)*base73 + (4068406157246472043/896875000000000000000000000000000 : ℝ)*base76 + (3914875396033972043/896875000000000000000000000000000 : ℝ)*base78 + (4977421012399597043/896875000000000000000000000000000 : ℝ)*base80 + (100334135790227/35875000000000000000000000000 : ℝ)*base82 + (5029107/5000000000000000000000 : ℝ)*base90 + (5029107/5000000000000000000000 : ℝ)*base92 + (5029107/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (480740066170571595564351039/64062500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (198126779/25000000000000 : ℝ)*(base19) + (1095598531/50000000000000 : ℝ)*(base23) + (5961587/25000000000000 : ℝ)*(lower2) + (102922923/100000000000000 : ℝ)*(upper3) + (57333917/50000000000000 : ℝ)*(lower4) + (176846029/50000000000000 : ℝ)*(upper5) + (861902525213629/50000000000000 : ℝ)*(major0) + (861902525213629/50000000000000 : ℝ)*(major1) + (861902525213629/50000000000000 : ℝ)*(major2) + (2415499347/20000000000000 : ℝ)*(sp2) + (603822405115533/25000000000000 : ℝ)*(sp4) + (301911103494377/12500000000000 : ℝ)*(sp5) + (150954709485521/6250000000000 : ℝ)*(sp6) + (1032320230251207/100000000000000 : ℝ)*(sp7) + (1032320230251207/100000000000000 : ℝ)*(f.failure) + (603822405115533/25000000000000 : ℝ)*(f.sum) + (375727480363607/53812500000000000000000000000 : ℝ)*base65 + (7728084422352380909/1793750000000000000000000000000000 : ℝ)*base67 + (448097305721130909/1793750000000000000000000000000000 : ℝ)*base69 + (4665522540077380909/1793750000000000000000000000000000 : ℝ)*base71 + (45951263152607/53812500000000000000000000000 : ℝ)*base73 + (2766602740771130909/1793750000000000000000000000000000 : ℝ)*base75 + (5507542379839880909/1793750000000000000000000000000000 : ℝ)*base77 + (4479419316016369091/1793750000000000000000000000000000 : ℝ)*base80 + (86751901289839/107625000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (10672747/5000000000000000000000 : ℝ)*base90 + (10672747/5000000000000000000000 : ℝ)*base92 + (10672747/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1557_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (12457/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3389/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (223/2500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4469/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1557_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1557_s2_0 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1800841467/10000000000 : ℝ)*x 0 + (136120253/250000000 : ℝ)*x 1 + (65050091/125000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1800841467/10000000000 : ℝ)^4611 ≤ (2759765050641/25000000000000 : ℝ)^3587 := by
    have hnat : (1800841467 : ℕ)^4611*25000000000000^3587 ≤ 2759765050641^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1800841467 10000000000 2759765050641 25000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (136120253/250000000 : ℝ)^4611 ≤ (9154662131193/20000000000000 : ℝ)^3587 := by
    have hnat : (136120253 : ℕ)^4611*20000000000000^3587 ≤ 9154662131193^3587*250000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      136120253 250000000 9154662131193 20000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (65050091/125000000 : ℝ)^4611 ≤ (8637525825261/20000000000000 : ℝ)^3587 := by
    have hnat : (65050091 : ℕ)^4611*20000000000000^3587 ≤ 8637525825261^3587*125000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      65050091 125000000 8637525825261 20000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1800841467/10000000000 : ℝ), (136120253/250000000 : ℝ), (65050091/125000000 : ℝ)] ![(2759765050641/25000000000000 : ℝ), (9154662131193/20000000000000 : ℝ), (8637525825261/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1800841467/10000000000 : ℝ)|^4611 ≤ (2759765050641/25000000000000 : ℝ)^3587
        have hw : |(-1800841467/10000000000 : ℝ)|=(1800841467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(136120253/250000000 : ℝ)|^4611 ≤ (9154662131193/20000000000000 : ℝ)^3587
        have hw : |(136120253/250000000 : ℝ)|=(136120253/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(65050091/125000000 : ℝ)|^4611 ≤ (8637525825261/20000000000000 : ℝ)^3587
        have hw : |(65050091/125000000 : ℝ)|=(65050091/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s2_1 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (669193447/1250000000 : ℝ)*x 0 + (-1924507633/10000000000 : ℝ)*x 1 + (5204007481/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669193447/1250000000 : ℝ)^4611 ≤ (44789432251553/100000000000000 : ℝ)^3587 := by
    have hnat : (669193447 : ℕ)^4611*100000000000000^3587 ≤ 44789432251553^3587*1250000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669193447 1250000000 44789432251553 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1924507633/10000000000 : ℝ)^4611 ≤ (480917458653/4000000000000 : ℝ)^3587 := by
    have hnat : (1924507633 : ℕ)^4611*4000000000000^3587 ≤ 480917458653^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1924507633 10000000000 480917458653 4000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5204007481/10000000000 : ℝ)^4611 ≤ (5398453908823/12500000000000 : ℝ)^3587 := by
    have hnat : (5204007481 : ℕ)^4611*12500000000000^3587 ≤ 5398453908823^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5204007481 10000000000 5398453908823 12500000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669193447/1250000000 : ℝ), (-1924507633/10000000000 : ℝ), (5204007481/10000000000 : ℝ)] ![(44789432251553/100000000000000 : ℝ), (480917458653/4000000000000 : ℝ), (5398453908823/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669193447/1250000000 : ℝ)|^4611 ≤ (44789432251553/100000000000000 : ℝ)^3587
        have hw : |(669193447/1250000000 : ℝ)|=(669193447/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1924507633/10000000000 : ℝ)|^4611 ≤ (480917458653/4000000000000 : ℝ)^3587
        have hw : |(-1924507633/10000000000 : ℝ)|=(1924507633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5204007481/10000000000 : ℝ)|^4611 ≤ (5398453908823/12500000000000 : ℝ)^3587
        have hw : |(5204007481/10000000000 : ℝ)|=(5204007481/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s2_2 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1070709557/2000000000 : ℝ)*x 0 + (520400731/1000000000 : ℝ)*x 1 + (-96225379/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070709557/2000000000 : ℝ)^4611 ≤ (44789434499281/100000000000000 : ℝ)^3587 := by
    have hnat : (1070709557 : ℕ)^4611*100000000000000^3587 ≤ 44789434499281^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070709557 2000000000 44789434499281 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (520400731/1000000000 : ℝ)^4611 ≤ (43187629446347/100000000000000 : ℝ)^3587 := by
    have hnat : (520400731 : ℕ)^4611*100000000000000^3587 ≤ 43187629446347^3587*1000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      520400731 1000000000 43187629446347 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (96225379/500000000 : ℝ)^4611 ≤ (1502867005087/12500000000000 : ℝ)^3587 := by
    have hnat : (96225379 : ℕ)^4611*12500000000000^3587 ≤ 1502867005087^3587*500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96225379 500000000 1502867005087 12500000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1070709557/2000000000 : ℝ), (520400731/1000000000 : ℝ), (-96225379/500000000 : ℝ)] ![(44789434499281/100000000000000 : ℝ), (43187629446347/100000000000000 : ℝ), (1502867005087/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1070709557/2000000000 : ℝ)|^4611 ≤ (44789434499281/100000000000000 : ℝ)^3587
        have hw : |(1070709557/2000000000 : ℝ)|=(1070709557/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(520400731/1000000000 : ℝ)|^4611 ≤ (43187629446347/100000000000000 : ℝ)^3587
        have hw : |(520400731/1000000000 : ℝ)|=(520400731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-96225379/500000000 : ℝ)|^4611 ≤ (1502867005087/12500000000000 : ℝ)^3587
        have hw : |(-96225379/500000000 : ℝ)|=(96225379/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s2_3 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6636743/15625000 : ℝ)*x 0 + (3973454941/10000000000 : ℝ)*x 1 + (181474161/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6636743/15625000 : ℝ)^4611 ≤ (2079010591111/6250000000000 : ℝ)^3587 := by
    have hnat : (6636743 : ℕ)^4611*6250000000000^3587 ≤ 2079010591111^3587*15625000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6636743 15625000 2079010591111 6250000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3973454941/10000000000 : ℝ)^4611 ≤ (30530978926557/100000000000000 : ℝ)^3587 := by
    have hnat : (3973454941 : ℕ)^4611*100000000000000^3587 ≤ 30530978926557^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3973454941 10000000000 30530978926557 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181474161/400000000 : ℝ)^4611 ≤ (18102425799451/50000000000000 : ℝ)^3587 := by
    have hnat : (181474161 : ℕ)^4611*50000000000000^3587 ≤ 18102425799451^3587*400000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181474161 400000000 18102425799451 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6636743/15625000 : ℝ), (3973454941/10000000000 : ℝ), (181474161/400000000 : ℝ)] ![(2079010591111/6250000000000 : ℝ), (30530978926557/100000000000000 : ℝ), (18102425799451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6636743/15625000 : ℝ)|^4611 ≤ (2079010591111/6250000000000 : ℝ)^3587
        have hw : |(6636743/15625000 : ℝ)|=(6636743/15625000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3973454941/10000000000 : ℝ)|^4611 ≤ (30530978926557/100000000000000 : ℝ)^3587
        have hw : |(3973454941/10000000000 : ℝ)|=(3973454941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181474161/400000000 : ℝ)|^4611 ≤ (18102425799451/50000000000000 : ℝ)^3587
        have hw : |(181474161/400000000 : ℝ)|=(181474161/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s2_4 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-56277589/312500000 : ℝ)*x 0 + (5205455417/10000000000 : ℝ)*x 1 + (5443350277/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (56277589/312500000 : ℝ)^4611 ≤ (11039386281519/100000000000000 : ℝ)^3587 := by
    have hnat : (56277589 : ℕ)^4611*100000000000000^3587 ≤ 11039386281519^3587*312500000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      56277589 312500000 11039386281519 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5205455417/10000000000 : ℝ)^4611 ≤ (10800769635973/25000000000000 : ℝ)^3587 := by
    have hnat : (5205455417 : ℕ)^4611*25000000000000^3587 ≤ 10800769635973^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5205455417 10000000000 10800769635973 25000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5443350277/10000000000 : ℝ)^4611 ≤ (11439383791459/25000000000000 : ℝ)^3587 := by
    have hnat : (5443350277 : ℕ)^4611*25000000000000^3587 ≤ 11439383791459^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5443350277 10000000000 11439383791459 25000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-56277589/312500000 : ℝ), (5205455417/10000000000 : ℝ), (5443350277/10000000000 : ℝ)] ![(11039386281519/100000000000000 : ℝ), (10800769635973/25000000000000 : ℝ), (11439383791459/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-56277589/312500000 : ℝ)|^4611 ≤ (11039386281519/100000000000000 : ℝ)^3587
        have hw : |(-56277589/312500000 : ℝ)|=(56277589/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5205455417/10000000000 : ℝ)|^4611 ≤ (10800769635973/25000000000000 : ℝ)^3587
        have hw : |(5205455417/10000000000 : ℝ)|=(5205455417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5443350277/10000000000 : ℝ)|^4611 ≤ (11439383791459/25000000000000 : ℝ)^3587
        have hw : |(5443350277/10000000000 : ℝ)|=(5443350277/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s2_5 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5289931947/10000000000 : ℝ)*x 0 + (-421291381/2500000000 : ℝ)*x 1 + (680418783/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5289931947/10000000000 : ℝ)^4611 ≤ (5513303754013/12500000000000 : ℝ)^3587 := by
    have hnat : (5289931947 : ℕ)^4611*12500000000000^3587 ≤ 5513303754013^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5289931947 10000000000 5513303754013 12500000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (421291381/2500000000 : ℝ)^4611 ≤ (10136034931737/100000000000000 : ℝ)^3587 := by
    have hnat : (421291381 : ℕ)^4611*100000000000000^3587 ≤ 10136034931737^3587*2500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      421291381 2500000000 10136034931737 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (680418783/1250000000 : ℝ)^4611 ≤ (571969187817/1250000000000 : ℝ)^3587 := by
    have hnat : (680418783 : ℕ)^4611*1250000000000^3587 ≤ 571969187817^3587*1250000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      680418783 1250000000 571969187817 1250000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5289931947/10000000000 : ℝ), (-421291381/2500000000 : ℝ), (680418783/1250000000 : ℝ)] ![(5513303754013/12500000000000 : ℝ), (10136034931737/100000000000000 : ℝ), (571969187817/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5289931947/10000000000 : ℝ)|^4611 ≤ (5513303754013/12500000000000 : ℝ)^3587
        have hw : |(5289931947/10000000000 : ℝ)|=(5289931947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-421291381/2500000000 : ℝ)|^4611 ≤ (10136034931737/100000000000000 : ℝ)^3587
        have hw : |(-421291381/2500000000 : ℝ)|=(421291381/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(680418783/1250000000 : ℝ)|^4611 ≤ (571969187817/1250000000000 : ℝ)^3587
        have hw : |(680418783/1250000000 : ℝ)|=(680418783/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s2_6 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (661241391/1250000000 : ℝ)*x 0 + (1360838059/2500000000 : ℝ)*x 1 + (-1685163903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (661241391/1250000000 : ℝ)^4611 ≤ (22053210627013/50000000000000 : ℝ)^3587 := by
    have hnat : (661241391 : ℕ)^4611*50000000000000^3587 ≤ 22053210627013^3587*1250000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      661241391 1250000000 22053210627013 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1360838059/2500000000 : ℝ)^4611 ≤ (45757556334553/100000000000000 : ℝ)^3587 := by
    have hnat : (1360838059 : ℕ)^4611*100000000000000^3587 ≤ 45757556334553^3587*2500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1360838059 2500000000 45757556334553 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1685163903/10000000000 : ℝ)^4611 ≤ (10136022398241/100000000000000 : ℝ)^3587 := by
    have hnat : (1685163903 : ℕ)^4611*100000000000000^3587 ≤ 10136022398241^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1685163903 10000000000 10136022398241 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(661241391/1250000000 : ℝ), (1360838059/2500000000 : ℝ), (-1685163903/10000000000 : ℝ)] ![(22053210627013/50000000000000 : ℝ), (45757556334553/100000000000000 : ℝ), (10136022398241/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(661241391/1250000000 : ℝ)|^4611 ≤ (22053210627013/50000000000000 : ℝ)^3587
        have hw : |(661241391/1250000000 : ℝ)|=(661241391/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1360838059/2500000000 : ℝ)|^4611 ≤ (45757556334553/100000000000000 : ℝ)^3587
        have hw : |(1360838059/2500000000 : ℝ)|=(1360838059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1685163903/10000000000 : ℝ)|^4611 ≤ (10136022398241/100000000000000 : ℝ)^3587
        have hw : |(-1685163903/10000000000 : ℝ)|=(1685163903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1557_s2_7 (p : ℝ) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4247614193/10000000000 : ℝ)*x 0 + (906693337/2000000000 : ℝ)*x 1 + (994217899/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4247614193/10000000000 : ℝ)^4611 ≤ (16632581407241/50000000000000 : ℝ)^3587 := by
    have hnat : (4247614193 : ℕ)^4611*50000000000000^3587 ≤ 16632581407241^3587*10000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4247614193 10000000000 16632581407241 50000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906693337/2000000000 : ℝ)^4611 ≤ (1130315841487/3125000000000 : ℝ)^3587 := by
    have hnat : (906693337 : ℕ)^4611*3125000000000^3587 ≤ 1130315841487^3587*2000000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906693337 2000000000 1130315841487 3125000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (994217899/2500000000 : ℝ)^4611 ≤ (30564730233889/100000000000000 : ℝ)^3587 := by
    have hnat : (994217899 : ℕ)^4611*100000000000000^3587 ≤ 30564730233889^3587*2500000000^4611 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      994217899 2500000000 30564730233889 100000000000000 4611 3587 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4611/1024 : ℝ)) 4611 3587 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4247614193/10000000000 : ℝ), (906693337/2000000000 : ℝ), (994217899/2500000000 : ℝ)] ![(16632581407241/50000000000000 : ℝ), (1130315841487/3125000000000 : ℝ), (30564730233889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4247614193/10000000000 : ℝ)|^4611 ≤ (16632581407241/50000000000000 : ℝ)^3587
        have hw : |(4247614193/10000000000 : ℝ)|=(4247614193/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(906693337/2000000000 : ℝ)|^4611 ≤ (1130315841487/3125000000000 : ℝ)^3587
        have hw : |(906693337/2000000000 : ℝ)|=(906693337/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(994217899/2500000000 : ℝ)|^4611 ≤ (30564730233889/100000000000000 : ℝ)^3587
        have hw : |(994217899/2500000000 : ℝ)|=(994217899/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1557_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4469/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/2500 : ℝ)*pair X i i ≤ pair X i h) :
    (1343/12500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1981/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4469/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (223/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4469/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (223/2500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4469/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (223/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4469/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (223/2500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4469/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (223/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4469/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (223/2500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (223/2500 : ℝ) ^ (4609/1024 : ℝ) ≤ (1886326258551121/100000000000000000000 : ℝ) := by
    have hpowers : (223/2500 : ℝ)^4609 ≤ (1886326258551121/100000000000000000000 : ℝ)^1024 := by
      have hnat : (223 : ℕ)^4609*100000000000000000000^1024 ≤ 1886326258551121^1024*2500^4609 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        223 2500 1886326258551121 100000000000000000000 4609 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (223/2500 : ℝ)) (X := (1886326258551121/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4469/25000 : ℝ) ^ (4609/1024 : ℝ) ≤ (10775225331147451/25000000000000000000 : ℝ) := by
    have hpowers : (4469/25000 : ℝ)^4609 ≤ (10775225331147451/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4469 : ℕ)^4609*25000000000000000000^1024 ≤ 10775225331147451^1024*25000^4609 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4469 25000 10775225331147451 25000000000000000000 4609 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4469/25000 : ℝ)) (X := (10775225331147451/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001886326258551121/50000000000000000000 : ℝ) ≤ (10000083817303031/10000000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (50001886326258551121/50000000000000000000 : ℝ)^1024 ≤ (10000083817303031/10000000000000000 : ℝ)^4609 := by
      have hnat : (50001886326258551121 : ℕ)^1024*10000000000000000^4609 ≤ 10000083817303031^4609*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001886326258551121 50000000000000000000 10000083817303031 10000000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000083817303031/10000000000000000 : ℝ)) (X := (50001886326258551121/50000000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (4001799489103325637/4000000000000000000 : ℝ) ≤ (5000499662218167/5000000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (4001799489103325637/4000000000000000000 : ℝ)^1024 ≤ (5000499662218167/5000000000000000 : ℝ)^4609 := by
      have hnat : (4001799489103325637 : ℕ)^1024*5000000000000000^4609 ≤ 5000499662218167^4609*4000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4001799489103325637 4000000000000000000 5000499662218167 5000000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000499662218167/5000000000000000 : ℝ)) (X := (4001799489103325637/4000000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12510775225331147451/12500000000000000000 : ℝ) ≤ (10001914831569637/10000000000000000 : ℝ) ^ (4609/1024 : ℝ) := by
    have hpowers : (12510775225331147451/12500000000000000000 : ℝ)^1024 ≤ (10001914831569637/10000000000000000 : ℝ)^4609 := by
      have hnat : (12510775225331147451 : ℕ)^1024*10000000000000000^4609 ≤ 10001914831569637^4609*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12510775225331147451 12500000000000000000 10001914831569637 10000000000000000 1024 4609 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001914831569637/10000000000000000 : ℝ)) (X := (12510775225331147451/12500000000000000000 : ℝ)) (by norm_num) 4609 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1886326258551121/100000000000000000000 : ℝ) ≤ ((22386104505126955029/22390000000000000000 : ℝ)+2*(915507133303/895600000000000 : ℝ)*(223/2500 : ℝ))^(4609/1024 : ℝ) := by
    rw [show (22386104505126955029/22390000000000000000 : ℝ)+2*(915507133303/895600000000000 : ℝ)*(223/2500 : ℝ)=(10000083817303031/10000000000000000 : ℝ) by norm_num, show 1+2*(1886326258551121/100000000000000000000 : ℝ)=(50001886326258551121/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10775225331147451/25000000000000000000 : ℝ)+(1886326258551121/100000000000000000000 : ℝ) ≤ ((22386104505126955029/22390000000000000000 : ℝ)+(915507133303/895600000000000 : ℝ)*((4469/25000 : ℝ)+(223/2500 : ℝ)))^(4609/1024 : ℝ) := by
    rw [show (22386104505126955029/22390000000000000000 : ℝ)+(915507133303/895600000000000 : ℝ)*((4469/25000 : ℝ)+(223/2500 : ℝ))=(5000499662218167/5000000000000000 : ℝ) by norm_num, show 1+(10775225331147451/25000000000000000000 : ℝ)+(1886326258551121/100000000000000000000 : ℝ)=(4001799489103325637/4000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10775225331147451/25000000000000000000 : ℝ) ≤ ((22386104505126955029/22390000000000000000 : ℝ)+2*(915507133303/895600000000000 : ℝ)*(4469/25000 : ℝ))^(4609/1024 : ℝ) := by
    rw [show (22386104505126955029/22390000000000000000 : ℝ)+2*(915507133303/895600000000000 : ℝ)*(4469/25000 : ℝ)=(10001914831569637/10000000000000000 : ℝ) by norm_num, show 1+2*(10775225331147451/25000000000000000000 : ℝ)=(12510775225331147451/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22386104505126955029/22390000000000000000 : ℝ)*(X 1 0+X 2 0)+(915507133303/895600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (223/2500 : ℝ)) (hi := (4469/25000 : ℝ)) (c := (22386104505126955029/22390000000000000000 : ℝ)) (alpha := (915507133303/895600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22386104505126955029/22390000000000000000 : ℝ)*(X 0 1+X 2 1)+(915507133303/895600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (223/2500 : ℝ)) (hi := (4469/25000 : ℝ)) (c := (22386104505126955029/22390000000000000000 : ℝ)) (alpha := (915507133303/895600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22386104505126955029/22390000000000000000 : ℝ)*(X 0 2+X 1 2)+(915507133303/895600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4609/1024 : ℝ)) (lo := (223/2500 : ℝ)) (hi := (4469/25000 : ℝ)) (c := (22386104505126955029/22390000000000000000 : ℝ)) (alpha := (915507133303/895600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1800841467/10000000000 : ℝ)*X 0 0+(136120253/250000000 : ℝ)*X 0 1+(65050091/125000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669193447/1250000000 : ℝ)*X 1 0+(-1924507633/10000000000 : ℝ)*X 1 1+(5204007481/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1070709557/2000000000 : ℝ)*X 2 0+(520400731/1000000000 : ℝ)*X 2 1+(-96225379/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((6636743/15625000 : ℝ)*X 0 0+(3973454941/10000000000 : ℝ)*X 0 1+(181474161/400000000 : ℝ)*X 0 2+(6636743/15625000 : ℝ)*X 1 0+(3973454941/10000000000 : ℝ)*X 1 1+(181474161/400000000 : ℝ)*X 1 2+(6636743/15625000 : ℝ)*X 2 0+(3973454941/10000000000 : ℝ)*X 2 1+(181474161/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-56277589/312500000 : ℝ)*X 0 0+(5205455417/10000000000 : ℝ)*X 0 1+(5443350277/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5289931947/10000000000 : ℝ)*X 1 0+(-421291381/2500000000 : ℝ)*X 1 1+(680418783/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((661241391/1250000000 : ℝ)*X 2 0+(1360838059/2500000000 : ℝ)*X 2 1+(-1685163903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4247614193/10000000000 : ℝ)*X 0 0+(906693337/2000000000 : ℝ)*X 0 1+(994217899/2500000000 : ℝ)*X 0 2+(4247614193/10000000000 : ℝ)*X 1 0+(906693337/2000000000 : ℝ)*X 1 1+(994217899/2500000000 : ℝ)*X 1 2+(4247614193/10000000000 : ℝ)*X 2 0+(906693337/2000000000 : ℝ)*X 2 1+(994217899/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1557_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2361880510492092450570000657/279875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (770135249/50000000000000 : ℝ)*(base19) + (1675009261/100000000000000 : ℝ)*(base23) + (182564857/100000000000000 : ℝ)*(upper3) + (7330491/50000000000000 : ℝ)*(upper4) + (945391/400000000000 : ℝ)*(upper5) + (1481946796689389/50000000000000 : ℝ)*(major0) + (1481946796689389/50000000000000 : ℝ)*(major1) + (1481946796689389/50000000000000 : ℝ)*(major2) + (519099855580747/12500000000000 : ℝ)*(sp0) + (415282402834583/10000000000000 : ℝ)*(sp1) + (2076411946803533/50000000000000 : ℝ)*(sp2) + (354990207913013/20000000000000 : ℝ)*(sp3) + (26723970351/100000000000000 : ℝ)*(sp4) + (411890973/4000000000000 : ℝ)*(sp7) + (177496133683939/10000000000000 : ℝ)*(f.failure) + (519103196077041/12500000000000 : ℝ)*(f.sum) + (30018639311283/22390000000000000000000000000 : ℝ)*base66 + (6089968877429662281/1119500000000000000000000000000000 : ℝ)*base67 + (5498274443107162281/1119500000000000000000000000000000 : ℝ)*base69 + (9101863672766337719/1119500000000000000000000000000000 : ℝ)*base72 + (84618131245867/22390000000000000000000000000 : ℝ)*base73 + (356621719208662281/1119500000000000000000000000000000 : ℝ)*base75 + (1691861929998662281/1119500000000000000000000000000000 : ℝ)*base77 + (7848441444656162281/1119500000000000000000000000000000 : ℝ)*base79 + (36731056504317/22390000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (837481/500000000000000000000 : ℝ)*base89 + (837481/500000000000000000000 : ℝ)*base91 + (837481/500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (374212281341802079342437/22390000000000000000000000000 : ℝ) := by norm_num
    linear_combination (373429017/100000000000000 : ℝ)*(base19) + (83732173/10000000000000 : ℝ)*(base23) + (19627439/20000000000000 : ℝ)*(upper3) + (367509819/100000000000000 : ℝ)*(lower4) + (107196681/50000000000000 : ℝ)*(upper5) + (1500042309528477/50000000000000 : ℝ)*(major0) + (1500042309528477/50000000000000 : ℝ)*(major1) + (1500042309528477/50000000000000 : ℝ)*(major2) + (1390406139/50000000000000 : ℝ)*(sp1) + (37701751929/100000000000000 : ℝ)*(sp2) + (42035339374439/1000000000000 : ℝ)*(sp4) + (840706156640521/20000000000000 : ℝ)*(sp5) + (4203495398370241/100000000000000 : ℝ)*(sp6) + (898317371778889/50000000000000 : ℝ)*(sp7) + (898317371778889/50000000000000 : ℝ)*(f.failure) + (42035339374439/1000000000000 : ℝ)*(f.sum) + (30221677359471/22390000000000000000000000000 : ℝ)*base65 + (3690634842472864167/1119500000000000000000000000000000 : ℝ)*base68 + (625483489446135833/1119500000000000000000000000000000 : ℝ)*base69 + (4773382762419364167/1119500000000000000000000000000000 : ℝ)*base72 + (38188773017509/22390000000000000000000000000 : ℝ)*base74 + (10786144819455135833/1119500000000000000000000000000000 : ℝ)*base75 + (1516901733894364167/1119500000000000000000000000000000 : ℝ)*base78 + (5223715765390135833/1119500000000000000000000000000000 : ℝ)*base79 + (11543373093981/22390000000000000000000000000 : ℝ)*base81 + (12746469/2500000000000000000000 : ℝ)*base90 + (12746469/2500000000000000000000 : ℝ)*base92 + (12746469/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1557_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4469/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (223/2500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1343/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1981/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1557_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1557_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1343/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1981/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1557_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1557_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1557_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4609/1024 : ℝ) ≤ p) (hpb : p ≤ (4611/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (83491779/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1343/12500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1981/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1557_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
