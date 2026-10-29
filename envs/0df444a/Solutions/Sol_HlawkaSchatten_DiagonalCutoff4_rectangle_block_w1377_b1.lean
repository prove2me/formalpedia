-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1377_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:22:10.836927+00:00
-- url     : https://prove2.me/submissions/56a6a984-0aa7-413c-99a3-ec29fea2aed3

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
theorem support_rectangle_w1377_s3_0 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1006340823/5000000000 : ℝ)*x 0 + (2711452501/5000000000 : ℝ)*x 1 + (5234560519/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006340823/5000000000 : ℝ)^4337 ≤ (3065646848519/25000000000000 : ℝ)^3313 := by
    have hnat : (1006340823 : ℕ)^4337*25000000000000^3313 ≤ 3065646848519^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006340823 5000000000 3065646848519 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711452501/5000000000 : ℝ)^4337 ≤ (22441763725451/50000000000000 : ℝ)^3313 := by
    have hnat : (2711452501 : ℕ)^4337*50000000000000^3313 ≤ 22441763725451^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711452501 5000000000 22441763725451 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234560519/10000000000 : ℝ)^4337 ≤ (42853885142953/100000000000000 : ℝ)^3313 := by
    have hnat : (5234560519 : ℕ)^4337*100000000000000^3313 ≤ 42853885142953^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234560519 10000000000 42853885142953 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1006340823/5000000000 : ℝ), (2711452501/5000000000 : ℝ), (5234560519/10000000000 : ℝ)] ![(3065646848519/25000000000000 : ℝ), (22441763725451/50000000000000 : ℝ), (42853885142953/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1006340823/5000000000 : ℝ)|^4337 ≤ (3065646848519/25000000000000 : ℝ)^3313
        have hw : |(-1006340823/5000000000 : ℝ)|=(1006340823/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711452501/5000000000 : ℝ)|^4337 ≤ (22441763725451/50000000000000 : ℝ)^3313
        have hw : |(2711452501/5000000000 : ℝ)|=(2711452501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234560519/10000000000 : ℝ)|^4337 ≤ (42853885142953/100000000000000 : ℝ)^3313
        have hw : |(5234560519/10000000000 : ℝ)|=(5234560519/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s3_1 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351442703/10000000000 : ℝ)*x 0 + (-1054429657/5000000000 : ℝ)*x 1 + (5234560771/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351442703/10000000000 : ℝ)^4337 ≤ (44110825713431/100000000000000 : ℝ)^3313 := by
    have hnat : (5351442703 : ℕ)^4337*100000000000000^3313 ≤ 44110825713431^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351442703 10000000000 44110825713431 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1054429657/5000000000 : ℝ)^4337 ≤ (3258821606561/25000000000000 : ℝ)^3313 := by
    have hnat : (1054429657 : ℕ)^4337*25000000000000^3313 ≤ 3258821606561^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054429657 5000000000 3258821606561 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5234560771/10000000000 : ℝ)^4337 ≤ (42853887843667/100000000000000 : ℝ)^3313 := by
    have hnat : (5234560771 : ℕ)^4337*100000000000000^3313 ≤ 42853887843667^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5234560771 10000000000 42853887843667 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351442703/10000000000 : ℝ), (-1054429657/5000000000 : ℝ), (5234560771/10000000000 : ℝ)] ![(44110825713431/100000000000000 : ℝ), (3258821606561/25000000000000 : ℝ), (42853887843667/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351442703/10000000000 : ℝ)|^4337 ≤ (44110825713431/100000000000000 : ℝ)^3313
        have hw : |(5351442703/10000000000 : ℝ)|=(5351442703/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1054429657/5000000000 : ℝ)|^4337 ≤ (3258821606561/25000000000000 : ℝ)^3313
        have hw : |(-1054429657/5000000000 : ℝ)|=(1054429657/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5234560771/10000000000 : ℝ)|^4337 ≤ (42853887843667/100000000000000 : ℝ)^3313
        have hw : |(5234560771/10000000000 : ℝ)|=(5234560771/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s3_2 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337860683/2500000000 : ℝ)*x 0 + (1308640249/2500000000 : ℝ)*x 1 + (-1054429489/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337860683/2500000000 : ℝ)^4337 ≤ (11027706506589/25000000000000 : ℝ)^3313 := by
    have hnat : (1337860683 : ℕ)^4337*25000000000000^3313 ≤ 11027706506589^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337860683 2500000000 11027706506589 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1308640249/2500000000 : ℝ)^4337 ≤ (21426945127509/50000000000000 : ℝ)^3313 := by
    have hnat : (1308640249 : ℕ)^4337*50000000000000^3313 ≤ 21426945127509^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1308640249 2500000000 21426945127509 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1054429489/5000000000 : ℝ)^4337 ≤ (521411348297/4000000000000 : ℝ)^3313 := by
    have hnat : (1054429489 : ℕ)^4337*4000000000000^3313 ≤ 521411348297^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054429489 5000000000 521411348297 4000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337860683/2500000000 : ℝ), (1308640249/2500000000 : ℝ), (-1054429489/5000000000 : ℝ)] ![(11027706506589/25000000000000 : ℝ), (21426945127509/50000000000000 : ℝ), (521411348297/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337860683/2500000000 : ℝ)|^4337 ≤ (11027706506589/25000000000000 : ℝ)^3313
        have hw : |(1337860683/2500000000 : ℝ)|=(1337860683/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1308640249/2500000000 : ℝ)|^4337 ≤ (21426945127509/50000000000000 : ℝ)^3313
        have hw : |(1308640249/2500000000 : ℝ)|=(1308640249/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1054429489/5000000000 : ℝ)|^4337 ≤ (521411348297/4000000000000 : ℝ)^3313
        have hw : |(-1054429489/5000000000 : ℝ)|=(1054429489/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s3_3 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158339563/5000000000 : ℝ)*x 0 + (4121083733/10000000000 : ℝ)*x 1 + (452078453/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158339563/5000000000 : ℝ)^4337 ≤ (8323766485921/25000000000000 : ℝ)^3313 := by
    have hnat : (2158339563 : ℕ)^4337*25000000000000^3313 ≤ 8323766485921^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158339563 5000000000 8323766485921 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4121083733/10000000000 : ℝ)^4337 ≤ (31334090044421/100000000000000 : ℝ)^3313 := by
    have hnat : (4121083733 : ℕ)^4337*100000000000000^3313 ≤ 31334090044421^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4121083733 10000000000 31334090044421 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452078453/1000000000 : ℝ)^4337 ≤ (35370844001841/100000000000000 : ℝ)^3313 := by
    have hnat : (452078453 : ℕ)^4337*100000000000000^3313 ≤ 35370844001841^3313*1000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452078453 1000000000 35370844001841 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158339563/5000000000 : ℝ), (4121083733/10000000000 : ℝ), (452078453/1000000000 : ℝ)] ![(8323766485921/25000000000000 : ℝ), (31334090044421/100000000000000 : ℝ), (35370844001841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158339563/5000000000 : ℝ)|^4337 ≤ (8323766485921/25000000000000 : ℝ)^3313
        have hw : |(2158339563/5000000000 : ℝ)|=(2158339563/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4121083733/10000000000 : ℝ)|^4337 ≤ (31334090044421/100000000000000 : ℝ)^3313
        have hw : |(4121083733/10000000000 : ℝ)|=(4121083733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(452078453/1000000000 : ℝ)|^4337 ≤ (35370844001841/100000000000000 : ℝ)^3313
        have hw : |(452078453/1000000000 : ℝ)|=(452078453/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s3_4 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1006350001/5000000000 : ℝ)*x 0 + (2617665333/5000000000 : ℝ)*x 1 + (1355532419/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1006350001/5000000000 : ℝ)^4337 ≤ (3065683449581/25000000000000 : ℝ)^3313 := by
    have hnat : (1006350001 : ℕ)^4337*25000000000000^3313 ≤ 3065683449581^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1006350001 5000000000 3065683449581 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2617665333/5000000000 : ℝ)^4337 ≤ (42862139085939/100000000000000 : ℝ)^3313 := by
    have hnat : (2617665333 : ℕ)^4337*100000000000000^3313 ≤ 42862139085939^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2617665333 5000000000 42862139085939 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355532419/2500000000 : ℝ)^4337 ≤ (22437563547149/50000000000000 : ℝ)^3313 := by
    have hnat : (1355532419 : ℕ)^4337*50000000000000^3313 ≤ 22437563547149^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355532419 2500000000 22437563547149 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1006350001/5000000000 : ℝ), (2617665333/5000000000 : ℝ), (1355532419/2500000000 : ℝ)] ![(3065683449581/25000000000000 : ℝ), (42862139085939/100000000000000 : ℝ), (22437563547149/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1006350001/5000000000 : ℝ)|^4337 ≤ (3065683449581/25000000000000 : ℝ)^3313
        have hw : |(-1006350001/5000000000 : ℝ)|=(1006350001/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2617665333/5000000000 : ℝ)|^4337 ≤ (42862139085939/100000000000000 : ℝ)^3313
        have hw : |(2617665333/5000000000 : ℝ)|=(2617665333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355532419/2500000000 : ℝ)|^4337 ≤ (22437563547149/50000000000000 : ℝ)^3313
        have hw : |(1355532419/2500000000 : ℝ)|=(1355532419/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s3_5 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325684917/2500000000 : ℝ)*x 0 + (-480322339/2500000000 : ℝ)*x 1 + (5422130429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325684917/2500000000 : ℝ)^4337 ≤ (21793017720737/50000000000000 : ℝ)^3313 := by
    have hnat : (1325684917 : ℕ)^4337*50000000000000^3313 ≤ 21793017720737^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325684917 2500000000 21793017720737 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (480322339/2500000000 : ℝ)^4337 ≤ (1442353662011/12500000000000 : ℝ)^3313 := by
    have hnat : (480322339 : ℕ)^4337*12500000000000^3313 ≤ 1442353662011^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      480322339 2500000000 1442353662011 12500000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422130429/10000000000 : ℝ)^4337 ≤ (44875135252581/100000000000000 : ℝ)^3313 := by
    have hnat : (5422130429 : ℕ)^4337*100000000000000^3313 ≤ 44875135252581^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422130429 10000000000 44875135252581 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325684917/2500000000 : ℝ), (-480322339/2500000000 : ℝ), (5422130429/10000000000 : ℝ)] ![(21793017720737/50000000000000 : ℝ), (1442353662011/12500000000000 : ℝ), (44875135252581/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325684917/2500000000 : ℝ)|^4337 ≤ (21793017720737/50000000000000 : ℝ)^3313
        have hw : |(1325684917/2500000000 : ℝ)|=(1325684917/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-480322339/2500000000 : ℝ)|^4337 ≤ (1442353662011/12500000000000 : ℝ)^3313
        have hw : |(-480322339/2500000000 : ℝ)|=(480322339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422130429/10000000000 : ℝ)|^4337 ≤ (44875135252581/100000000000000 : ℝ)^3313
        have hw : |(5422130429/10000000000 : ℝ)|=(5422130429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s3_6 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2651370539/5000000000 : ℝ)*x 0 + (2711064677/5000000000 : ℝ)*x 1 + (-1921288907/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2651370539/5000000000 : ℝ)^4337 ≤ (10896512653293/25000000000000 : ℝ)^3313 := by
    have hnat : (2651370539 : ℕ)^4337*25000000000000^3313 ≤ 10896512653293^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2651370539 5000000000 10896512653293 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711064677/5000000000 : ℝ)^4337 ≤ (4487512360563/10000000000000 : ℝ)^3313 := by
    have hnat : (2711064677 : ℕ)^4337*10000000000000^3313 ≤ 4487512360563^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711064677 5000000000 4487512360563 10000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1921288907/10000000000 : ℝ)^4337 ≤ (11538825766019/100000000000000 : ℝ)^3313 := by
    have hnat : (1921288907 : ℕ)^4337*100000000000000^3313 ≤ 11538825766019^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1921288907 10000000000 11538825766019 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2651370539/5000000000 : ℝ), (2711064677/5000000000 : ℝ), (-1921288907/10000000000 : ℝ)] ![(10896512653293/25000000000000 : ℝ), (4487512360563/10000000000000 : ℝ), (11538825766019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2651370539/5000000000 : ℝ)|^4337 ≤ (10896512653293/25000000000000 : ℝ)^3313
        have hw : |(2651370539/5000000000 : ℝ)|=(2651370539/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711064677/5000000000 : ℝ)|^4337 ≤ (4487512360563/10000000000000 : ℝ)^3313
        have hw : |(2711064677/5000000000 : ℝ)|=(2711064677/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1921288907/10000000000 : ℝ)|^4337 ≤ (11538825766019/100000000000000 : ℝ)^3313
        have hw : |(-1921288907/10000000000 : ℝ)|=(1921288907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s3_7 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4316717963/10000000000 : ℝ)*x 0 + (2259574931/5000000000 : ℝ)*x 1 + (4122726253/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4316717963/10000000000 : ℝ)^4337 ≤ (33295458086603/100000000000000 : ℝ)^3313 := by
    have hnat : (4316717963 : ℕ)^4337*100000000000000^3313 ≤ 33295458086603^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4316717963 10000000000 33295458086603 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2259574931/5000000000 : ℝ)^4337 ≤ (35354102096177/100000000000000 : ℝ)^3313 := by
    have hnat : (2259574931 : ℕ)^4337*100000000000000^3313 ≤ 35354102096177^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2259574931 5000000000 35354102096177 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4122726253/10000000000 : ℝ)^4337 ≤ (1567521989593/5000000000000 : ℝ)^3313 := by
    have hnat : (4122726253 : ℕ)^4337*5000000000000^3313 ≤ 1567521989593^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4122726253 10000000000 1567521989593 5000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4316717963/10000000000 : ℝ), (2259574931/5000000000 : ℝ), (4122726253/10000000000 : ℝ)] ![(33295458086603/100000000000000 : ℝ), (35354102096177/100000000000000 : ℝ), (1567521989593/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4316717963/10000000000 : ℝ)|^4337 ≤ (33295458086603/100000000000000 : ℝ)^3313
        have hw : |(4316717963/10000000000 : ℝ)|=(4316717963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2259574931/5000000000 : ℝ)|^4337 ≤ (35354102096177/100000000000000 : ℝ)^3313
        have hw : |(2259574931/5000000000 : ℝ)|=(2259574931/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4122726253/10000000000 : ℝ)|^4337 ≤ (1567521989593/5000000000000 : ℝ)^3313
        have hw : |(4122726253/10000000000 : ℝ)|=(4122726253/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s3_8 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-82977967/10000000000 : ℝ)*x 0 + (2857978101/5000000000 : ℝ)*x 1 + (6043759957/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (82977967/10000000000 : ℝ)^4337 ≤ (23586013401/12500000000000 : ℝ)^3313 := by
    have hnat : (82977967 : ℕ)^4337*12500000000000^3313 ≤ 23586013401^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82977967 10000000000 23586013401 12500000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2857978101/5000000000 : ℝ)^4337 ≤ (48084888176351/100000000000000 : ℝ)^3313 := by
    have hnat : (2857978101 : ℕ)^4337*100000000000000^3313 ≤ 48084888176351^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2857978101 5000000000 48084888176351 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (6043759957/10000000000 : ℝ)^4337 ≤ (10345284740377/20000000000000 : ℝ)^3313 := by
    have hnat : (6043759957 : ℕ)^4337*20000000000000^3313 ≤ 10345284740377^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6043759957 10000000000 10345284740377 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-82977967/10000000000 : ℝ), (2857978101/5000000000 : ℝ), (6043759957/10000000000 : ℝ)] ![(23586013401/12500000000000 : ℝ), (48084888176351/100000000000000 : ℝ), (10345284740377/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-82977967/10000000000 : ℝ)|^4337 ≤ (23586013401/12500000000000 : ℝ)^3313
        have hw : |(-82977967/10000000000 : ℝ)|=(82977967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2857978101/5000000000 : ℝ)|^4337 ≤ (48084888176351/100000000000000 : ℝ)^3313
        have hw : |(2857978101/5000000000 : ℝ)|=(2857978101/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(6043759957/10000000000 : ℝ)|^4337 ≤ (10345284740377/20000000000000 : ℝ)^3313
        have hw : |(6043759957/10000000000 : ℝ)|=(6043759957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s3_9 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1027366643/10000000000 : ℝ)*x 0 + (872939259/1250000000 : ℝ)*x 1 + (-4229281891/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1027366643/10000000000 : ℝ)^4337 ≤ (1271171704931/25000000000000 : ℝ)^3313 := by
    have hnat : (1027366643 : ℕ)^4337*25000000000000^3313 ≤ 1271171704931^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1027366643 10000000000 1271171704931 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (872939259/1250000000 : ℝ)^4337 ≤ (31249967316639/50000000000000 : ℝ)^3313 := by
    have hnat : (872939259 : ℕ)^4337*50000000000000^3313 ≤ 31249967316639^3313*1250000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      872939259 1250000000 31249967316639 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4229281891/10000000000 : ℝ)^4337 ≤ (32415378544731/100000000000000 : ℝ)^3313 := by
    have hnat : (4229281891 : ℕ)^4337*100000000000000^3313 ≤ 32415378544731^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4229281891 10000000000 32415378544731 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1027366643/10000000000 : ℝ), (872939259/1250000000 : ℝ), (-4229281891/10000000000 : ℝ)] ![(1271171704931/25000000000000 : ℝ), (31249967316639/50000000000000 : ℝ), (32415378544731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1027366643/10000000000 : ℝ)|^4337 ≤ (1271171704931/25000000000000 : ℝ)^3313
        have hw : |(1027366643/10000000000 : ℝ)|=(1027366643/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(872939259/1250000000 : ℝ)|^4337 ≤ (31249967316639/50000000000000 : ℝ)^3313
        have hw : |(872939259/1250000000 : ℝ)|=(872939259/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-4229281891/10000000000 : ℝ)|^4337 ≤ (32415378544731/100000000000000 : ℝ)^3313
        have hw : |(-4229281891/10000000000 : ℝ)|=(4229281891/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s3_10 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (19265701/200000000 : ℝ)*x 0 + (5835211213/10000000000 : ℝ)*x 1 + (2759338873/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (19265701/200000000 : ℝ)^4337 ≤ (116839115211/2500000000000 : ℝ)^3313 := by
    have hnat : (19265701 : ℕ)^4337*2500000000000^3313 ≤ 116839115211^3313*200000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19265701 200000000 116839115211 2500000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5835211213/10000000000 : ℝ)^4337 ≤ (49402403692343/100000000000000 : ℝ)^3313 := by
    have hnat : (5835211213 : ℕ)^4337*100000000000000^3313 ≤ 49402403692343^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5835211213 10000000000 49402403692343 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2759338873/5000000000 : ℝ)^4337 ≤ (5740503961273/12500000000000 : ℝ)^3313 := by
    have hnat : (2759338873 : ℕ)^4337*12500000000000^3313 ≤ 5740503961273^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2759338873 5000000000 5740503961273 12500000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(19265701/200000000 : ℝ), (5835211213/10000000000 : ℝ), (2759338873/5000000000 : ℝ)] ![(116839115211/2500000000000 : ℝ), (49402403692343/100000000000000 : ℝ), (5740503961273/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(19265701/200000000 : ℝ)|^4337 ≤ (116839115211/2500000000000 : ℝ)^3313
        have hw : |(19265701/200000000 : ℝ)|=(19265701/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5835211213/10000000000 : ℝ)|^4337 ≤ (49402403692343/100000000000000 : ℝ)^3313
        have hw : |(5835211213/10000000000 : ℝ)|=(5835211213/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2759338873/5000000000 : ℝ)|^4337 ≤ (5740503961273/12500000000000 : ℝ)^3313
        have hw : |(2759338873/5000000000 : ℝ)|=(2759338873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1377_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3993/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (10993/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14979/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3993/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1259/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3993/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1259/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3993/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1259/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3993/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1259/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3993/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1259/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3993/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1259/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base21 : ((1 : ℝ)*X 2 0+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 0).2]
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
  have hpowlo : (1259/12500 : ℝ) ^ (271/64 : ℝ) ≤ (6009220146555053/100000000000000000000 : ℝ) := by
    have hpowers : (1259/12500 : ℝ)^271 ≤ (6009220146555053/100000000000000000000 : ℝ)^64 := by
      have hnat : (1259 : ℕ)^271*100000000000000000000^64 ≤ 6009220146555053^64*12500^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1259 12500 6009220146555053 100000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1259/12500 : ℝ)) (X := (6009220146555053/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hpowhi : (3993/25000 : ℝ) ^ (271/64 : ℝ) ≤ (846748699016951/2000000000000000000 : ℝ) := by
    have hpowers : (3993/25000 : ℝ)^271 ≤ (846748699016951/2000000000000000000 : ℝ)^64 := by
      have hnat : (3993 : ℕ)^271*2000000000000000000^64 ≤ 846748699016951^64*25000^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3993 25000 846748699016951 2000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3993/25000 : ℝ)) (X := (846748699016951/2000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50006009220146555053/50000000000000000000 : ℝ) ≤ (500014190864859/500000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (50006009220146555053/50000000000000000000 : ℝ)^64 ≤ (500014190864859/500000000000000 : ℝ)^271 := by
      have hnat : (50006009220146555053 : ℕ)^64*500000000000000^271 ≤ 500014190864859^271*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50006009220146555053 50000000000000000000 500014190864859 500000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500014190864859/500000000000000 : ℝ)) (X := (50006009220146555053/50000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (100048346655097402603/100000000000000000000 : ℝ) ≤ (10001141555262989/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (100048346655097402603/100000000000000000000 : ℝ)^64 ≤ (10001141555262989/10000000000000000 : ℝ)^271 := by
      have hnat : (100048346655097402603 : ℕ)^64*10000000000000000^271 ≤ 10001141555262989^271*100000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100048346655097402603 100000000000000000000 10001141555262989 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001141555262989/10000000000000000 : ℝ)) (X := (100048346655097402603/100000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (1000846748699016951/1000000000000000000 : ℝ) ≤ (5000999646614399/5000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (1000846748699016951/1000000000000000000 : ℝ)^64 ≤ (5000999646614399/5000000000000000 : ℝ)^271 := by
      have hnat : (1000846748699016951 : ℕ)^64*5000000000000000^271 ≤ 5000999646614399^271*1000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1000846748699016951 1000000000000000000 5000999646614399 5000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000999646614399/5000000000000000 : ℝ)) (X := (1000846748699016951/1000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6009220146555053/100000000000000000000 : ℝ) ≤ ((1843262382764690797/1843750000000000000 : ℝ)+2*(857737965809/590000000000000 : ℝ)*(1259/12500 : ℝ))^(271/64 : ℝ) := by
    rw [show (1843262382764690797/1843750000000000000 : ℝ)+2*(857737965809/590000000000000 : ℝ)*(1259/12500 : ℝ)=(500014190864859/500000000000000 : ℝ) by norm_num, show 1+2*(6009220146555053/100000000000000000000 : ℝ)=(50006009220146555053/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(846748699016951/2000000000000000000 : ℝ)+(6009220146555053/100000000000000000000 : ℝ) ≤ ((1843262382764690797/1843750000000000000 : ℝ)+(857737965809/590000000000000 : ℝ)*((3993/25000 : ℝ)+(1259/12500 : ℝ)))^(271/64 : ℝ) := by
    rw [show (1843262382764690797/1843750000000000000 : ℝ)+(857737965809/590000000000000 : ℝ)*((3993/25000 : ℝ)+(1259/12500 : ℝ))=(10001141555262989/10000000000000000 : ℝ) by norm_num, show 1+(846748699016951/2000000000000000000 : ℝ)+(6009220146555053/100000000000000000000 : ℝ)=(100048346655097402603/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(846748699016951/2000000000000000000 : ℝ) ≤ ((1843262382764690797/1843750000000000000 : ℝ)+2*(857737965809/590000000000000 : ℝ)*(3993/25000 : ℝ))^(271/64 : ℝ) := by
    rw [show (1843262382764690797/1843750000000000000 : ℝ)+2*(857737965809/590000000000000 : ℝ)*(3993/25000 : ℝ)=(5000999646614399/5000000000000000 : ℝ) by norm_num, show 1+2*(846748699016951/2000000000000000000 : ℝ)=(1000846748699016951/1000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1843262382764690797/1843750000000000000 : ℝ)*(X 1 0+X 2 0)+(857737965809/590000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (1259/12500 : ℝ)) (hi := (3993/25000 : ℝ)) (c := (1843262382764690797/1843750000000000000 : ℝ)) (alpha := (857737965809/590000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1843262382764690797/1843750000000000000 : ℝ)*(X 0 1+X 2 1)+(857737965809/590000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (1259/12500 : ℝ)) (hi := (3993/25000 : ℝ)) (c := (1843262382764690797/1843750000000000000 : ℝ)) (alpha := (857737965809/590000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1843262382764690797/1843750000000000000 : ℝ)*(X 0 2+X 1 2)+(857737965809/590000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (1259/12500 : ℝ)) (hi := (3993/25000 : ℝ)) (c := (1843262382764690797/1843750000000000000 : ℝ)) (alpha := (857737965809/590000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1006340823/5000000000 : ℝ)*X 0 0+(2711452501/5000000000 : ℝ)*X 0 1+(5234560519/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351442703/10000000000 : ℝ)*X 1 0+(-1054429657/5000000000 : ℝ)*X 1 1+(5234560771/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337860683/2500000000 : ℝ)*X 2 0+(1308640249/2500000000 : ℝ)*X 2 1+(-1054429489/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158339563/5000000000 : ℝ)*X 0 0+(4121083733/10000000000 : ℝ)*X 0 1+(452078453/1000000000 : ℝ)*X 0 2+(2158339563/5000000000 : ℝ)*X 1 0+(4121083733/10000000000 : ℝ)*X 1 1+(452078453/1000000000 : ℝ)*X 1 2+(2158339563/5000000000 : ℝ)*X 2 0+(4121083733/10000000000 : ℝ)*X 2 1+(452078453/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1006350001/5000000000 : ℝ)*X 0 0+(2617665333/5000000000 : ℝ)*X 0 1+(1355532419/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325684917/2500000000 : ℝ)*X 1 0+(-480322339/2500000000 : ℝ)*X 1 1+(5422130429/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2651370539/5000000000 : ℝ)*X 2 0+(2711064677/5000000000 : ℝ)*X 2 1+(-1921288907/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4316717963/10000000000 : ℝ)*X 0 0+(2259574931/5000000000 : ℝ)*X 0 1+(4122726253/10000000000 : ℝ)*X 0 2+(4316717963/10000000000 : ℝ)*X 1 0+(2259574931/5000000000 : ℝ)*X 1 1+(4122726253/10000000000 : ℝ)*X 1 2+(4316717963/10000000000 : ℝ)*X 2 0+(2259574931/5000000000 : ℝ)*X 2 1+(4122726253/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-82977967/10000000000 : ℝ)*X 0 0+(2857978101/5000000000 : ℝ)*X 0 1+(6043759957/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s3_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1027366643/10000000000 : ℝ)*X 2 0+(872939259/1250000000 : ℝ)*X 2 1+(-4229281891/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s3_9 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((19265701/200000000 : ℝ)*X 0 0+(5835211213/10000000000 : ℝ)*X 0 1+(2759338873/5000000000 : ℝ)*X 0 2+(19265701/200000000 : ℝ)*X 1 0+(5835211213/10000000000 : ℝ)*X 1 1+(2759338873/5000000000 : ℝ)*X 1 2+(19265701/200000000 : ℝ)*X 2 0+(5835211213/10000000000 : ℝ)*X 2 1+(2759338873/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s3_10 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (154210140557224736640161847/23046875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2860853/10000000000000 : ℝ)*(base21) + (74835609/50000000000000 : ℝ)*(lower2) + (9086447/10000000000000 : ℝ)*(lower4) + (74869611/100000000000000 : ℝ)*(upper5) + (976414317614467/25000000000000 : ℝ)*(major0) + (976414317614467/25000000000000 : ℝ)*(major1) + (976414317614467/25000000000000 : ℝ)*(major2) + (265471440408371/5000000000000 : ℝ)*(sp0) + (5309435941443133/100000000000000 : ℝ)*(sp1) + (5309442095309041/100000000000000 : ℝ)*(sp2) + (1250935942557289/50000000000000 : ℝ)*(sp3) + (13315750151/100000000000000 : ℝ)*(sp4) + (3091237219/50000000000000 : ℝ)*(sp5) + (308845183/100000000000000 : ℝ)*(sp7) + (2501872193959761/100000000000000 : ℝ)*(f.failure) + (1327360530979393/25000000000000 : ℝ)*(f.sum) + (5972032462839/3687500000000000000000000000 : ℝ)*base65 + (80656718537233963/23046875000000000000000000000000 : ℝ)*base68 + (93771756196546669/11523437500000000000000000000000 : ℝ)*base70 + (137419811726047287/23046875000000000000000000000000 : ℝ)*base71 + (30360810499947/7375000000000000000000000000 : ℝ)*base74 + (199319022530202713/23046875000000000000000000000000 : ℝ)*base76 + (30941567110125103/5761718750000000000000000000000 : ℝ)*base77 + (170283697588015213/23046875000000000000000000000000 : ℝ)*base80 + (354953330491/921875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1312153/1250000000000000000000 : ℝ)*base89 + (1312153/1250000000000000000000 : ℝ)*base91 + (1312153/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (39559467960436602972419997/92187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28003793/50000000000000 : ℝ)*(lower4) + (3937955553434461/100000000000000 : ℝ)*(major0) + (3937955553434461/100000000000000 : ℝ)*(major1) + (3937955553434461/100000000000000 : ℝ)*(major2) + (14558253493/100000000000000 : ℝ)*(sp1) + (1985273503/100000000000000 : ℝ)*(sp2) + (1369096343/50000000000000 : ℝ)*(sp3) + (133833682155703/2500000000000 : ℝ)*(sp4) + (1338333704967481/25000000000000 : ℝ)*(sp5) + (66916820494551/1250000000000 : ℝ)*(sp6) + (1261278715647821/50000000000000 : ℝ)*(sp7) + (1045947649/50000000000000 : ℝ)*(sp8) + (876642917/50000000000000 : ℝ)*(sp9) + (96559573/6250000000000 : ℝ)*(sp10) + (1261280857220749/50000000000000 : ℝ)*(f.failure) + (2676674689061709/50000000000000 : ℝ)*(f.sum) + (68568696401949/29500000000000000000000000000 : ℝ)*base65 + (608343627043973021/92187500000000000000000000000000 : ℝ)*base67 + (406721221759598021/92187500000000000000000000000000 : ℝ)*base69 + (4167954881248660521/92187500000000000000000000000000 : ℝ)*base71 + (120752261083949/29500000000000000000000000000 : ℝ)*base73 + (1731716561779910521/92187500000000000000000000000000 : ℝ)*base75 + (1858401090103348021/92187500000000000000000000000000 : ℝ)*base77 + (2225304703356473021/92187500000000000000000000000000 : ℝ)*base79 + (131120169836949/29500000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3551077/625000000000000000000 : ℝ)*base89 + (3551077/625000000000000000000 : ℝ)*base91 + (3551077/625000000000000000000 : ℝ)*base93 + (1/50000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1377_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3993/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10993/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14979/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1377_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1377_s4_0 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2013886823/10000000000 : ℝ)*x 0 + (1353223269/2500000000 : ℝ)*x 1 + (1310945011/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2013886823/10000000000 : ℝ)^4337 ≤ (12272200551011/100000000000000 : ℝ)^3313 := by
    have hnat : (2013886823 : ℕ)^4337*100000000000000^3313 ≤ 12272200551011^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2013886823 10000000000 12272200551011 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353223269/2500000000 : ℝ)^4337 ≤ (11193770170431/25000000000000 : ℝ)^3313 := by
    have hnat : (1353223269 : ℕ)^4337*25000000000000^3313 ≤ 11193770170431^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353223269 2500000000 11193770170431 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310945011/2500000000 : ℝ)^4337 ≤ (21476359376227/50000000000000 : ℝ)^3313 := by
    have hnat : (1310945011 : ℕ)^4337*50000000000000^3313 ≤ 21476359376227^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310945011 2500000000 21476359376227 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2013886823/10000000000 : ℝ), (1353223269/2500000000 : ℝ), (1310945011/2500000000 : ℝ)] ![(12272200551011/100000000000000 : ℝ), (11193770170431/25000000000000 : ℝ), (21476359376227/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2013886823/10000000000 : ℝ)|^4337 ≤ (12272200551011/100000000000000 : ℝ)^3313
        have hw : |(-2013886823/10000000000 : ℝ)|=(2013886823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353223269/2500000000 : ℝ)|^4337 ≤ (11193770170431/25000000000000 : ℝ)^3313
        have hw : |(1353223269/2500000000 : ℝ)|=(1353223269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310945011/2500000000 : ℝ)|^4337 ≤ (21476359376227/50000000000000 : ℝ)^3313
        have hw : |(1310945011/2500000000 : ℝ)|=(1310945011/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s4_1 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348877523/10000000000 : ℝ)*x 0 + (-2100059953/10000000000 : ℝ)*x 1 + (2621890147/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348877523/10000000000 : ℝ)^4337 ≤ (8816629628631/20000000000000 : ℝ)^3313 := by
    have hnat : (5348877523 : ℕ)^4337*20000000000000^3313 ≤ 8816629628631^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348877523 10000000000 8816629628631 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2100059953/10000000000 : ℝ)^4337 ≤ (6482065200437/50000000000000 : ℝ)^3313 := by
    have hnat : (2100059953 : ℕ)^4337*50000000000000^3313 ≤ 6482065200437^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100059953 10000000000 6482065200437 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621890147/5000000000 : ℝ)^4337 ≤ (42952721433191/100000000000000 : ℝ)^3313 := by
    have hnat : (2621890147 : ℕ)^4337*100000000000000^3313 ≤ 42952721433191^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621890147 5000000000 42952721433191 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348877523/10000000000 : ℝ), (-2100059953/10000000000 : ℝ), (2621890147/5000000000 : ℝ)] ![(8816629628631/20000000000000 : ℝ), (6482065200437/50000000000000 : ℝ), (42952721433191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348877523/10000000000 : ℝ)|^4337 ≤ (8816629628631/20000000000000 : ℝ)^3313
        have hw : |(5348877523/10000000000 : ℝ)|=(5348877523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2100059953/10000000000 : ℝ)|^4337 ≤ (6482065200437/50000000000000 : ℝ)^3313
        have hw : |(-2100059953/10000000000 : ℝ)|=(2100059953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621890147/5000000000 : ℝ)|^4337 ≤ (42952721433191/100000000000000 : ℝ)^3313
        have hw : |(2621890147/5000000000 : ℝ)|=(2621890147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s4_2 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (6686097/12500000 : ℝ)*x 0 + (5243779941/10000000000 : ℝ)*x 1 + (-2100060319/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (6686097/12500000 : ℝ)^4337 ≤ (22041574486951/50000000000000 : ℝ)^3313 := by
    have hnat : (6686097 : ℕ)^4337*50000000000000^3313 ≤ 22041574486951^3313*12500000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      6686097 12500000 22041574486951 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243779941/10000000000 : ℝ)^4337 ≤ (42952717647991/100000000000000 : ℝ)^3313 := by
    have hnat : (5243779941 : ℕ)^4337*100000000000000^3313 ≤ 42952717647991^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243779941 10000000000 42952717647991 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2100060319/10000000000 : ℝ)^4337 ≤ (12964133358619/100000000000000 : ℝ)^3313 := by
    have hnat : (2100060319 : ℕ)^4337*100000000000000^3313 ≤ 12964133358619^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100060319 10000000000 12964133358619 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(6686097/12500000 : ℝ), (5243779941/10000000000 : ℝ), (-2100060319/10000000000 : ℝ)] ![(22041574486951/50000000000000 : ℝ), (42952717647991/100000000000000 : ℝ), (12964133358619/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(6686097/12500000 : ℝ)|^4337 ≤ (22041574486951/50000000000000 : ℝ)^3313
        have hw : |(6686097/12500000 : ℝ)|=(6686097/12500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243779941/10000000000 : ℝ)|^4337 ≤ (42952717647991/100000000000000 : ℝ)^3313
        have hw : |(5243779941/10000000000 : ℝ)|=(5243779941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2100060319/10000000000 : ℝ)|^4337 ≤ (12964133358619/100000000000000 : ℝ)^3313
        have hw : |(-2100060319/10000000000 : ℝ)|=(2100060319/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s4_3 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158706669/5000000000 : ℝ)*x 0 + (2070699463/5000000000 : ℝ)*x 1 + (281268071/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158706669/5000000000 : ℝ)^4337 ≤ (33302479575127/100000000000000 : ℝ)^3313 := by
    have hnat : (2158706669 : ℕ)^4337*100000000000000^3313 ≤ 33302479575127^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158706669 5000000000 33302479575127 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070699463/5000000000 : ℝ)^4337 ≤ (31536450172357/100000000000000 : ℝ)^3313 := by
    have hnat : (2070699463 : ℕ)^4337*100000000000000^3313 ≤ 31536450172357^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070699463 5000000000 31536450172357 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (281268071/625000000 : ℝ)^4337 ≤ (17580535120097/50000000000000 : ℝ)^3313 := by
    have hnat : (281268071 : ℕ)^4337*50000000000000^3313 ≤ 17580535120097^3313*625000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      281268071 625000000 17580535120097 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158706669/5000000000 : ℝ), (2070699463/5000000000 : ℝ), (281268071/625000000 : ℝ)] ![(33302479575127/100000000000000 : ℝ), (31536450172357/100000000000000 : ℝ), (17580535120097/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158706669/5000000000 : ℝ)|^4337 ≤ (33302479575127/100000000000000 : ℝ)^3313
        have hw : |(2158706669/5000000000 : ℝ)|=(2158706669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2070699463/5000000000 : ℝ)|^4337 ≤ (31536450172357/100000000000000 : ℝ)^3313
        have hw : |(2070699463/5000000000 : ℝ)|=(2070699463/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(281268071/625000000 : ℝ)|^4337 ≤ (17580535120097/50000000000000 : ℝ)^3313
        have hw : |(281268071/625000000 : ℝ)|=(281268071/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s4_4 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-503474849/2500000000 : ℝ)*x 0 + (2622200581/5000000000 : ℝ)*x 1 + (5412268737/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (503474849/2500000000 : ℝ)^4337 ≤ (3068075212393/25000000000000 : ℝ)^3313 := by
    have hnat : (503474849 : ℕ)^4337*25000000000000^3313 ≤ 3068075212393^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      503474849 2500000000 3068075212393 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622200581/5000000000 : ℝ)^4337 ≤ (859187581801/2000000000000 : ℝ)^3313 := by
    have hnat : (2622200581 : ℕ)^4337*2000000000000^3313 ≤ 859187581801^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622200581 5000000000 859187581801 2000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5412268737/10000000000 : ℝ)^4337 ≤ (349752500347/781250000000 : ℝ)^3313 := by
    have hnat : (5412268737 : ℕ)^4337*781250000000^3313 ≤ 349752500347^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5412268737 10000000000 349752500347 781250000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-503474849/2500000000 : ℝ), (2622200581/5000000000 : ℝ), (5412268737/10000000000 : ℝ)] ![(3068075212393/25000000000000 : ℝ), (859187581801/2000000000000 : ℝ), (349752500347/781250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-503474849/2500000000 : ℝ)|^4337 ≤ (3068075212393/25000000000000 : ℝ)^3313
        have hw : |(-503474849/2500000000 : ℝ)|=(503474849/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622200581/5000000000 : ℝ)|^4337 ≤ (859187581801/2000000000000 : ℝ)^3313
        have hw : |(2622200581/5000000000 : ℝ)|=(2622200581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5412268737/10000000000 : ℝ)|^4337 ≤ (349752500347/781250000000 : ℝ)^3313
        have hw : |(5412268737/10000000000 : ℝ)|=(5412268737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s4_5 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652573729/5000000000 : ℝ)*x 0 + (-15090401/78125000 : ℝ)*x 1 + (169133401/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652573729/5000000000 : ℝ)^4337 ≤ (43611945245323/100000000000000 : ℝ)^3313 := by
    have hnat : (2652573729 : ℕ)^4337*100000000000000^3313 ≤ 43611945245323^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652573729 5000000000 43611945245323 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15090401/78125000 : ℝ)^4337 ≤ (363116676997/3125000000000 : ℝ)^3313 := by
    have hnat : (15090401 : ℕ)^4337*3125000000000^3313 ≤ 363116676997^3313*78125000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15090401 78125000 363116676997 3125000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (169133401/312500000 : ℝ)^4337 ≤ (22384160536551/50000000000000 : ℝ)^3313 := by
    have hnat : (169133401 : ℕ)^4337*50000000000000^3313 ≤ 22384160536551^3313*312500000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      169133401 312500000 22384160536551 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652573729/5000000000 : ℝ), (-15090401/78125000 : ℝ), (169133401/312500000 : ℝ)] ![(43611945245323/100000000000000 : ℝ), (363116676997/3125000000000 : ℝ), (22384160536551/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652573729/5000000000 : ℝ)|^4337 ≤ (43611945245323/100000000000000 : ℝ)^3313
        have hw : |(2652573729/5000000000 : ℝ)|=(2652573729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-15090401/78125000 : ℝ)|^4337 ≤ (363116676997/3125000000000 : ℝ)^3313
        have hw : |(-15090401/78125000 : ℝ)|=(15090401/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(169133401/312500000 : ℝ)|^4337 ≤ (22384160536551/50000000000000 : ℝ)^3313
        have hw : |(169133401/312500000 : ℝ)|=(169133401/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s4_6 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305147487/10000000000 : ℝ)*x 0 + (1082453751/2000000000 : ℝ)*x 1 + (-386314279/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305147487/10000000000 : ℝ)^4337 ≤ (43611945557409/100000000000000 : ℝ)^3313 := by
    have hnat : (5305147487 : ℕ)^4337*100000000000000^3313 ≤ 43611945557409^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305147487 10000000000 43611945557409 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1082453751/2000000000 : ℝ)^4337 ≤ (1790732809573/4000000000000 : ℝ)^3313 := by
    have hnat : (1082453751 : ℕ)^4337*4000000000000^3313 ≤ 1790732809573^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082453751 2000000000 1790732809573 4000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (386314279/2000000000 : ℝ)^4337 ≤ (11619734191533/100000000000000 : ℝ)^3313 := by
    have hnat : (386314279 : ℕ)^4337*100000000000000^3313 ≤ 11619734191533^3313*2000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386314279 2000000000 11619734191533 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305147487/10000000000 : ℝ), (1082453751/2000000000 : ℝ), (-386314279/2000000000 : ℝ)] ![(43611945557409/100000000000000 : ℝ), (1790732809573/4000000000000 : ℝ), (11619734191533/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305147487/10000000000 : ℝ)|^4337 ≤ (43611945557409/100000000000000 : ℝ)^3313
        have hw : |(5305147487/10000000000 : ℝ)|=(5305147487/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1082453751/2000000000 : ℝ)|^4337 ≤ (1790732809573/4000000000000 : ℝ)^3313
        have hw : |(1082453751/2000000000 : ℝ)|=(1082453751/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-386314279/2000000000 : ℝ)|^4337 ≤ (11619734191533/100000000000000 : ℝ)^3313
        have hw : |(-386314279/2000000000 : ℝ)|=(386314279/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s4_7 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2158719933/5000000000 : ℝ)*x 0 + (4498970907/10000000000 : ℝ)*x 1 + (4142724457/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2158719933/5000000000 : ℝ)^4337 ≤ (1665137372311/5000000000000 : ℝ)^3313 := by
    have hnat : (2158719933 : ℕ)^4337*5000000000000^3313 ≤ 1665137372311^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2158719933 5000000000 1665137372311 5000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4498970907/10000000000 : ℝ)^4337 ≤ (8786897009357/25000000000000 : ℝ)^3313 := by
    have hnat : (4498970907 : ℕ)^4337*25000000000000^3313 ≤ 8786897009357^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4498970907 10000000000 8786897009357 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4142724457/10000000000 : ℝ)^4337 ≤ (31549664500739/100000000000000 : ℝ)^3313 := by
    have hnat : (4142724457 : ℕ)^4337*100000000000000^3313 ≤ 31549664500739^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4142724457 10000000000 31549664500739 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2158719933/5000000000 : ℝ), (4498970907/10000000000 : ℝ), (4142724457/10000000000 : ℝ)] ![(1665137372311/5000000000000 : ℝ), (8786897009357/25000000000000 : ℝ), (31549664500739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2158719933/5000000000 : ℝ)|^4337 ≤ (1665137372311/5000000000000 : ℝ)^3313
        have hw : |(2158719933/5000000000 : ℝ)|=(2158719933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4498970907/10000000000 : ℝ)|^4337 ≤ (8786897009357/25000000000000 : ℝ)^3313
        have hw : |(4498970907/10000000000 : ℝ)|=(4498970907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4142724457/10000000000 : ℝ)|^4337 ≤ (31549664500739/100000000000000 : ℝ)^3313
        have hw : |(4142724457/10000000000 : ℝ)|=(4142724457/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1377_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (1119/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1477/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14979/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10993/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14979/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10993/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14979/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10993/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14979/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10993/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14979/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10993/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14979/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10993/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10993/100000 : ℝ) ^ (271/64 : ℝ) ≤ (8704153229252817/100000000000000000000 : ℝ) := by
    have hpowers : (10993/100000 : ℝ)^271 ≤ (8704153229252817/100000000000000000000 : ℝ)^64 := by
      have hnat : (10993 : ℕ)^271*100000000000000000000^64 ≤ 8704153229252817^64*100000^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10993 100000 8704153229252817 100000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10993/100000 : ℝ)) (X := (8704153229252817/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hpowhi : (14979/100000 : ℝ) ^ (271/64 : ℝ) ≤ (32261538119507409/100000000000000000000 : ℝ) := by
    have hpowers : (14979/100000 : ℝ)^271 ≤ (32261538119507409/100000000000000000000 : ℝ)^64 := by
      have hnat : (14979 : ℕ)^271*100000000000000000000^64 ≤ 32261538119507409^64*100000^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14979 100000 32261538119507409 100000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14979/100000 : ℝ)) (X := (32261538119507409/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008704153229252817/50000000000000000000 : ℝ) ≤ (10000411091345837/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (50008704153229252817/50000000000000000000 : ℝ)^64 ≤ (10000411091345837/10000000000000000 : ℝ)^271 := by
      have hnat : (50008704153229252817 : ℕ)^64*10000000000000000^271 ≤ 10000411091345837^271*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008704153229252817 50000000000000000000 10000411091345837 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000411091345837/10000000000000000 : ℝ)) (X := (50008704153229252817/50000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50020482845674380113/50000000000000000000 : ℝ) ≤ (1000096730411399/1000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (50020482845674380113/50000000000000000000 : ℝ)^64 ≤ (1000096730411399/1000000000000000 : ℝ)^271 := by
      have hnat : (50020482845674380113 : ℕ)^64*1000000000000000^271 ≤ 1000096730411399^271*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50020482845674380113 50000000000000000000 1000096730411399 1000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000096730411399/1000000000000000 : ℝ)) (X := (50020482845674380113/50000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (50032261538119507409/50000000000000000000 : ℝ) ≤ (10001523516882143/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (50032261538119507409/50000000000000000000 : ℝ)^64 ≤ (10001523516882143/10000000000000000 : ℝ)^271 := by
      have hnat : (50032261538119507409 : ℕ)^64*10000000000000000^271 ≤ 10001523516882143^271*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50032261538119507409 50000000000000000000 10001523516882143 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001523516882143/10000000000000000 : ℝ)) (X := (50032261538119507409/50000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8704153229252817/100000000000000000000 : ℝ) ≤ ((4981176214522986803/4982500000000000000 : ℝ)+2*(556212768153/398600000000000 : ℝ)*(10993/100000 : ℝ))^(271/64 : ℝ) := by
    rw [show (4981176214522986803/4982500000000000000 : ℝ)+2*(556212768153/398600000000000 : ℝ)*(10993/100000 : ℝ)=(10000411091345837/10000000000000000 : ℝ) by norm_num, show 1+2*(8704153229252817/100000000000000000000 : ℝ)=(50008704153229252817/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(32261538119507409/100000000000000000000 : ℝ)+(8704153229252817/100000000000000000000 : ℝ) ≤ ((4981176214522986803/4982500000000000000 : ℝ)+(556212768153/398600000000000 : ℝ)*((14979/100000 : ℝ)+(10993/100000 : ℝ)))^(271/64 : ℝ) := by
    rw [show (4981176214522986803/4982500000000000000 : ℝ)+(556212768153/398600000000000 : ℝ)*((14979/100000 : ℝ)+(10993/100000 : ℝ))=(1000096730411399/1000000000000000 : ℝ) by norm_num, show 1+(32261538119507409/100000000000000000000 : ℝ)+(8704153229252817/100000000000000000000 : ℝ)=(50020482845674380113/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(32261538119507409/100000000000000000000 : ℝ) ≤ ((4981176214522986803/4982500000000000000 : ℝ)+2*(556212768153/398600000000000 : ℝ)*(14979/100000 : ℝ))^(271/64 : ℝ) := by
    rw [show (4981176214522986803/4982500000000000000 : ℝ)+2*(556212768153/398600000000000 : ℝ)*(14979/100000 : ℝ)=(10001523516882143/10000000000000000 : ℝ) by norm_num, show 1+2*(32261538119507409/100000000000000000000 : ℝ)=(50032261538119507409/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4981176214522986803/4982500000000000000 : ℝ)*(X 1 0+X 2 0)+(556212768153/398600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (10993/100000 : ℝ)) (hi := (14979/100000 : ℝ)) (c := (4981176214522986803/4982500000000000000 : ℝ)) (alpha := (556212768153/398600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4981176214522986803/4982500000000000000 : ℝ)*(X 0 1+X 2 1)+(556212768153/398600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (10993/100000 : ℝ)) (hi := (14979/100000 : ℝ)) (c := (4981176214522986803/4982500000000000000 : ℝ)) (alpha := (556212768153/398600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4981176214522986803/4982500000000000000 : ℝ)*(X 0 2+X 1 2)+(556212768153/398600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (10993/100000 : ℝ)) (hi := (14979/100000 : ℝ)) (c := (4981176214522986803/4982500000000000000 : ℝ)) (alpha := (556212768153/398600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2013886823/10000000000 : ℝ)*X 0 0+(1353223269/2500000000 : ℝ)*X 0 1+(1310945011/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348877523/10000000000 : ℝ)*X 1 0+(-2100059953/10000000000 : ℝ)*X 1 1+(2621890147/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((6686097/12500000 : ℝ)*X 2 0+(5243779941/10000000000 : ℝ)*X 2 1+(-2100060319/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2158706669/5000000000 : ℝ)*X 0 0+(2070699463/5000000000 : ℝ)*X 0 1+(281268071/625000000 : ℝ)*X 0 2+(2158706669/5000000000 : ℝ)*X 1 0+(2070699463/5000000000 : ℝ)*X 1 1+(281268071/625000000 : ℝ)*X 1 2+(2158706669/5000000000 : ℝ)*X 2 0+(2070699463/5000000000 : ℝ)*X 2 1+(281268071/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-503474849/2500000000 : ℝ)*X 0 0+(2622200581/5000000000 : ℝ)*X 0 1+(5412268737/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652573729/5000000000 : ℝ)*X 1 0+(-15090401/78125000 : ℝ)*X 1 1+(169133401/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305147487/10000000000 : ℝ)*X 2 0+(1082453751/2000000000 : ℝ)*X 2 1+(-386314279/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2158719933/5000000000 : ℝ)*X 0 0+(4498970907/10000000000 : ℝ)*X 0 1+(4142724457/10000000000 : ℝ)*X 0 2+(2158719933/5000000000 : ℝ)*X 1 0+(4498970907/10000000000 : ℝ)*X 1 1+(4142724457/10000000000 : ℝ)*X 1 2+(2158719933/5000000000 : ℝ)*X 2 0+(4498970907/10000000000 : ℝ)*X 2 1+(4142724457/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (150612130163761108043115843/62281250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (30998723/6250000000000 : ℝ)*(base19) + (601170793/100000000000000 : ℝ)*(base23) + (290765709/100000000000000 : ℝ)*(upper3) + (620527/2500000000000 : ℝ)*(lower4) + (2174902397567227/50000000000000 : ℝ)*(major0) + (2174902397567227/50000000000000 : ℝ)*(major1) + (2174902397567227/50000000000000 : ℝ)*(major2) + (2956610669688017/50000000000000 : ℝ)*(sp0) + (5913226360902819/100000000000000 : ℝ)*(sp1) + (739152879283081/12500000000000 : ℝ)*(sp2) + (2786372916879167/100000000000000 : ℝ)*(sp3) + (2758753177/50000000000000 : ℝ)*(sp4) + (3221446947/100000000000000 : ℝ)*(sp6) + (9735898743/100000000000000 : ℝ)*(sp7) + (278638265277791/10000000000000 : ℝ)*(f.failure) + (5913226856882387/100000000000000 : ℝ)*(f.sum) + (91797643891861/9965000000000000000000000000 : ℝ)*base65 + (4650003310286432219/249125000000000000000000000000000 : ℝ)*base68 + (4746250059002182219/249125000000000000000000000000000 : ℝ)*base70 + (2845288683383682219/249125000000000000000000000000000 : ℝ)*base72 + (22167392557991/9965000000000000000000000000 : ℝ)*base73 + (269351580340817781/249125000000000000000000000000000 : ℝ)*base75 + (5088290516688182219/249125000000000000000000000000000 : ℝ)*base78 + (1946285265568057219/249125000000000000000000000000000 : ℝ)*base80 + (30157663883741/9965000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (236343/125000000000000000000 : ℝ)*base89 + (236343/125000000000000000000 : ℝ)*base91 + (236343/125000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (8653706105950304980561053/1946289062500000000000000000000 : ℝ) := by norm_num
    linear_combination (405880733/50000000000000 : ℝ)*(base19) + (833532621/100000000000000 : ℝ)*(base23) + (2411641/50000000000000 : ℝ)*(upper2) + (13527339/12500000000000 : ℝ)*(upper3) + (59388429/50000000000000 : ℝ)*(upper5) + (547757652126797/12500000000000 : ℝ)*(major0) + (547757652126797/12500000000000 : ℝ)*(major1) + (547757652126797/12500000000000 : ℝ)*(major2) + (19039150143/100000000000000 : ℝ)*(sp1) + (332537183/2000000000000 : ℝ)*(sp2) + (5957076927794487/100000000000000 : ℝ)*(sp4) + (5957057076882879/100000000000000 : ℝ)*(sp5) + (1489264866850679/25000000000000 : ℝ)*(sp6) + (2807045358025611/100000000000000 : ℝ)*(sp7) + (2807045358025611/100000000000000 : ℝ)*(f.failure) + (5957076927794487/100000000000000 : ℝ)*(f.sum) + (12241829741677/4982500000000000000000000000 : ℝ)*base65 + (786521277665296259/62281250000000000000000000000000 : ℝ)*base68 + (469984801211390009/62281250000000000000000000000000 : ℝ)*base70 + (240228918134608759/62281250000000000000000000000000 : ℝ)*base72 + (11135583492863/4982500000000000000000000000 : ℝ)*base74 + (454150195175233759/62281250000000000000000000000000 : ℝ)*base76 + (383274447779359991/62281250000000000000000000000000 : ℝ)*base77 + (104645257080078741/62281250000000000000000000000000 : ℝ)*base79 + (27684234416741/9965000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1320797/1250000000000000000000 : ℝ)*base90 + (1320797/1250000000000000000000 : ℝ)*base92 + (1320797/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1377_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14979/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10993/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1377_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1377_s5_0 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014081897/10000000000 : ℝ)*x 0 + (541118357/1000000000 : ℝ)*x 1 + (32783507/62500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014081897/10000000000 : ℝ)^4337 ≤ (12273756736137/100000000000000 : ℝ)^3313 := by
    have hnat : (2014081897 : ℕ)^4337*100000000000000^3313 ≤ 12273756736137^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014081897 10000000000 12273756736137 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541118357/1000000000 : ℝ)^4337 ≤ (22378284958829/50000000000000 : ℝ)^3313 := by
    have hnat : (541118357 : ℕ)^4337*50000000000000^3313 ≤ 22378284958829^3313*1000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541118357 1000000000 22378284958829 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32783507/62500000 : ℝ)^4337 ≤ (1718786933491/4000000000000 : ℝ)^3313 := by
    have hnat : (32783507 : ℕ)^4337*4000000000000^3313 ≤ 1718786933491^3313*62500000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32783507 62500000 1718786933491 4000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014081897/10000000000 : ℝ), (541118357/1000000000 : ℝ), (32783507/62500000 : ℝ)] ![(12273756736137/100000000000000 : ℝ), (22378284958829/50000000000000 : ℝ), (1718786933491/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014081897/10000000000 : ℝ)|^4337 ≤ (12273756736137/100000000000000 : ℝ)^3313
        have hw : |(-2014081897/10000000000 : ℝ)|=(2014081897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(541118357/1000000000 : ℝ)|^4337 ≤ (22378284958829/50000000000000 : ℝ)^3313
        have hw : |(541118357/1000000000 : ℝ)|=(541118357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32783507/62500000 : ℝ)|^4337 ≤ (1718786933491/4000000000000 : ℝ)^3313
        have hw : |(32783507/62500000 : ℝ)|=(32783507/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s5_1 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5348438957/10000000000 : ℝ)*x 0 + (-2098547543/10000000000 : ℝ)*x 1 + (524536117/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5348438957/10000000000 : ℝ)^4337 ≤ (8815683310009/20000000000000 : ℝ)^3313 := by
    have hnat : (5348438957 : ℕ)^4337*20000000000000^3313 ≤ 8815683310009^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5348438957 10000000000 8815683310009 20000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2098547543/10000000000 : ℝ)^4337 ≤ (12951909565963/100000000000000 : ℝ)^3313 := by
    have hnat : (2098547543 : ℕ)^4337*100000000000000^3313 ≤ 12951909565963^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2098547543 10000000000 12951909565963 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524536117/1000000000 : ℝ)^4337 ≤ (671401154273/1562500000000 : ℝ)^3313 := by
    have hnat : (524536117 : ℕ)^4337*1562500000000^3313 ≤ 671401154273^3313*1000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524536117 1000000000 671401154273 1562500000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5348438957/10000000000 : ℝ), (-2098547543/10000000000 : ℝ), (524536117/1000000000 : ℝ)] ![(8815683310009/20000000000000 : ℝ), (12951909565963/100000000000000 : ℝ), (671401154273/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5348438957/10000000000 : ℝ)|^4337 ≤ (8815683310009/20000000000000 : ℝ)^3313
        have hw : |(5348438957/10000000000 : ℝ)|=(5348438957/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2098547543/10000000000 : ℝ)|^4337 ≤ (12951909565963/100000000000000 : ℝ)^3313
        have hw : |(-2098547543/10000000000 : ℝ)|=(2098547543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(524536117/1000000000 : ℝ)|^4337 ≤ (671401154273/1562500000000 : ℝ)^3313
        have hw : |(524536117/1000000000 : ℝ)|=(524536117/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s5_2 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337109707/2500000000 : ℝ)*x 0 + (2622680629/5000000000 : ℝ)*x 1 + (-1049273799/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337109707/2500000000 : ℝ)^4337 ≤ (4407841515831/10000000000000 : ℝ)^3313 := by
    have hnat : (1337109707 : ℕ)^4337*10000000000000^3313 ≤ 4407841515831^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337109707 2500000000 4407841515831 10000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622680629/5000000000 : ℝ)^4337 ≤ (42969674817179/100000000000000 : ℝ)^3313 := by
    have hnat : (2622680629 : ℕ)^4337*100000000000000^3313 ≤ 42969674817179^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622680629 5000000000 42969674817179 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1049273799/5000000000 : ℝ)^4337 ≤ (6475955005167/50000000000000 : ℝ)^3313 := by
    have hnat : (1049273799 : ℕ)^4337*50000000000000^3313 ≤ 6475955005167^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049273799 5000000000 6475955005167 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337109707/2500000000 : ℝ), (2622680629/5000000000 : ℝ), (-1049273799/5000000000 : ℝ)] ![(4407841515831/10000000000000 : ℝ), (42969674817179/100000000000000 : ℝ), (6475955005167/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337109707/2500000000 : ℝ)|^4337 ≤ (4407841515831/10000000000000 : ℝ)^3313
        have hw : |(1337109707/2500000000 : ℝ)|=(1337109707/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622680629/5000000000 : ℝ)|^4337 ≤ (42969674817179/100000000000000 : ℝ)^3313
        have hw : |(2622680629/5000000000 : ℝ)|=(2622680629/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1049273799/5000000000 : ℝ)|^4337 ≤ (6475955005167/50000000000000 : ℝ)^3313
        have hw : |(-1049273799/5000000000 : ℝ)|=(1049273799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s5_3 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4317530621/10000000000 : ℝ)*x 0 + (2072438367/5000000000 : ℝ)*x 1 + (2248391437/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317530621/10000000000 : ℝ)^4337 ≤ (1665183193223/5000000000000 : ℝ)^3313 := by
    have hnat : (4317530621 : ℕ)^4337*5000000000000^3313 ≤ 1665183193223^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317530621 10000000000 1665183193223 5000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2072438367/5000000000 : ℝ)^4337 ≤ (31571123512209/100000000000000 : ℝ)^3313 := by
    have hnat : (2072438367 : ℕ)^4337*100000000000000^3313 ≤ 31571123512209^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2072438367 5000000000 31571123512209 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2248391437/5000000000 : ℝ)^4337 ≤ (35125212599189/100000000000000 : ℝ)^3313 := by
    have hnat : (2248391437 : ℕ)^4337*100000000000000^3313 ≤ 35125212599189^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2248391437 5000000000 35125212599189 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317530621/10000000000 : ℝ), (2072438367/5000000000 : ℝ), (2248391437/5000000000 : ℝ)] ![(1665183193223/5000000000000 : ℝ), (31571123512209/100000000000000 : ℝ), (35125212599189/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317530621/10000000000 : ℝ)|^4337 ≤ (1665183193223/5000000000000 : ℝ)^3313
        have hw : |(4317530621/10000000000 : ℝ)|=(4317530621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2072438367/5000000000 : ℝ)|^4337 ≤ (31571123512209/100000000000000 : ℝ)^3313
        have hw : |(2072438367/5000000000 : ℝ)|=(2072438367/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2248391437/5000000000 : ℝ)|^4337 ≤ (35125212599189/100000000000000 : ℝ)^3313
        have hw : |(2248391437/5000000000 : ℝ)|=(2248391437/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s5_4 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2014093709/10000000000 : ℝ)*x 0 + (5245958523/10000000000 : ℝ)*x 1 + (5410583163/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2014093709/10000000000 : ℝ)^4337 ≤ (12273850966791/100000000000000 : ℝ)^3313 := by
    have hnat : (2014093709 : ℕ)^4337*100000000000000^3313 ≤ 12273850966791^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2014093709 10000000000 12273850966791 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245958523/10000000000 : ℝ)^4337 ≤ (21488039983973/50000000000000 : ℝ)^3313 := by
    have hnat : (5245958523 : ℕ)^4337*50000000000000^3313 ≤ 21488039983973^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245958523 10000000000 21488039983973 50000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410583163/10000000000 : ℝ)^4337 ≤ (44750069057649/100000000000000 : ℝ)^3313 := by
    have hnat : (5410583163 : ℕ)^4337*100000000000000^3313 ≤ 44750069057649^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410583163 10000000000 44750069057649 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2014093709/10000000000 : ℝ), (5245958523/10000000000 : ℝ), (5410583163/10000000000 : ℝ)] ![(12273850966791/100000000000000 : ℝ), (21488039983973/50000000000000 : ℝ), (44750069057649/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2014093709/10000000000 : ℝ)|^4337 ≤ (12273850966791/100000000000000 : ℝ)^3313
        have hw : |(-2014093709/10000000000 : ℝ)|=(2014093709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245958523/10000000000 : ℝ)|^4337 ≤ (21488039983973/50000000000000 : ℝ)^3313
        have hw : |(5245958523/10000000000 : ℝ)|=(5245958523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410583163/10000000000 : ℝ)|^4337 ≤ (44750069057649/100000000000000 : ℝ)^3313
        have hw : |(5410583163/10000000000 : ℝ)|=(5410583163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s5_5 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2652779793/5000000000 : ℝ)*x 0 + (-1933325579/10000000000 : ℝ)*x 1 + (5410583169/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652779793/5000000000 : ℝ)^4337 ≤ (43616380446461/100000000000000 : ℝ)^3313 := by
    have hnat : (2652779793 : ℕ)^4337*100000000000000^3313 ≤ 43616380446461^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652779793 5000000000 43616380446461 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1933325579/10000000000 : ℝ)^4337 ≤ (11633550419683/100000000000000 : ℝ)^3313 := by
    have hnat : (1933325579 : ℕ)^4337*100000000000000^3313 ≤ 11633550419683^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1933325579 10000000000 11633550419683 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5410583169/10000000000 : ℝ)^4337 ≤ (11187517280653/25000000000000 : ℝ)^3313 := by
    have hnat : (5410583169 : ℕ)^4337*25000000000000^3313 ≤ 11187517280653^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5410583169 10000000000 11187517280653 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652779793/5000000000 : ℝ), (-1933325579/10000000000 : ℝ), (5410583169/10000000000 : ℝ)] ![(43616380446461/100000000000000 : ℝ), (11633550419683/100000000000000 : ℝ), (11187517280653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652779793/5000000000 : ℝ)|^4337 ≤ (43616380446461/100000000000000 : ℝ)^3313
        have hw : |(2652779793/5000000000 : ℝ)|=(2652779793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1933325579/10000000000 : ℝ)|^4337 ≤ (11633550419683/100000000000000 : ℝ)^3313
        have hw : |(-1933325579/10000000000 : ℝ)|=(1933325579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5410583169/10000000000 : ℝ)|^4337 ≤ (11187517280653/25000000000000 : ℝ)^3313
        have hw : |(5410583169/10000000000 : ℝ)|=(5410583169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s5_6 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1326389891/2500000000 : ℝ)*x 0 + (2705291593/5000000000 : ℝ)*x 1 + (-966662793/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1326389891/2500000000 : ℝ)^4337 ≤ (43616380209701/100000000000000 : ℝ)^3313 := by
    have hnat : (1326389891 : ℕ)^4337*100000000000000^3313 ≤ 43616380209701^3313*2500000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1326389891 2500000000 43616380209701 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2705291593/5000000000 : ℝ)^4337 ≤ (1790002772267/4000000000000 : ℝ)^3313 := by
    have hnat : (2705291593 : ℕ)^4337*4000000000000^3313 ≤ 1790002772267^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2705291593 5000000000 1790002772267 4000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966662793/5000000000 : ℝ)^4337 ≤ (1454193809353/12500000000000 : ℝ)^3313 := by
    have hnat : (966662793 : ℕ)^4337*12500000000000^3313 ≤ 1454193809353^3313*5000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966662793 5000000000 1454193809353 12500000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1326389891/2500000000 : ℝ), (2705291593/5000000000 : ℝ), (-966662793/5000000000 : ℝ)] ![(43616380209701/100000000000000 : ℝ), (1790002772267/4000000000000 : ℝ), (1454193809353/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1326389891/2500000000 : ℝ)|^4337 ≤ (43616380209701/100000000000000 : ℝ)^3313
        have hw : |(1326389891/2500000000 : ℝ)|=(1326389891/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2705291593/5000000000 : ℝ)|^4337 ≤ (1790002772267/4000000000000 : ℝ)^3313
        have hw : |(2705291593/5000000000 : ℝ)|=(2705291593/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-966662793/5000000000 : ℝ)|^4337 ≤ (1454193809353/12500000000000 : ℝ)^3313
        have hw : |(-966662793/5000000000 : ℝ)|=(966662793/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1377_s5_7 (p : ℝ) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4317555997/10000000000 : ℝ)*x 0 + (4495515273/10000000000 : ℝ)*x 1 + (4146150853/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4317555997/10000000000 : ℝ)^4337 ≤ (33303920105173/100000000000000 : ℝ)^3313 := by
    have hnat : (4317555997 : ℕ)^4337*100000000000000^3313 ≤ 33303920105173^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4317555997 10000000000 33303920105173 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4495515273/10000000000 : ℝ)^4337 ≤ (8778062823913/25000000000000 : ℝ)^3313 := by
    have hnat : (4495515273 : ℕ)^4337*25000000000000^3313 ≤ 8778062823913^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4495515273 10000000000 8778062823913 25000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4146150853/10000000000 : ℝ)^4337 ≤ (31583828581143/100000000000000 : ℝ)^3313 := by
    have hnat : (4146150853 : ℕ)^4337*100000000000000^3313 ≤ 31583828581143^3313*10000000000^4337 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4146150853 10000000000 31583828581143 100000000000000 4337 3313 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4337/1024 : ℝ)) 4337 3313 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4317555997/10000000000 : ℝ), (4495515273/10000000000 : ℝ), (4146150853/10000000000 : ℝ)] ![(33303920105173/100000000000000 : ℝ), (8778062823913/25000000000000 : ℝ), (31583828581143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4317555997/10000000000 : ℝ)|^4337 ≤ (33303920105173/100000000000000 : ℝ)^3313
        have hw : |(4317555997/10000000000 : ℝ)|=(4317555997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4495515273/10000000000 : ℝ)|^4337 ≤ (8778062823913/25000000000000 : ℝ)^3313
        have hw : |(4495515273/10000000000 : ℝ)|=(4495515273/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4146150853/10000000000 : ℝ)|^4337 ≤ (31583828581143/100000000000000 : ℝ)^3313
        have hw : |(4146150853/10000000000 : ℝ)|=(4146150853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1377_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11223/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7367/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1119/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1119/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1119/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1477/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1119/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1119/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1477/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1119/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1119/10000 : ℝ) ^ (271/64 : ℝ) ≤ (2346010255656931/25000000000000000000 : ℝ) := by
    have hpowers : (1119/10000 : ℝ)^271 ≤ (2346010255656931/25000000000000000000 : ℝ)^64 := by
      have hnat : (1119 : ℕ)^271*25000000000000000000^64 ≤ 2346010255656931^64*10000^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1119 10000 2346010255656931 25000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1119/10000 : ℝ)) (X := (2346010255656931/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hpowhi : (1477/10000 : ℝ) ^ (271/64 : ℝ) ≤ (3039803668898313/10000000000000000000 : ℝ) := by
    have hpowers : (1477/10000 : ℝ)^271 ≤ (3039803668898313/10000000000000000000 : ℝ)^64 := by
      have hnat : (1477 : ℕ)^271*10000000000000000000^64 ≤ 3039803668898313^64*10000^271 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1477 10000 3039803668898313 10000000000000000000 271 64 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1477/10000 : ℝ)) (X := (3039803668898313/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502346010255656931/12500000000000000000 : ℝ) ≤ (5000221599845543/5000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (12502346010255656931/12500000000000000000 : ℝ)^64 ≤ (5000221599845543/5000000000000000 : ℝ)^271 := by
      have hnat : (12502346010255656931 : ℕ)^64*5000000000000000^271 ≤ 5000221599845543^271*12500000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502346010255656931 12500000000000000000 5000221599845543 5000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000221599845543/5000000000000000 : ℝ)) (X := (12502346010255656931/12500000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019891038855805427/50000000000000000000 : ℝ) ≤ (10000939360232039/10000000000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (50019891038855805427/50000000000000000000 : ℝ)^64 ≤ (10000939360232039/10000000000000000 : ℝ)^271 := by
      have hnat : (50019891038855805427 : ℕ)^64*10000000000000000^271 ≤ 10000939360232039^271*50000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019891038855805427 50000000000000000000 10000939360232039 10000000000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000939360232039/10000000000000000 : ℝ)) (X := (50019891038855805427/50000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003039803668898313/5000000000000000000 : ℝ) ≤ (78136215006039/78125000000000 : ℝ) ^ (271/64 : ℝ) := by
    have hpowers : (5003039803668898313/5000000000000000000 : ℝ)^64 ≤ (78136215006039/78125000000000 : ℝ)^271 := by
      have hnat : (5003039803668898313 : ℕ)^64*78125000000000^271 ≤ 78136215006039^271*5000000000000000000^64 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003039803668898313 5000000000000000000 78136215006039 78125000000000 64 271 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (78136215006039/78125000000000 : ℝ)) (X := (5003039803668898313/5000000000000000000 : ℝ)) (by norm_num) 271 64 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2346010255656931/25000000000000000000 : ℝ) ≤ ((1789524129099377987/1790000000000000000 : ℝ)+2*(496160540953/358000000000000 : ℝ)*(1119/10000 : ℝ))^(271/64 : ℝ) := by
    rw [show (1789524129099377987/1790000000000000000 : ℝ)+2*(496160540953/358000000000000 : ℝ)*(1119/10000 : ℝ)=(5000221599845543/5000000000000000 : ℝ) by norm_num, show 1+2*(2346010255656931/25000000000000000000 : ℝ)=(12502346010255656931/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3039803668898313/10000000000000000000 : ℝ)+(2346010255656931/25000000000000000000 : ℝ) ≤ ((1789524129099377987/1790000000000000000 : ℝ)+(496160540953/358000000000000 : ℝ)*((1477/10000 : ℝ)+(1119/10000 : ℝ)))^(271/64 : ℝ) := by
    rw [show (1789524129099377987/1790000000000000000 : ℝ)+(496160540953/358000000000000 : ℝ)*((1477/10000 : ℝ)+(1119/10000 : ℝ))=(10000939360232039/10000000000000000 : ℝ) by norm_num, show 1+(3039803668898313/10000000000000000000 : ℝ)+(2346010255656931/25000000000000000000 : ℝ)=(50019891038855805427/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3039803668898313/10000000000000000000 : ℝ) ≤ ((1789524129099377987/1790000000000000000 : ℝ)+2*(496160540953/358000000000000 : ℝ)*(1477/10000 : ℝ))^(271/64 : ℝ) := by
    rw [show (1789524129099377987/1790000000000000000 : ℝ)+2*(496160540953/358000000000000 : ℝ)*(1477/10000 : ℝ)=(78136215006039/78125000000000 : ℝ) by norm_num, show 1+2*(3039803668898313/10000000000000000000 : ℝ)=(5003039803668898313/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1789524129099377987/1790000000000000000 : ℝ)*(X 1 0+X 2 0)+(496160540953/358000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (1119/10000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (1789524129099377987/1790000000000000000 : ℝ)) (alpha := (496160540953/358000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1789524129099377987/1790000000000000000 : ℝ)*(X 0 1+X 2 1)+(496160540953/358000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (1119/10000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (1789524129099377987/1790000000000000000 : ℝ)) (alpha := (496160540953/358000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1789524129099377987/1790000000000000000 : ℝ)*(X 0 2+X 1 2)+(496160540953/358000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (271/64 : ℝ)) (lo := (1119/10000 : ℝ)) (hi := (1477/10000 : ℝ)) (c := (1789524129099377987/1790000000000000000 : ℝ)) (alpha := (496160540953/358000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2014081897/10000000000 : ℝ)*X 0 0+(541118357/1000000000 : ℝ)*X 0 1+(32783507/62500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5348438957/10000000000 : ℝ)*X 1 0+(-2098547543/10000000000 : ℝ)*X 1 1+(524536117/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337109707/2500000000 : ℝ)*X 2 0+(2622680629/5000000000 : ℝ)*X 2 1+(-1049273799/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4317530621/10000000000 : ℝ)*X 0 0+(2072438367/5000000000 : ℝ)*X 0 1+(2248391437/5000000000 : ℝ)*X 0 2+(4317530621/10000000000 : ℝ)*X 1 0+(2072438367/5000000000 : ℝ)*X 1 1+(2248391437/5000000000 : ℝ)*X 1 2+(4317530621/10000000000 : ℝ)*X 2 0+(2072438367/5000000000 : ℝ)*X 2 1+(2248391437/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2014093709/10000000000 : ℝ)*X 0 0+(5245958523/10000000000 : ℝ)*X 0 1+(5410583163/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652779793/5000000000 : ℝ)*X 1 0+(-1933325579/10000000000 : ℝ)*X 1 1+(5410583169/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1326389891/2500000000 : ℝ)*X 2 0+(2705291593/5000000000 : ℝ)*X 2 1+(-966662793/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4317555997/10000000000 : ℝ)*X 0 0+(4495515273/10000000000 : ℝ)*X 0 1+(4146150853/10000000000 : ℝ)*X 0 2+(4317555997/10000000000 : ℝ)*X 1 0+(4495515273/10000000000 : ℝ)*X 1 1+(4146150853/10000000000 : ℝ)*X 1 2+(4317555997/10000000000 : ℝ)*X 2 0+(4495515273/10000000000 : ℝ)*X 2 1+(4146150853/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1377_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (44256284572851928722603/4475000000000000000000000000 : ℝ) := by norm_num
    linear_combination (77062549/4000000000000 : ℝ)*(base19) + (1749148811/100000000000000 : ℝ)*(base23) + (144582601/50000000000000 : ℝ)*(upper3) + (17094167/100000000000000 : ℝ)*(upper4) + (21602669/12500000000000 : ℝ)*(upper5) + (554521010965571/12500000000000 : ℝ)*(major0) + (554521010965571/12500000000000 : ℝ)*(major1) + (554521010965571/12500000000000 : ℝ)*(major2) + (3015295567122363/50000000000000 : ℝ)*(sp0) + (1206125794463183/20000000000000 : ℝ)*(sp1) + (6030629149730829/100000000000000 : ℝ)*(sp2) + (1420842578326253/50000000000000 : ℝ)*(sp3) + (19882317457/50000000000000 : ℝ)*(sp4) + (3958052247/20000000000000 : ℝ)*(sp7) + (2841704946913741/100000000000000 : ℝ)*(f.failure) + (150765772471991/2500000000000 : ℝ)*(f.sum) + (23897359138349/4475000000000000000000000000 : ℝ)*base66 + (97632096329274423/22375000000000000000000000000000 : ℝ)*base68 + (113401958470725577/22375000000000000000000000000000 : ℝ)*base69 + (68920536044899423/22375000000000000000000000000000 : ℝ)*base72 + (317220764147/559375000000000000000000000 : ℝ)*base73 + (98674410196725577/22375000000000000000000000000000 : ℝ)*base75 + (231701519607774423/22375000000000000000000000000000 : ℝ)*base78 + (18879025150725577/22375000000000000000000000000000 : ℝ)*base79 + (22486775074249/4475000000000000000000000000 : ℝ)*base82 + (1080693/1250000000000000000000 : ℝ)*base89 + (1080693/1250000000000000000000 : ℝ)*base91 + (1080693/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9580712962447016025359319/4475000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (350545029/100000000000000 : ℝ)*(base19) + (45705123/12500000000000 : ℝ)*(base23) + (5902381/12500000000000 : ℝ)*(upper3) + (9320183/50000000000000 : ℝ)*(lower4) + (38743309/100000000000000 : ℝ)*(upper5) + (446838229009979/10000000000000 : ℝ)*(major0) + (446838229009979/10000000000000 : ℝ)*(major1) + (446838229009979/10000000000000 : ℝ)*(major2) + (7099861449/100000000000000 : ℝ)*(sp1) + (1934290107/25000000000000 : ℝ)*(sp2) + (1518605975373801/25000000000000 : ℝ)*(sp4) + (3037208225544363/50000000000000 : ℝ)*(sp5) + (189825493709181/3125000000000 : ℝ)*(sp6) + (715585151834913/25000000000000 : ℝ)*(sp7) + (715585151834913/25000000000000 : ℝ)*(f.failure) + (1518605975373801/25000000000000 : ℝ)*(f.sum) + (3964499150333/1790000000000000000000000000 : ℝ)*base66 + (19914799949332727/17900000000000000000000000000000 : ℝ)*base68 + (95331880437332727/17900000000000000000000000000000 : ℝ)*base70 + (73658157369167273/17900000000000000000000000000000 : ℝ)*base71 + (12936679804663/1790000000000000000000000000 : ℝ)*base74 + (422868546556132727/17900000000000000000000000000000 : ℝ)*base76 + (14650220710532727/17900000000000000000000000000000 : ℝ)*base78 + (375270183136932727/17900000000000000000000000000000 : ℝ)*base80 + (5018966119013/1790000000000000000000000000 : ℝ)*base82 + (1484551/312500000000000000000 : ℝ)*base90 + (1484551/312500000000000000000 : ℝ)*base92 + (1484551/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1377_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1477/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1119/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1377_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1377_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3993/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1377_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1377_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1377_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (271/64 : ℝ) ≤ p) (hpb : p ≤ (4337/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (19513673/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3993/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1259/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11223/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7367/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1377_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
