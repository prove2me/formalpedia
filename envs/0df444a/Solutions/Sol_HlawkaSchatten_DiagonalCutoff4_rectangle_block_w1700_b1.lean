-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1700_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:44:22.884961+00:00
-- url     : https://prove2.me/submissions/b7d2ef53-7d26-4bd2-9e6b-11859988cd57

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
theorem support_rectangle_w1700_s3_0 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-181129807/1250000000 : ℝ)*x 0 + (5476517917/10000000000 : ℝ)*x 1 + (1284232511/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (181129807/1250000000 : ℝ)^5223 ≤ (904678966481/10000000000000 : ℝ)^4199 := by
    have hnat : (181129807 : ℕ)^5223*10000000000000^4199 ≤ 904678966481^4199*1250000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181129807 1250000000 904678966481 10000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5476517917/10000000000 : ℝ)^5223 ≤ (2955386305571/6250000000000 : ℝ)^4199 := by
    have hnat : (5476517917 : ℕ)^5223*6250000000000^4199 ≤ 2955386305571^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476517917 10000000000 2955386305571 6250000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1284232511/2500000000 : ℝ)^5223 ≤ (21833514714131/50000000000000 : ℝ)^4199 := by
    have hnat : (1284232511 : ℕ)^5223*50000000000000^4199 ≤ 21833514714131^4199*2500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1284232511 2500000000 21833514714131 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-181129807/1250000000 : ℝ), (5476517917/10000000000 : ℝ), (1284232511/2500000000 : ℝ)] ![(904678966481/10000000000000 : ℝ), (2955386305571/6250000000000 : ℝ), (21833514714131/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-181129807/1250000000 : ℝ)|^5223 ≤ (904678966481/10000000000000 : ℝ)^4199
        have hw : |(-181129807/1250000000 : ℝ)|=(181129807/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5476517917/10000000000 : ℝ)|^5223 ≤ (2955386305571/6250000000000 : ℝ)^4199
        have hw : |(5476517917/10000000000 : ℝ)|=(5476517917/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1284232511/2500000000 : ℝ)|^5223 ≤ (21833514714131/50000000000000 : ℝ)^4199
        have hw : |(1284232511/2500000000 : ℝ)|=(1284232511/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s3_1 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673437057/5000000000 : ℝ)*x 0 + (-1625275047/10000000000 : ℝ)*x 1 + (642116233/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673437057/5000000000 : ℝ)^5223 ≤ (45897851055031/100000000000000 : ℝ)^4199 := by
    have hnat : (2673437057 : ℕ)^5223*100000000000000^4199 ≤ 45897851055031^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673437057 5000000000 45897851055031 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1625275047/10000000000 : ℝ)^5223 ≤ (2608780353357/25000000000000 : ℝ)^4199 := by
    have hnat : (1625275047 : ℕ)^5223*25000000000000^4199 ≤ 2608780353357^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625275047 10000000000 2608780353357 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642116233/1250000000 : ℝ)^5223 ≤ (2729189220313/6250000000000 : ℝ)^4199 := by
    have hnat : (642116233 : ℕ)^5223*6250000000000^4199 ≤ 2729189220313^4199*1250000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642116233 1250000000 2729189220313 6250000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673437057/5000000000 : ℝ), (-1625275047/10000000000 : ℝ), (642116233/1250000000 : ℝ)] ![(45897851055031/100000000000000 : ℝ), (2608780353357/25000000000000 : ℝ), (2729189220313/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673437057/5000000000 : ℝ)|^5223 ≤ (45897851055031/100000000000000 : ℝ)^4199
        have hw : |(2673437057/5000000000 : ℝ)|=(2673437057/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1625275047/10000000000 : ℝ)|^5223 ≤ (2608780353357/25000000000000 : ℝ)^4199
        have hw : |(-1625275047/10000000000 : ℝ)|=(1625275047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642116233/1250000000 : ℝ)|^5223 ≤ (2729189220313/6250000000000 : ℝ)^4199
        have hw : |(642116233/1250000000 : ℝ)|=(642116233/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s3_2 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673436999/5000000000 : ℝ)*x 0 + (513692987/1000000000 : ℝ)*x 1 + (-812637597/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673436999/5000000000 : ℝ)^5223 ≤ (45897849816449/100000000000000 : ℝ)^4199 := by
    have hnat : (2673436999 : ℕ)^5223*100000000000000^4199 ≤ 45897849816449^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673436999 5000000000 45897849816449 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513692987/1000000000 : ℝ)^5223 ≤ (873340551769/2000000000000 : ℝ)^4199 := by
    have hnat : (513692987 : ℕ)^5223*2000000000000^4199 ≤ 873340551769^4199*1000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513692987 1000000000 873340551769 2000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (812637597/5000000000 : ℝ)^5223 ≤ (10435122587411/100000000000000 : ℝ)^4199 := by
    have hnat : (812637597 : ℕ)^5223*100000000000000^4199 ≤ 10435122587411^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      812637597 5000000000 10435122587411 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673436999/5000000000 : ℝ), (513692987/1000000000 : ℝ), (-812637597/5000000000 : ℝ)] ![(45897849816449/100000000000000 : ℝ), (873340551769/2000000000000 : ℝ), (10435122587411/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673436999/5000000000 : ℝ)|^5223 ≤ (45897849816449/100000000000000 : ℝ)^4199
        have hw : |(2673436999/5000000000 : ℝ)|=(2673436999/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(513692987/1000000000 : ℝ)|^5223 ≤ (873340551769/2000000000000 : ℝ)^4199
        have hw : |(513692987/1000000000 : ℝ)|=(513692987/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-812637597/5000000000 : ℝ)|^5223 ≤ (10435122587411/100000000000000 : ℝ)^4199
        have hw : |(-812637597/5000000000 : ℝ)|=(812637597/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s3_3 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4117756227/10000000000 : ℝ)*x 0 + (228434407/625000000 : ℝ)*x 1 + (230853329/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4117756227/10000000000 : ℝ)^5223 ≤ (2072854735567/6250000000000 : ℝ)^4199 := by
    have hnat : (4117756227 : ℕ)^5223*6250000000000^4199 ≤ 2072854735567^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4117756227 10000000000 2072854735567 6250000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (228434407/625000000 : ℝ)^5223 ≤ (28594497382667/100000000000000 : ℝ)^4199 := by
    have hnat : (228434407 : ℕ)^5223*100000000000000^4199 ≤ 28594497382667^4199*625000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      228434407 625000000 28594497382667 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (230853329/500000000 : ℝ)^5223 ≤ (38239826831727/100000000000000 : ℝ)^4199 := by
    have hnat : (230853329 : ℕ)^5223*100000000000000^4199 ≤ 38239826831727^4199*500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      230853329 500000000 38239826831727 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4117756227/10000000000 : ℝ), (228434407/625000000 : ℝ), (230853329/500000000 : ℝ)] ![(2072854735567/6250000000000 : ℝ), (28594497382667/100000000000000 : ℝ), (38239826831727/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4117756227/10000000000 : ℝ)|^5223 ≤ (2072854735567/6250000000000 : ℝ)^4199
        have hw : |(4117756227/10000000000 : ℝ)|=(4117756227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(228434407/625000000 : ℝ)|^5223 ≤ (28594497382667/100000000000000 : ℝ)^4199
        have hw : |(228434407/625000000 : ℝ)|=(228434407/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(230853329/500000000 : ℝ)|^5223 ≤ (38239826831727/100000000000000 : ℝ)^4199
        have hw : |(230853329/500000000 : ℝ)|=(230853329/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s3_4 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-9057467/62500000 : ℝ)*x 0 + (5140657521/10000000000 : ℝ)*x 1 + (2736367271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (9057467/62500000 : ℝ)^5223 ≤ (9048003202811/100000000000000 : ℝ)^4199 := by
    have hnat : (9057467 : ℕ)^5223*100000000000000^4199 ≤ 9048003202811^4199*62500000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      9057467 62500000 9048003202811 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5140657521/10000000000 : ℝ)^5223 ≤ (43706445881013/100000000000000 : ℝ)^4199 := by
    have hnat : (5140657521 : ℕ)^5223*100000000000000^4199 ≤ 43706445881013^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5140657521 10000000000 43706445881013 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2736367271/5000000000 : ℝ)^5223 ≤ (9449110180563/20000000000000 : ℝ)^4199 := by
    have hnat : (2736367271 : ℕ)^5223*20000000000000^4199 ≤ 9449110180563^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2736367271 5000000000 9449110180563 20000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-9057467/62500000 : ℝ), (5140657521/10000000000 : ℝ), (2736367271/5000000000 : ℝ)] ![(9048003202811/100000000000000 : ℝ), (43706445881013/100000000000000 : ℝ), (9449110180563/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-9057467/62500000 : ℝ)|^5223 ≤ (9048003202811/100000000000000 : ℝ)^4199
        have hw : |(-9057467/62500000 : ℝ)|=(9057467/62500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5140657521/10000000000 : ℝ)|^5223 ≤ (43706445881013/100000000000000 : ℝ)^4199
        have hw : |(5140657521/10000000000 : ℝ)|=(5140657521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2736367271/5000000000 : ℝ)|^5223 ≤ (9449110180563/20000000000000 : ℝ)^4199
        have hw : |(2736367271/5000000000 : ℝ)|=(2736367271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s3_5 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (328500867/625000000 : ℝ)*x 0 + (-161183851/1250000000 : ℝ)*x 1 + (5472734187/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (328500867/625000000 : ℝ)^5223 ≤ (44929716473609/100000000000000 : ℝ)^4199 := by
    have hnat : (328500867 : ℕ)^5223*100000000000000^4199 ≤ 44929716473609^4199*625000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      328500867 625000000 44929716473609 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (161183851/1250000000 : ℝ)^5223 ≤ (978092052187/12500000000000 : ℝ)^4199 := by
    have hnat : (161183851 : ℕ)^5223*12500000000000^4199 ≤ 978092052187^4199*1250000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161183851 1250000000 978092052187 12500000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5472734187/10000000000 : ℝ)^5223 ≤ (47245547090761/100000000000000 : ℝ)^4199 := by
    have hnat : (5472734187 : ℕ)^5223*100000000000000^4199 ≤ 47245547090761^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472734187 10000000000 47245547090761 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(328500867/625000000 : ℝ), (-161183851/1250000000 : ℝ), (5472734187/10000000000 : ℝ)] ![(44929716473609/100000000000000 : ℝ), (978092052187/12500000000000 : ℝ), (47245547090761/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(328500867/625000000 : ℝ)|^5223 ≤ (44929716473609/100000000000000 : ℝ)^4199
        have hw : |(328500867/625000000 : ℝ)|=(328500867/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-161183851/1250000000 : ℝ)|^5223 ≤ (978092052187/12500000000000 : ℝ)^4199
        have hw : |(-161183851/1250000000 : ℝ)|=(161183851/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5472734187/10000000000 : ℝ)|^5223 ≤ (47245547090761/100000000000000 : ℝ)^4199
        have hw : |(5472734187/10000000000 : ℝ)|=(5472734187/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s3_6 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628006933/5000000000 : ℝ)*x 0 + (5472734287/10000000000 : ℝ)*x 1 + (-51578827/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628006933/5000000000 : ℝ)^5223 ≤ (44929716409811/100000000000000 : ℝ)^4199 := by
    have hnat : (2628006933 : ℕ)^5223*100000000000000^4199 ≤ 44929716409811^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628006933 5000000000 44929716409811 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472734287/10000000000 : ℝ)^5223 ≤ (47245548164579/100000000000000 : ℝ)^4199 := by
    have hnat : (5472734287 : ℕ)^5223*100000000000000^4199 ≤ 47245548164579^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472734287 10000000000 47245548164579 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (51578827/400000000 : ℝ)^5223 ≤ (7824735413611/100000000000000 : ℝ)^4199 := by
    have hnat : (51578827 : ℕ)^5223*100000000000000^4199 ≤ 7824735413611^4199*400000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      51578827 400000000 7824735413611 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628006933/5000000000 : ℝ), (5472734287/10000000000 : ℝ), (-51578827/400000000 : ℝ)] ![(44929716409811/100000000000000 : ℝ), (47245548164579/100000000000000 : ℝ), (7824735413611/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628006933/5000000000 : ℝ)|^5223 ≤ (44929716409811/100000000000000 : ℝ)^4199
        have hw : |(2628006933/5000000000 : ℝ)|=(2628006933/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472734287/10000000000 : ℝ)|^5223 ≤ (47245548164579/100000000000000 : ℝ)^4199
        have hw : |(5472734287/10000000000 : ℝ)|=(5472734287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-51578827/400000000 : ℝ)|^5223 ≤ (7824735413611/100000000000000 : ℝ)^4199
        have hw : |(-51578827/400000000 : ℝ)|=(51578827/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s3_7 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (164727929/400000000 : ℝ)*x 0 + (921300811/2000000000 : ℝ)*x 1 + (3665670441/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (164727929/400000000 : ℝ)^5223 ≤ (33170103980593/100000000000000 : ℝ)^4199 := by
    have hnat : (164727929 : ℕ)^5223*100000000000000^4199 ≤ 33170103980593^4199*400000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164727929 400000000 33170103980593 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (921300811/2000000000 : ℝ)^5223 ≤ (38131041473153/100000000000000 : ℝ)^4199 := by
    have hnat : (921300811 : ℕ)^5223*100000000000000^4199 ≤ 38131041473153^4199*2000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      921300811 2000000000 38131041473153 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3665670441/10000000000 : ℝ)^5223 ≤ (358735681631/1250000000000 : ℝ)^4199 := by
    have hnat : (3665670441 : ℕ)^5223*1250000000000^4199 ≤ 358735681631^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3665670441 10000000000 358735681631 1250000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(164727929/400000000 : ℝ), (921300811/2000000000 : ℝ), (3665670441/10000000000 : ℝ)] ![(33170103980593/100000000000000 : ℝ), (38131041473153/100000000000000 : ℝ), (358735681631/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(164727929/400000000 : ℝ)|^5223 ≤ (33170103980593/100000000000000 : ℝ)^4199
        have hw : |(164727929/400000000 : ℝ)|=(164727929/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(921300811/2000000000 : ℝ)|^5223 ≤ (38131041473153/100000000000000 : ℝ)^4199
        have hw : |(921300811/2000000000 : ℝ)|=(921300811/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3665670441/10000000000 : ℝ)|^5223 ≤ (358735681631/1250000000000 : ℝ)^4199
        have hw : |(3665670441/10000000000 : ℝ)|=(3665670441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1700_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (859/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1239/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (397/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4291/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (859/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1239/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (859/5000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1239/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (859/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1239/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (859/5000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1239/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (859/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1239/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (859/5000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1239/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1239/12500 : ℝ) ^ (5215/1024 : ℝ) ≤ (772105950185549/100000000000000000000 : ℝ) := by
    have hpowers : (1239/12500 : ℝ)^5215 ≤ (772105950185549/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1239 : ℕ)^5215*100000000000000000000^1024 ≤ 772105950185549^1024*12500^5215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1239 12500 772105950185549 100000000000000000000 5215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1239/12500 : ℝ)) (X := (772105950185549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (859/5000 : ℝ) ^ (5215/1024 : ℝ) ≤ (3177505237280003/25000000000000000000 : ℝ) := by
    have hpowers : (859/5000 : ℝ)^5215 ≤ (3177505237280003/25000000000000000000 : ℝ)^1024 := by
      have hnat : (859 : ℕ)^5215*25000000000000000000^1024 ≤ 3177505237280003^1024*5000^5215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        859 5000 3177505237280003 25000000000000000000 5215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (859/5000 : ℝ)) (X := (3177505237280003/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000772105950185549/50000000000000000000 : ℝ) ≤ (5000015160720751/5000000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (50000772105950185549/50000000000000000000 : ℝ)^1024 ≤ (5000015160720751/5000000000000000 : ℝ)^5215 := by
      have hnat : (50000772105950185549 : ℕ)^1024*5000000000000000^5215 ≤ 5000015160720751^5215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000772105950185549 50000000000000000000 5000015160720751 5000000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000015160720751/5000000000000000 : ℝ)) (X := (50000772105950185549/50000000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100013482126899305561/100000000000000000000 : ℝ) ≤ (5000132358102533/5000000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (100013482126899305561/100000000000000000000 : ℝ)^1024 ≤ (5000132358102533/5000000000000000 : ℝ)^5215 := by
      have hnat : (100013482126899305561 : ℕ)^1024*5000000000000000^5215 ≤ 5000132358102533^5215*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100013482126899305561 100000000000000000000 5000132358102533 5000000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000132358102533/5000000000000000 : ℝ)) (X := (100013482126899305561/100000000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503177505237280003/12500000000000000000 : ℝ) ≤ (1000049911096863/1000000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (12503177505237280003/12500000000000000000 : ℝ)^1024 ≤ (1000049911096863/1000000000000000 : ℝ)^5215 := by
      have hnat : (12503177505237280003 : ℕ)^1024*1000000000000000^5215 ≤ 1000049911096863^5215*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503177505237280003 12500000000000000000 1000049911096863 1000000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000049911096863/1000000000000000 : ℝ)) (X := (12503177505237280003/12500000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(772105950185549/100000000000000000000 : ℝ) ≤ ((363377868672219719/363400000000000000 : ℝ)+2*(58598690891/181700000000000 : ℝ)*(1239/12500 : ℝ))^(5215/1024 : ℝ) := by
    rw [show (363377868672219719/363400000000000000 : ℝ)+2*(58598690891/181700000000000 : ℝ)*(1239/12500 : ℝ)=(5000015160720751/5000000000000000 : ℝ) by norm_num, show 1+2*(772105950185549/100000000000000000000 : ℝ)=(50000772105950185549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3177505237280003/25000000000000000000 : ℝ)+(772105950185549/100000000000000000000 : ℝ) ≤ ((363377868672219719/363400000000000000 : ℝ)+(58598690891/181700000000000 : ℝ)*((859/5000 : ℝ)+(1239/12500 : ℝ)))^(5215/1024 : ℝ) := by
    rw [show (363377868672219719/363400000000000000 : ℝ)+(58598690891/181700000000000 : ℝ)*((859/5000 : ℝ)+(1239/12500 : ℝ))=(5000132358102533/5000000000000000 : ℝ) by norm_num, show 1+(3177505237280003/25000000000000000000 : ℝ)+(772105950185549/100000000000000000000 : ℝ)=(100013482126899305561/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3177505237280003/25000000000000000000 : ℝ) ≤ ((363377868672219719/363400000000000000 : ℝ)+2*(58598690891/181700000000000 : ℝ)*(859/5000 : ℝ))^(5215/1024 : ℝ) := by
    rw [show (363377868672219719/363400000000000000 : ℝ)+2*(58598690891/181700000000000 : ℝ)*(859/5000 : ℝ)=(1000049911096863/1000000000000000 : ℝ) by norm_num, show 1+2*(3177505237280003/25000000000000000000 : ℝ)=(12503177505237280003/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (363377868672219719/363400000000000000 : ℝ)*(X 1 0+X 2 0)+(58598690891/181700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (1239/12500 : ℝ)) (hi := (859/5000 : ℝ)) (c := (363377868672219719/363400000000000000 : ℝ)) (alpha := (58598690891/181700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (363377868672219719/363400000000000000 : ℝ)*(X 0 1+X 2 1)+(58598690891/181700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (1239/12500 : ℝ)) (hi := (859/5000 : ℝ)) (c := (363377868672219719/363400000000000000 : ℝ)) (alpha := (58598690891/181700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (363377868672219719/363400000000000000 : ℝ)*(X 0 2+X 1 2)+(58598690891/181700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (1239/12500 : ℝ)) (hi := (859/5000 : ℝ)) (c := (363377868672219719/363400000000000000 : ℝ)) (alpha := (58598690891/181700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-181129807/1250000000 : ℝ)*X 0 0+(5476517917/10000000000 : ℝ)*X 0 1+(1284232511/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673437057/5000000000 : ℝ)*X 1 0+(-1625275047/10000000000 : ℝ)*X 1 1+(642116233/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673436999/5000000000 : ℝ)*X 2 0+(513692987/1000000000 : ℝ)*X 2 1+(-812637597/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4117756227/10000000000 : ℝ)*X 0 0+(228434407/625000000 : ℝ)*X 0 1+(230853329/500000000 : ℝ)*X 0 2+(4117756227/10000000000 : ℝ)*X 1 0+(228434407/625000000 : ℝ)*X 1 1+(230853329/500000000 : ℝ)*X 1 2+(4117756227/10000000000 : ℝ)*X 2 0+(228434407/625000000 : ℝ)*X 2 1+(230853329/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-9057467/62500000 : ℝ)*X 0 0+(5140657521/10000000000 : ℝ)*X 0 1+(2736367271/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((328500867/625000000 : ℝ)*X 1 0+(-161183851/1250000000 : ℝ)*X 1 1+(5472734187/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2628006933/5000000000 : ℝ)*X 2 0+(5472734287/10000000000 : ℝ)*X 2 1+(-51578827/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((164727929/400000000 : ℝ)*X 0 0+(921300811/2000000000 : ℝ)*X 0 1+(3665670441/10000000000 : ℝ)*X 0 2+(164727929/400000000 : ℝ)*X 1 0+(921300811/2000000000 : ℝ)*X 1 1+(3665670441/10000000000 : ℝ)*X 1 2+(164727929/400000000 : ℝ)*X 2 0+(921300811/2000000000 : ℝ)*X 2 1+(3665670441/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2669839990603751188181769/197500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1860967743/100000000000000 : ℝ)*(base19) + (1532206789/100000000000000 : ℝ)*(base23) + (70812471/50000000000000 : ℝ)*(lower2) + (95295773/25000000000000 : ℝ)*(upper3) + (11304773/12500000000000 : ℝ)*(upper5) + (996041495961291/50000000000000 : ℝ)*(major0) + (996041495961291/50000000000000 : ℝ)*(major1) + (996041495961291/50000000000000 : ℝ)*(major2) + (2944763525743079/100000000000000 : ℝ)*(sp0) + (368096960651527/12500000000000 : ℝ)*(sp1) + (2944776013973169/100000000000000 : ℝ)*(sp2) + (1039380722823099/100000000000000 : ℝ)*(sp3) + (14020436879/100000000000000 : ℝ)*(sp4) + (1452847239/20000000000000 : ℝ)*(sp7) + (519693993529647/50000000000000 : ℝ)*(f.failure) + (1472388773089979/50000000000000 : ℝ)*(f.sum) + (717355732757/197500000000000000000000000 : ℝ)*base65 + (3744557140743077/790000000000000000000000000000 : ℝ)*base68 + (1022008588996923/790000000000000000000000000000 : ℝ)*base69 + (6816793794773077/790000000000000000000000000000 : ℝ)*base72 + (1088096977201/395000000000000000000000000 : ℝ)*base74 + (10017355607703077/790000000000000000000000000000 : ℝ)*base76 + (235132394793077/790000000000000000000000000000 : ℝ)*base78 + (8954839896863077/790000000000000000000000000000 : ℝ)*base80 + (371211622561/395000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9783129/1250000000000000000000 : ℝ)*base89 + (9783129/1250000000000000000000 : ℝ)*base91 + (9783129/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (455194318251395345034471/98750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (322977893/50000000000000 : ℝ)*(base19) + (671842789/100000000000000 : ℝ)*(base23) + (63905871/50000000000000 : ℝ)*(lower1) + (29784661/100000000000000 : ℝ)*(upper3) + (574337/2500000000000 : ℝ)*(lower4) + (98706147/50000000000000 : ℝ)*(upper5) + (509279206290431/25000000000000 : ℝ)*(major0) + (509279206290431/25000000000000 : ℝ)*(major1) + (509279206290431/25000000000000 : ℝ)*(major2) + (33283757/4000000000000 : ℝ)*(sp1) + (188209292793483/6250000000000 : ℝ)*(sp4) + (1505673603323009/50000000000000 : ℝ)*(sp5) + (3011348012852939/100000000000000 : ℝ)*(sp6) + (1062884811975619/100000000000000 : ℝ)*(sp7) + (1062884811975619/100000000000000 : ℝ)*(f.failure) + (188209292793483/6250000000000 : ℝ)*(f.sum) + (49369261411309/9085000000000000000000000000 : ℝ)*base65 + (34588192436945889/9085000000000000000000000000000 : ℝ)*base67 + (3481068655075889/9085000000000000000000000000000 : ℝ)*base69 + (78616009487465889/9085000000000000000000000000000 : ℝ)*base71 + (464842917563/4542500000000000000000000000 : ℝ)*base74 + (13926309099074111/9085000000000000000000000000000 : ℝ)*base76 + (38622630928085889/9085000000000000000000000000000 : ℝ)*base77 + (87151738409520889/9085000000000000000000000000000 : ℝ)*base79 + (31496982216503/4542500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (26909467/2500000000000000000000 : ℝ)*base90 + (26909467/2500000000000000000000 : ℝ)*base92 + (26909467/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1700_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (859/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1239/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (397/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4291/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1700_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1700_s4_0 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-289809463/2000000000 : ℝ)*x 0 + (5476485981/10000000000 : ℝ)*x 1 + (642119497/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (289809463/2000000000 : ℝ)^5223 ≤ (2261714615621/25000000000000 : ℝ)^4199 := by
    have hnat : (289809463 : ℕ)^5223*25000000000000^4199 ≤ 2261714615621^4199*2000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      289809463 2000000000 2261714615621 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5476485981/10000000000 : ℝ)^5223 ≤ (47285837897059/100000000000000 : ℝ)^4199 := by
    have hnat : (5476485981 : ℕ)^5223*100000000000000^4199 ≤ 47285837897059^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5476485981 10000000000 47285837897059 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (642119497/1250000000 : ℝ)^5223 ≤ (10916825905957/25000000000000 : ℝ)^4199 := by
    have hnat : (642119497 : ℕ)^5223*25000000000000^4199 ≤ 10916825905957^4199*1250000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      642119497 1250000000 10916825905957 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-289809463/2000000000 : ℝ), (5476485981/10000000000 : ℝ), (642119497/1250000000 : ℝ)] ![(2261714615621/25000000000000 : ℝ), (47285837897059/100000000000000 : ℝ), (10916825905957/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-289809463/2000000000 : ℝ)|^5223 ≤ (2261714615621/25000000000000 : ℝ)^4199
        have hw : |(-289809463/2000000000 : ℝ)|=(289809463/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5476485981/10000000000 : ℝ)|^5223 ≤ (47285837897059/100000000000000 : ℝ)^4199
        have hw : |(5476485981/10000000000 : ℝ)|=(5476485981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(642119497/1250000000 : ℝ)|^5223 ≤ (10916825905957/25000000000000 : ℝ)^4199
        have hw : |(642119497/1250000000 : ℝ)|=(642119497/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s4_1 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2673433353/5000000000 : ℝ)*x 0 + (-162525241/1000000000 : ℝ)*x 1 + (2568477221/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673433353/5000000000 : ℝ)^5223 ≤ (45897771956677/100000000000000 : ℝ)^4199 := by
    have hnat : (2673433353 : ℕ)^5223*100000000000000^4199 ≤ 45897771956677^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673433353 5000000000 45897771956677 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (162525241/1000000000 : ℝ)^5223 ≤ (10434940628207/100000000000000 : ℝ)^4199 := by
    have hnat : (162525241 : ℕ)^5223*100000000000000^4199 ≤ 10434940628207^4199*1000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162525241 1000000000 10434940628207 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2568477221/5000000000 : ℝ)^5223 ≤ (43667287403859/100000000000000 : ℝ)^4199 := by
    have hnat : (2568477221 : ℕ)^5223*100000000000000^4199 ≤ 43667287403859^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568477221 5000000000 43667287403859 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673433353/5000000000 : ℝ), (-162525241/1000000000 : ℝ), (2568477221/5000000000 : ℝ)] ![(45897771956677/100000000000000 : ℝ), (10434940628207/100000000000000 : ℝ), (43667287403859/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673433353/5000000000 : ℝ)|^5223 ≤ (45897771956677/100000000000000 : ℝ)^4199
        have hw : |(2673433353/5000000000 : ℝ)|=(2673433353/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-162525241/1000000000 : ℝ)|^5223 ≤ (10434940628207/100000000000000 : ℝ)^4199
        have hw : |(-162525241/1000000000 : ℝ)|=(162525241/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2568477221/5000000000 : ℝ)|^5223 ≤ (43667287403859/100000000000000 : ℝ)^4199
        have hw : |(2568477221/5000000000 : ℝ)|=(2568477221/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s4_2 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5346863103/10000000000 : ℝ)*x 0 + (2568477763/5000000000 : ℝ)*x 1 + (-1625255791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346863103/10000000000 : ℝ)^5223 ≤ (4589773348593/10000000000000 : ℝ)^4199 := by
    have hnat : (5346863103 : ℕ)^5223*10000000000000^4199 ≤ 4589773348593^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346863103 10000000000 4589773348593 10000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2568477763/5000000000 : ℝ)^5223 ≤ (43667298865689/100000000000000 : ℝ)^4199 := by
    have hnat : (2568477763 : ℕ)^5223*100000000000000^4199 ≤ 43667298865689^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2568477763 5000000000 43667298865689 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1625255791/10000000000 : ℝ)^5223 ≤ (10434967629751/100000000000000 : ℝ)^4199 := by
    have hnat : (1625255791 : ℕ)^5223*100000000000000^4199 ≤ 10434967629751^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1625255791 10000000000 10434967629751 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346863103/10000000000 : ℝ), (2568477763/5000000000 : ℝ), (-1625255791/10000000000 : ℝ)] ![(4589773348593/10000000000000 : ℝ), (43667298865689/100000000000000 : ℝ), (10434967629751/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346863103/10000000000 : ℝ)|^5223 ≤ (4589773348593/10000000000000 : ℝ)^4199
        have hw : |(5346863103/10000000000 : ℝ)|=(5346863103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2568477763/5000000000 : ℝ)|^5223 ≤ (43667298865689/100000000000000 : ℝ)^4199
        have hw : |(2568477763/5000000000 : ℝ)|=(2568477763/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1625255791/10000000000 : ℝ)|^5223 ≤ (10434967629751/100000000000000 : ℝ)^4199
        have hw : |(-1625255791/10000000000 : ℝ)|=(1625255791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s4_3 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2058881169/5000000000 : ℝ)*x 0 + (3655028791/10000000000 : ℝ)*x 1 + (4616986693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2058881169/5000000000 : ℝ)^5223 ≤ (3316573699209/10000000000000 : ℝ)^4199 := by
    have hnat : (2058881169 : ℕ)^5223*10000000000000^4199 ≤ 3316573699209^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058881169 5000000000 3316573699209 10000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3655028791/10000000000 : ℝ)^5223 ≤ (14297629574277/50000000000000 : ℝ)^4199 := by
    have hnat : (3655028791 : ℕ)^5223*50000000000000^4199 ≤ 14297629574277^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3655028791 10000000000 14297629574277 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4616986693/10000000000 : ℝ)^5223 ≤ (38239003833069/100000000000000 : ℝ)^4199 := by
    have hnat : (4616986693 : ℕ)^5223*100000000000000^4199 ≤ 38239003833069^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4616986693 10000000000 38239003833069 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2058881169/5000000000 : ℝ), (3655028791/10000000000 : ℝ), (4616986693/10000000000 : ℝ)] ![(3316573699209/10000000000000 : ℝ), (14297629574277/50000000000000 : ℝ), (38239003833069/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2058881169/5000000000 : ℝ)|^5223 ≤ (3316573699209/10000000000000 : ℝ)^4199
        have hw : |(2058881169/5000000000 : ℝ)|=(2058881169/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3655028791/10000000000 : ℝ)|^5223 ≤ (14297629574277/50000000000000 : ℝ)^4199
        have hw : |(3655028791/10000000000 : ℝ)|=(3655028791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4616986693/10000000000 : ℝ)|^5223 ≤ (38239003833069/100000000000000 : ℝ)^4199
        have hw : |(4616986693/10000000000 : ℝ)|=(4616986693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s4_4 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5256020431/10000000000 : ℝ)*x 0 + (5472704601/10000000000 : ℝ)*x 1 + (-1289503659/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5256020431/10000000000 : ℝ)^5223 ≤ (22464893107373/50000000000000 : ℝ)^4199 := by
    have hnat : (5256020431 : ℕ)^5223*50000000000000^4199 ≤ 22464893107373^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5256020431 10000000000 22464893107373 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472704601/10000000000 : ℝ)^5223 ≤ (47245229391177/100000000000000 : ℝ)^4199 := by
    have hnat : (5472704601 : ℕ)^5223*100000000000000^4199 ≤ 47245229391177^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472704601 10000000000 47245229391177 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1289503659/10000000000 : ℝ)^5223 ≤ (3912492188939/50000000000000 : ℝ)^4199 := by
    have hnat : (1289503659 : ℕ)^5223*50000000000000^4199 ≤ 3912492188939^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1289503659 10000000000 3912492188939 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5256020431/10000000000 : ℝ), (5472704601/10000000000 : ℝ), (-1289503659/10000000000 : ℝ)] ![(22464893107373/50000000000000 : ℝ), (47245229391177/100000000000000 : ℝ), (3912492188939/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5256020431/10000000000 : ℝ)|^5223 ≤ (22464893107373/50000000000000 : ℝ)^4199
        have hw : |(5256020431/10000000000 : ℝ)|=(5256020431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472704601/10000000000 : ℝ)|^5223 ≤ (47245229391177/100000000000000 : ℝ)^4199
        have hw : |(5472704601/10000000000 : ℝ)|=(5472704601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1289503659/10000000000 : ℝ)|^5223 ≤ (3912492188939/50000000000000 : ℝ)^4199
        have hw : |(-1289503659/10000000000 : ℝ)|=(1289503659/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_s4_5 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4118203161/10000000000 : ℝ)*x 0 + (287901779/625000000 : ℝ)*x 1 + (916436321/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4118203161/10000000000 : ℝ)^5223 ≤ (33170153433173/100000000000000 : ℝ)^4199 := by
    have hnat : (4118203161 : ℕ)^5223*100000000000000^4199 ≤ 33170153433173^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4118203161 10000000000 33170153433173 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (287901779/625000000 : ℝ)^5223 ≤ (9532565791697/25000000000000 : ℝ)^4199 := by
    have hnat : (287901779 : ℕ)^5223*25000000000000^4199 ≤ 9532565791697^4199*625000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      287901779 625000000 9532565791697 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (916436321/2500000000 : ℝ)^5223 ≤ (5739916675897/20000000000000 : ℝ)^4199 := by
    have hnat : (916436321 : ℕ)^5223*20000000000000^4199 ≤ 5739916675897^4199*2500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      916436321 2500000000 5739916675897 20000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4118203161/10000000000 : ℝ), (287901779/625000000 : ℝ), (916436321/2500000000 : ℝ)] ![(33170153433173/100000000000000 : ℝ), (9532565791697/25000000000000 : ℝ), (5739916675897/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4118203161/10000000000 : ℝ)|^5223 ≤ (33170153433173/100000000000000 : ℝ)^4199
        have hw : |(4118203161/10000000000 : ℝ)|=(4118203161/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(287901779/625000000 : ℝ)|^5223 ≤ (9532565791697/25000000000000 : ℝ)^4199
        have hw : |(287901779/625000000 : ℝ)|=(287901779/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(916436321/2500000000 : ℝ)|^5223 ≤ (5739916675897/20000000000000 : ℝ)^4199
        have hw : |(916436321/2500000000 : ℝ)|=(916436321/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1700_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4291/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (397/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (4963/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4291/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4291/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (397/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4291/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (397/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4291/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (397/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4291/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (397/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4291/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (397/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4291/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (397/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (397/4000 : ℝ) ^ (5215/1024 : ℝ) ≤ (48579812661151/6250000000000000000 : ℝ) := by
    have hpowers : (397/4000 : ℝ)^5215 ≤ (48579812661151/6250000000000000000 : ℝ)^1024 := by
      have hnat : (397 : ℕ)^5215*6250000000000000000^1024 ≤ 48579812661151^1024*4000^5215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        397 4000 48579812661151 6250000000000000000 5215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (397/4000 : ℝ)) (X := (48579812661151/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4291/25000 : ℝ) ^ (5215/1024 : ℝ) ≤ (3162463092367547/25000000000000000000 : ℝ) := by
    have hpowers : (4291/25000 : ℝ)^5215 ≤ (3162463092367547/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4291 : ℕ)^5215*25000000000000000000^1024 ≤ 3162463092367547^1024*25000^5215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4291 25000 3162463092367547 25000000000000000000 5215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4291/25000 : ℝ)) (X := (3162463092367547/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (3125048579812661151/3125000000000000000 : ℝ) ≤ (2500007631128273/2500000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (3125048579812661151/3125000000000000000 : ℝ)^1024 ≤ (2500007631128273/2500000000000000 : ℝ)^5215 := by
      have hnat : (3125048579812661151 : ℕ)^1024*2500000000000000^5215 ≤ 2500007631128273^5215*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3125048579812661151 3125000000000000000 2500007631128273 2500000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500007631128273/2500000000000000 : ℝ)) (X := (3125048579812661151/3125000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25003356782343012151/25000000000000000000 : ℝ) ≤ (2500065909102181/2500000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (25003356782343012151/25000000000000000000 : ℝ)^1024 ≤ (2500065909102181/2500000000000000 : ℝ)^5215 := by
      have hnat : (25003356782343012151 : ℕ)^1024*2500000000000000^5215 ≤ 2500065909102181^5215*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25003356782343012151 25000000000000000000 2500065909102181 2500000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500065909102181/2500000000000000 : ℝ)) (X := (25003356782343012151/25000000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503162463092367547/12500000000000000000 : ℝ) ≤ (2500124187076089/2500000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (12503162463092367547/12500000000000000000 : ℝ)^1024 ≤ (2500124187076089/2500000000000000 : ℝ)^5215 := by
      have hnat : (12503162463092367547 : ℕ)^1024*2500000000000000^5215 ≤ 2500124187076089^5215*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503162463092367547 12500000000000000000 2500124187076089 2500000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500124187076089/2500000000000000 : ℝ)) (X := (12503162463092367547/12500000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(48579812661151/6250000000000000000 : ℝ) ≤ ((18096398423955494447/18097500000000000000 : ℝ)+2*(14569493477/45243750000000 : ℝ)*(397/4000 : ℝ))^(5215/1024 : ℝ) := by
    rw [show (18096398423955494447/18097500000000000000 : ℝ)+2*(14569493477/45243750000000 : ℝ)*(397/4000 : ℝ)=(2500007631128273/2500000000000000 : ℝ) by norm_num, show 1+2*(48579812661151/6250000000000000000 : ℝ)=(3125048579812661151/3125000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3162463092367547/25000000000000000000 : ℝ)+(48579812661151/6250000000000000000 : ℝ) ≤ ((18096398423955494447/18097500000000000000 : ℝ)+(14569493477/45243750000000 : ℝ)*((4291/25000 : ℝ)+(397/4000 : ℝ)))^(5215/1024 : ℝ) := by
    rw [show (18096398423955494447/18097500000000000000 : ℝ)+(14569493477/45243750000000 : ℝ)*((4291/25000 : ℝ)+(397/4000 : ℝ))=(2500065909102181/2500000000000000 : ℝ) by norm_num, show 1+(3162463092367547/25000000000000000000 : ℝ)+(48579812661151/6250000000000000000 : ℝ)=(25003356782343012151/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3162463092367547/25000000000000000000 : ℝ) ≤ ((18096398423955494447/18097500000000000000 : ℝ)+2*(14569493477/45243750000000 : ℝ)*(4291/25000 : ℝ))^(5215/1024 : ℝ) := by
    rw [show (18096398423955494447/18097500000000000000 : ℝ)+2*(14569493477/45243750000000 : ℝ)*(4291/25000 : ℝ)=(2500124187076089/2500000000000000 : ℝ) by norm_num, show 1+2*(3162463092367547/25000000000000000000 : ℝ)=(12503162463092367547/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (18096398423955494447/18097500000000000000 : ℝ)*(X 1 0+X 2 0)+(14569493477/45243750000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (397/4000 : ℝ)) (hi := (4291/25000 : ℝ)) (c := (18096398423955494447/18097500000000000000 : ℝ)) (alpha := (14569493477/45243750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (18096398423955494447/18097500000000000000 : ℝ)*(X 0 1+X 2 1)+(14569493477/45243750000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (397/4000 : ℝ)) (hi := (4291/25000 : ℝ)) (c := (18096398423955494447/18097500000000000000 : ℝ)) (alpha := (14569493477/45243750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (18096398423955494447/18097500000000000000 : ℝ)*(X 0 2+X 1 2)+(14569493477/45243750000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (397/4000 : ℝ)) (hi := (4291/25000 : ℝ)) (c := (18096398423955494447/18097500000000000000 : ℝ)) (alpha := (14569493477/45243750000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-289809463/2000000000 : ℝ)*X 0 0+(5476485981/10000000000 : ℝ)*X 0 1+(642119497/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2673433353/5000000000 : ℝ)*X 1 0+(-162525241/1000000000 : ℝ)*X 1 1+(2568477221/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5346863103/10000000000 : ℝ)*X 2 0+(2568477763/5000000000 : ℝ)*X 2 1+(-1625255791/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2058881169/5000000000 : ℝ)*X 0 0+(3655028791/10000000000 : ℝ)*X 0 1+(4616986693/10000000000 : ℝ)*X 0 2+(2058881169/5000000000 : ℝ)*X 1 0+(3655028791/10000000000 : ℝ)*X 1 1+(4616986693/10000000000 : ℝ)*X 1 2+(2058881169/5000000000 : ℝ)*X 2 0+(3655028791/10000000000 : ℝ)*X 2 1+(4616986693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((5256020431/10000000000 : ℝ)*X 2 0+(5472704601/10000000000 : ℝ)*X 2 1+(-1289503659/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s4_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((4118203161/10000000000 : ℝ)*X 0 0+(287901779/625000000 : ℝ)*X 0 1+(916436321/2500000000 : ℝ)*X 0 2+(4118203161/10000000000 : ℝ)*X 1 0+(287901779/625000000 : ℝ)*X 1 1+(916436321/2500000000 : ℝ)*X 1 2+(4118203161/10000000000 : ℝ)*X 2 0+(287901779/625000000 : ℝ)*X 2 1+(916436321/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_s4_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2477392158292467357075655149/301625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1507202431/100000000000000 : ℝ)*(base19) + (104907449/50000000000000 : ℝ)*(upper2) + (140578049/50000000000000 : ℝ)*(upper3) + (132741059/50000000000000 : ℝ)*(lower4) + (85899987/50000000000000 : ℝ)*(upper5) + (1992411125752333/100000000000000 : ℝ)*(major0) + (1992411125752333/100000000000000 : ℝ)*(major1) + (1992411125752333/100000000000000 : ℝ)*(major2) + (92039461992467/3125000000000 : ℝ)*(sp0) + (92039414892391/3125000000000 : ℝ)*(sp1) + (1472619283038993/50000000000000 : ℝ)*(sp2) + (129944308066419/12500000000000 : ℝ)*(sp3) + (12108840479/50000000000000 : ℝ)*(sp4) + (1182357889/25000000000000 : ℝ)*(sp5) + (1039559193962909/100000000000000 : ℝ)*(f.failure) + (92039461992467/3125000000000 : ℝ)*(f.sum) + (58223640099571/9048750000000000000000000000 : ℝ)*base66 + (442402618185194851/1809750000000000000000000000000000 : ℝ)*base67 + (12760645694121194851/1809750000000000000000000000000000 : ℝ)*base69 + (3779978465483805149/1809750000000000000000000000000000 : ℝ)*base72 + (6977140526467/4524375000000000000000000000 : ℝ)*base73 + (27857259940761194851/1809750000000000000000000000000000 : ℝ)*base75 + (13030178948027805149/1809750000000000000000000000000000 : ℝ)*base78 + (1479435824467694851/1809750000000000000000000000000000 : ℝ)*base79 + (17102036635751/2262187500000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (24893563/2500000000000000000000 : ℝ)*base89 + (24893563/2500000000000000000000 : ℝ)*base91 + (24893563/2500000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1700_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4291/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (397/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4963/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4291/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1700_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1700_box_0 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-70154609/625000000 : ℝ)*x 0 + (1084515941/2000000000 : ℝ)*x 1 + (5422579637/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (70154609/625000000 : ℝ)^5223 ≤ (6584835806949/100000000000000 : ℝ)^4199 := by
    have hnat : (70154609 : ℕ)^5223*100000000000000^4199 ≤ 6584835806949^4199*625000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      70154609 625000000 6584835806949 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1084515941/2000000000 : ℝ)^5223 ≤ (46707582456561/100000000000000 : ℝ)^4199 := by
    have hnat : (1084515941 : ℕ)^5223*100000000000000^4199 ≤ 46707582456561^4199*2000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084515941 2000000000 46707582456561 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422579637/10000000000 : ℝ)^5223 ≤ (23353790864001/50000000000000 : ℝ)^4199 := by
    have hnat : (5422579637 : ℕ)^5223*50000000000000^4199 ≤ 23353790864001^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422579637 10000000000 23353790864001 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-70154609/625000000 : ℝ), (1084515941/2000000000 : ℝ), (5422579637/10000000000 : ℝ)] ![(6584835806949/100000000000000 : ℝ), (46707582456561/100000000000000 : ℝ), (23353790864001/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-70154609/625000000 : ℝ)|^5223 ≤ (6584835806949/100000000000000 : ℝ)^4199
        have hw : |(-70154609/625000000 : ℝ)|=(70154609/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1084515941/2000000000 : ℝ)|^5223 ≤ (46707582456561/100000000000000 : ℝ)^4199
        have hw : |(1084515941/2000000000 : ℝ)|=(1084515941/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422579637/10000000000 : ℝ)|^5223 ≤ (23353790864001/50000000000000 : ℝ)^4199
        have hw : |(5422579637/10000000000 : ℝ)|=(5422579637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_1 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1045161377/2000000000 : ℝ)*x 0 + (-1402092119/10000000000 : ℝ)*x 1 + (5422579647/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1045161377/2000000000 : ℝ)^5223 ≤ (22304377152401/50000000000000 : ℝ)^4199 := by
    have hnat : (1045161377 : ℕ)^5223*50000000000000^4199 ≤ 22304377152401^4199*2000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1045161377 2000000000 22304377152401 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1402092119/10000000000 : ℝ)^5223 ≤ (4341831925873/50000000000000 : ℝ)^4199 := by
    have hnat : (1402092119 : ℕ)^5223*50000000000000^4199 ≤ 4341831925873^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1402092119 10000000000 4341831925873 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5422579647/10000000000 : ℝ)^5223 ≤ (46707581835143/100000000000000 : ℝ)^4199 := by
    have hnat : (5422579647 : ℕ)^5223*100000000000000^4199 ≤ 46707581835143^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5422579647 10000000000 46707581835143 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1045161377/2000000000 : ℝ), (-1402092119/10000000000 : ℝ), (5422579647/10000000000 : ℝ)] ![(22304377152401/50000000000000 : ℝ), (4341831925873/50000000000000 : ℝ), (46707581835143/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1045161377/2000000000 : ℝ)|^5223 ≤ (22304377152401/50000000000000 : ℝ)^4199
        have hw : |(1045161377/2000000000 : ℝ)|=(1045161377/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1402092119/10000000000 : ℝ)|^5223 ≤ (4341831925873/50000000000000 : ℝ)^4199
        have hw : |(-1402092119/10000000000 : ℝ)|=(1402092119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5422579647/10000000000 : ℝ)|^5223 ≤ (46707581835143/100000000000000 : ℝ)^4199
        have hw : |(5422579647/10000000000 : ℝ)|=(5422579647/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_2 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (522580689/1000000000 : ℝ)*x 0 + (2711289809/5000000000 : ℝ)*x 1 + (-175261519/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (522580689/1000000000 : ℝ)^5223 ≤ (11152188589473/25000000000000 : ℝ)^4199 := by
    have hnat : (522580689 : ℕ)^5223*25000000000000^4199 ≤ 11152188589473^4199*1000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      522580689 1000000000 11152188589473 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2711289809/5000000000 : ℝ)^5223 ≤ (9341516304887/20000000000000 : ℝ)^4199 := by
    have hnat : (2711289809 : ℕ)^5223*20000000000000^4199 ≤ 9341516304887^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2711289809 5000000000 9341516304887 20000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (175261519/1250000000 : ℝ)^5223 ≤ (8683664105969/100000000000000 : ℝ)^4199 := by
    have hnat : (175261519 : ℕ)^5223*100000000000000^4199 ≤ 8683664105969^4199*1250000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      175261519 1250000000 8683664105969 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(522580689/1000000000 : ℝ), (2711289809/5000000000 : ℝ), (-175261519/1250000000 : ℝ)] ![(11152188589473/25000000000000 : ℝ), (9341516304887/20000000000000 : ℝ), (8683664105969/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(522580689/1000000000 : ℝ)|^5223 ≤ (11152188589473/25000000000000 : ℝ)^4199
        have hw : |(522580689/1000000000 : ℝ)|=(522580689/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2711289809/5000000000 : ℝ)|^5223 ≤ (9341516304887/20000000000000 : ℝ)^4199
        have hw : |(2711289809/5000000000 : ℝ)|=(2711289809/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-175261519/1250000000 : ℝ)|^5223 ≤ (8683664105969/100000000000000 : ℝ)^4199
        have hw : |(-175261519/1250000000 : ℝ)|=(175261519/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_3 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4500764157/10000000000 : ℝ)*x 0 + (3948372939/10000000000 : ℝ)*x 1 + (3948372897/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4500764157/10000000000 : ℝ)^5223 ≤ (4630672051779/12500000000000 : ℝ)^4199 := by
    have hnat : (4500764157 : ℕ)^5223*12500000000000^4199 ≤ 4630672051779^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4500764157 10000000000 4630672051779 12500000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3948372939/10000000000 : ℝ)^5223 ≤ (15738655996573/50000000000000 : ℝ)^4199 := by
    have hnat : (3948372939 : ℕ)^5223*50000000000000^4199 ≤ 15738655996573^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3948372939 10000000000 15738655996573 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3948372897/10000000000 : ℝ)^5223 ≤ (15738655788329/50000000000000 : ℝ)^4199 := by
    have hnat : (3948372897 : ℕ)^5223*50000000000000^4199 ≤ 15738655788329^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3948372897 10000000000 15738655788329 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4500764157/10000000000 : ℝ), (3948372939/10000000000 : ℝ), (3948372897/10000000000 : ℝ)] ![(4630672051779/12500000000000 : ℝ), (15738655996573/50000000000000 : ℝ), (15738655788329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4500764157/10000000000 : ℝ)|^5223 ≤ (4630672051779/12500000000000 : ℝ)^4199
        have hw : |(4500764157/10000000000 : ℝ)|=(4500764157/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3948372939/10000000000 : ℝ)|^5223 ≤ (15738655996573/50000000000000 : ℝ)^4199
        have hw : |(3948372939/10000000000 : ℝ)|=(3948372939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3948372897/10000000000 : ℝ)|^5223 ≤ (15738655788329/50000000000000 : ℝ)^4199
        have hw : |(3948372897/10000000000 : ℝ)|=(3948372897/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_4 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1796412383/10000000000 : ℝ)*x 0 + (2588471323/5000000000 : ℝ)*x 1 + (323558953/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1796412383/10000000000 : ℝ)^5223 ≤ (11818975701669/100000000000000 : ℝ)^4199 := by
    have hnat : (1796412383 : ℕ)^5223*100000000000000^4199 ≤ 11818975701669^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1796412383 10000000000 11818975701669 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2588471323/5000000000 : ℝ)^5223 ≤ (44090508955471/100000000000000 : ℝ)^4199 := by
    have hnat : (2588471323 : ℕ)^5223*100000000000000^4199 ≤ 44090508955471^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2588471323 5000000000 44090508955471 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323558953/625000000 : ℝ)^5223 ≤ (44090515332853/100000000000000 : ℝ)^4199 := by
    have hnat : (323558953 : ℕ)^5223*100000000000000^4199 ≤ 44090515332853^4199*625000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323558953 625000000 44090515332853 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1796412383/10000000000 : ℝ), (2588471323/5000000000 : ℝ), (323558953/625000000 : ℝ)] ![(11818975701669/100000000000000 : ℝ), (44090508955471/100000000000000 : ℝ), (44090515332853/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1796412383/10000000000 : ℝ)|^5223 ≤ (11818975701669/100000000000000 : ℝ)^4199
        have hw : |(-1796412383/10000000000 : ℝ)|=(1796412383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2588471323/5000000000 : ℝ)|^5223 ≤ (44090508955471/100000000000000 : ℝ)^4199
        have hw : |(2588471323/5000000000 : ℝ)|=(2588471323/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323558953/625000000 : ℝ)|^5223 ≤ (44090515332853/100000000000000 : ℝ)^4199
        have hw : |(323558953/625000000 : ℝ)|=(323558953/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_5 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392795963/10000000000 : ℝ)*x 0 + (-754884431/5000000000 : ℝ)*x 1 + (647117863/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392795963/10000000000 : ℝ)^5223 ≤ (46388690549717/100000000000000 : ℝ)^4199 := by
    have hnat : (5392795963 : ℕ)^5223*100000000000000^4199 ≤ 46388690549717^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392795963 10000000000 46388690549717 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (754884431/5000000000 : ℝ)^5223 ≤ (2380199439001/25000000000000 : ℝ)^4199 := by
    have hnat : (754884431 : ℕ)^5223*25000000000000^4199 ≤ 2380199439001^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      754884431 5000000000 2380199439001 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (647117863/1250000000 : ℝ)^5223 ≤ (8818102337727/20000000000000 : ℝ)^4199 := by
    have hnat : (647117863 : ℕ)^5223*20000000000000^4199 ≤ 8818102337727^4199*1250000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      647117863 1250000000 8818102337727 20000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392795963/10000000000 : ℝ), (-754884431/5000000000 : ℝ), (647117863/1250000000 : ℝ)] ![(46388690549717/100000000000000 : ℝ), (2380199439001/25000000000000 : ℝ), (8818102337727/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392795963/10000000000 : ℝ)|^5223 ≤ (46388690549717/100000000000000 : ℝ)^4199
        have hw : |(5392795963/10000000000 : ℝ)|=(5392795963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-754884431/5000000000 : ℝ)|^5223 ≤ (2380199439001/25000000000000 : ℝ)^4199
        have hw : |(-754884431/5000000000 : ℝ)|=(754884431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(647117863/1250000000 : ℝ)|^5223 ≤ (8818102337727/20000000000000 : ℝ)^4199
        have hw : |(647117863/1250000000 : ℝ)|=(647117863/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_6 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5392795909/10000000000 : ℝ)*x 0 + (5176942967/10000000000 : ℝ)*x 1 + (-94360553/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5392795909/10000000000 : ℝ)^5223 ≤ (11597172492983/25000000000000 : ℝ)^4199 := by
    have hnat : (5392795909 : ℕ)^5223*25000000000000^4199 ≤ 11597172492983^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392795909 10000000000 11597172492983 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5176942967/10000000000 : ℝ)^5223 ≤ (8818102471207/20000000000000 : ℝ)^4199 := by
    have hnat : (5176942967 : ℕ)^5223*20000000000000^4199 ≤ 8818102471207^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5176942967 10000000000 8818102471207 20000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94360553/625000000 : ℝ)^5223 ≤ (2380199411547/25000000000000 : ℝ)^4199 := by
    have hnat : (94360553 : ℕ)^5223*25000000000000^4199 ≤ 2380199411547^4199*625000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94360553 625000000 2380199411547 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5392795909/10000000000 : ℝ), (5176942967/10000000000 : ℝ), (-94360553/625000000 : ℝ)] ![(11597172492983/25000000000000 : ℝ), (8818102471207/20000000000000 : ℝ), (2380199411547/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5392795909/10000000000 : ℝ)|^5223 ≤ (11597172492983/25000000000000 : ℝ)^4199
        have hw : |(5392795909/10000000000 : ℝ)|=(5392795909/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5176942967/10000000000 : ℝ)|^5223 ≤ (8818102471207/20000000000000 : ℝ)^4199
        have hw : |(5176942967/10000000000 : ℝ)|=(5176942967/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94360553/625000000 : ℝ)|^5223 ≤ (2380199411547/25000000000000 : ℝ)^4199
        have hw : |(-94360553/625000000 : ℝ)|=(94360553/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_7 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (929909589/2500000000 : ℝ)*x 0 + (2169046331/5000000000 : ℝ)*x 1 + (4338091913/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (929909589/2500000000 : ℝ)^5223 ≤ (3653169108151/12500000000000 : ℝ)^4199 := by
    have hnat : (929909589 : ℕ)^5223*12500000000000^4199 ≤ 3653169108151^4199*2500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      929909589 2500000000 3653169108151 12500000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2169046331/5000000000 : ℝ)^5223 ≤ (17693663680239/50000000000000 : ℝ)^4199 := by
    have hnat : (2169046331 : ℕ)^5223*50000000000000^4199 ≤ 17693663680239^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2169046331 5000000000 17693663680239 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4338091913/10000000000 : ℝ)^5223 ≤ (35387319760631/100000000000000 : ℝ)^4199 := by
    have hnat : (4338091913 : ℕ)^5223*100000000000000^4199 ≤ 35387319760631^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4338091913 10000000000 35387319760631 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(929909589/2500000000 : ℝ), (2169046331/5000000000 : ℝ), (4338091913/10000000000 : ℝ)] ![(3653169108151/12500000000000 : ℝ), (17693663680239/50000000000000 : ℝ), (35387319760631/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(929909589/2500000000 : ℝ)|^5223 ≤ (3653169108151/12500000000000 : ℝ)^4199
        have hw : |(929909589/2500000000 : ℝ)|=(929909589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2169046331/5000000000 : ℝ)|^5223 ≤ (17693663680239/50000000000000 : ℝ)^4199
        have hw : |(2169046331/5000000000 : ℝ)|=(2169046331/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4338091913/10000000000 : ℝ)|^5223 ≤ (35387319760631/100000000000000 : ℝ)^4199
        have hw : |(4338091913/10000000000 : ℝ)|=(4338091913/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_8 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-165162139/1000000000 : ℝ)*x 0 + (78065063/156250000 : ℝ)*x 1 + (5465737339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165162139/1000000000 : ℝ)^5223 ≤ (532297250857/5000000000000 : ℝ)^4199 := by
    have hnat : (165162139 : ℕ)^5223*5000000000000^4199 ≤ 532297250857^4199*1000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165162139 1000000000 532297250857 5000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (78065063/156250000 : ℝ)^5223 ≤ (2636476848939/6250000000000 : ℝ)^4199 := by
    have hnat : (78065063 : ℕ)^5223*6250000000000^4199 ≤ 2636476848939^4199*156250000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      78065063 156250000 2636476848939 6250000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5465737339/10000000000 : ℝ)^5223 ≤ (11792606348519/25000000000000 : ℝ)^4199 := by
    have hnat : (5465737339 : ℕ)^5223*25000000000000^4199 ≤ 11792606348519^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465737339 10000000000 11792606348519 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-165162139/1000000000 : ℝ), (78065063/156250000 : ℝ), (5465737339/10000000000 : ℝ)] ![(532297250857/5000000000000 : ℝ), (2636476848939/6250000000000 : ℝ), (11792606348519/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-165162139/1000000000 : ℝ)|^5223 ≤ (532297250857/5000000000000 : ℝ)^4199
        have hw : |(-165162139/1000000000 : ℝ)|=(165162139/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(78065063/156250000 : ℝ)|^5223 ≤ (2636476848939/6250000000000 : ℝ)^4199
        have hw : |(78065063/156250000 : ℝ)|=(78065063/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5465737339/10000000000 : ℝ)|^5223 ≤ (11792606348519/25000000000000 : ℝ)^4199
        have hw : |(5465737339/10000000000 : ℝ)|=(5465737339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_9 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2598241439/5000000000 : ℝ)*x 0 + (-1382366331/10000000000 : ℝ)*x 1 + (2732868877/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2598241439/5000000000 : ℝ)^5223 ≤ (44297606651633/100000000000000 : ℝ)^4199 := by
    have hnat : (2598241439 : ℕ)^5223*100000000000000^4199 ≤ 44297606651633^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2598241439 5000000000 44297606651633 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1382366331/10000000000 : ℝ)^5223 ≤ (4265981739473/50000000000000 : ℝ)^4199 := by
    have hnat : (1382366331 : ℕ)^5223*50000000000000^4199 ≤ 4265981739473^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1382366331 10000000000 4265981739473 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2732868877/5000000000 : ℝ)^5223 ≤ (47170429849031/100000000000000 : ℝ)^4199 := by
    have hnat : (2732868877 : ℕ)^5223*100000000000000^4199 ≤ 47170429849031^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2732868877 5000000000 47170429849031 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2598241439/5000000000 : ℝ), (-1382366331/10000000000 : ℝ), (2732868877/5000000000 : ℝ)] ![(44297606651633/100000000000000 : ℝ), (4265981739473/50000000000000 : ℝ), (47170429849031/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2598241439/5000000000 : ℝ)|^5223 ≤ (44297606651633/100000000000000 : ℝ)^4199
        have hw : |(2598241439/5000000000 : ℝ)|=(2598241439/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1382366331/10000000000 : ℝ)|^5223 ≤ (4265981739473/50000000000000 : ℝ)^4199
        have hw : |(-1382366331/10000000000 : ℝ)|=(1382366331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2732868877/5000000000 : ℝ)|^5223 ≤ (47170429849031/100000000000000 : ℝ)^4199
        have hw : |(2732868877/5000000000 : ℝ)|=(2732868877/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_10 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5196484159/10000000000 : ℝ)*x 0 + (5465736393/10000000000 : ℝ)*x 1 + (-276473293/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5196484159/10000000000 : ℝ)^5223 ≤ (22148810117291/50000000000000 : ℝ)^4199 := by
    have hnat : (5196484159 : ℕ)^5223*50000000000000^4199 ≤ 22148810117291^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5196484159 10000000000 22148810117291 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5465736393/10000000000 : ℝ)^5223 ≤ (47170415238927/100000000000000 : ℝ)^4199 := by
    have hnat : (5465736393 : ℕ)^5223*100000000000000^4199 ≤ 47170415238927^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5465736393 10000000000 47170415238927 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276473293/2000000000 : ℝ)^5223 ≤ (2132991126921/25000000000000 : ℝ)^4199 := by
    have hnat : (276473293 : ℕ)^5223*25000000000000^4199 ≤ 2132991126921^4199*2000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276473293 2000000000 2132991126921 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5196484159/10000000000 : ℝ), (5465736393/10000000000 : ℝ), (-276473293/2000000000 : ℝ)] ![(22148810117291/50000000000000 : ℝ), (47170415238927/100000000000000 : ℝ), (2132991126921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5196484159/10000000000 : ℝ)|^5223 ≤ (22148810117291/50000000000000 : ℝ)^4199
        have hw : |(5196484159/10000000000 : ℝ)|=(5196484159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5465736393/10000000000 : ℝ)|^5223 ≤ (47170415238927/100000000000000 : ℝ)^4199
        have hw : |(5465736393/10000000000 : ℝ)|=(5465736393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276473293/2000000000 : ℝ)|^5223 ≤ (2132991126921/25000000000000 : ℝ)^4199
        have hw : |(-276473293/2000000000 : ℝ)|=(276473293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_11 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2316500761/5000000000 : ℝ)*x 0 + (969929599/2500000000 : ℝ)*x 1 + (3879721269/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2316500761/5000000000 : ℝ)^5223 ≤ (38404058530687/100000000000000 : ℝ)^4199 := by
    have hnat : (2316500761 : ℕ)^5223*100000000000000^4199 ≤ 38404058530687^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2316500761 5000000000 38404058530687 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969929599/2500000000 : ℝ)^5223 ≤ (481218070997/1562500000000 : ℝ)^4199 := by
    have hnat : (969929599 : ℕ)^5223*1562500000000^4199 ≤ 481218070997^4199*2500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969929599 2500000000 481218070997 1562500000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3879721269/10000000000 : ℝ)^5223 ≤ (3079798491199/10000000000000 : ℝ)^4199 := by
    have hnat : (3879721269 : ℕ)^5223*10000000000000^4199 ≤ 3079798491199^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3879721269 10000000000 3079798491199 10000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2316500761/5000000000 : ℝ), (969929599/2500000000 : ℝ), (3879721269/10000000000 : ℝ)] ![(38404058530687/100000000000000 : ℝ), (481218070997/1562500000000 : ℝ), (3079798491199/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2316500761/5000000000 : ℝ)|^5223 ≤ (38404058530687/100000000000000 : ℝ)^4199
        have hw : |(2316500761/5000000000 : ℝ)|=(2316500761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(969929599/2500000000 : ℝ)|^5223 ≤ (481218070997/1562500000000 : ℝ)^4199
        have hw : |(969929599/2500000000 : ℝ)|=(969929599/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3879721269/10000000000 : ℝ)|^5223 ≤ (3079798491199/10000000000000 : ℝ)^4199
        have hw : |(3879721269/10000000000 : ℝ)|=(3879721269/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_12 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1262114823/10000000000 : ℝ)*x 0 + (699325341/1250000000 : ℝ)*x 1 + (1287930353/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1262114823/10000000000 : ℝ)^5223 ≤ (7618790239359/100000000000000 : ℝ)^4199 := by
    have hnat : (1262114823 : ℕ)^5223*100000000000000^4199 ≤ 7618790239359^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1262114823 10000000000 7618790239359 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (699325341/1250000000 : ℝ)^5223 ≤ (48557726981557/100000000000000 : ℝ)^4199 := by
    have hnat : (699325341 : ℕ)^5223*100000000000000^4199 ≤ 48557726981557^4199*1250000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      699325341 1250000000 48557726981557 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1287930353/2500000000 : ℝ)^5223 ≤ (21911741383159/50000000000000 : ℝ)^4199 := by
    have hnat : (1287930353 : ℕ)^5223*50000000000000^4199 ≤ 21911741383159^4199*2500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1287930353 2500000000 21911741383159 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1262114823/10000000000 : ℝ), (699325341/1250000000 : ℝ), (1287930353/2500000000 : ℝ)] ![(7618790239359/100000000000000 : ℝ), (48557726981557/100000000000000 : ℝ), (21911741383159/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1262114823/10000000000 : ℝ)|^5223 ≤ (7618790239359/100000000000000 : ℝ)^4199
        have hw : |(-1262114823/10000000000 : ℝ)|=(1262114823/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(699325341/1250000000 : ℝ)|^5223 ≤ (48557726981557/100000000000000 : ℝ)^4199
        have hw : |(699325341/1250000000 : ℝ)|=(699325341/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1287930353/2500000000 : ℝ)|^5223 ≤ (21911741383159/50000000000000 : ℝ)^4199
        have hw : |(1287930353/2500000000 : ℝ)|=(1287930353/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_13 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5409971347/10000000000 : ℝ)*x 0 + (-1520364781/10000000000 : ℝ)*x 1 + (5151721467/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409971347/10000000000 : ℝ)^5223 ≤ (23286266800411/50000000000000 : ℝ)^4199 := by
    have hnat : (5409971347 : ℕ)^5223*50000000000000^4199 ≤ 23286266800411^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409971347 10000000000 23286266800411 50000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1520364781/10000000000 : ℝ)^5223 ≤ (9603983038333/100000000000000 : ℝ)^4199 := by
    have hnat : (1520364781 : ℕ)^5223*100000000000000^4199 ≤ 9603983038333^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1520364781 10000000000 9603983038333 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5151721467/10000000000 : ℝ)^5223 ≤ (10955870837069/25000000000000 : ℝ)^4199 := by
    have hnat : (5151721467 : ℕ)^5223*25000000000000^4199 ≤ 10955870837069^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5151721467 10000000000 10955870837069 25000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409971347/10000000000 : ℝ), (-1520364781/10000000000 : ℝ), (5151721467/10000000000 : ℝ)] ![(23286266800411/50000000000000 : ℝ), (9603983038333/100000000000000 : ℝ), (10955870837069/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409971347/10000000000 : ℝ)|^5223 ≤ (23286266800411/50000000000000 : ℝ)^4199
        have hw : |(5409971347/10000000000 : ℝ)|=(5409971347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1520364781/10000000000 : ℝ)|^5223 ≤ (9603983038333/100000000000000 : ℝ)^4199
        have hw : |(-1520364781/10000000000 : ℝ)|=(1520364781/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5151721467/10000000000 : ℝ)|^5223 ≤ (10955870837069/25000000000000 : ℝ)^4199
        have hw : |(5151721467/10000000000 : ℝ)|=(5151721467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_14 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5409971333/10000000000 : ℝ)*x 0 + (643965179/1250000000 : ℝ)*x 1 + (-760182423/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5409971333/10000000000 : ℝ)^5223 ≤ (46572533450909/100000000000000 : ℝ)^4199 := by
    have hnat : (5409971333 : ℕ)^5223*100000000000000^4199 ≤ 46572533450909^4199*10000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5409971333 10000000000 46572533450909 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (643965179/1250000000 : ℝ)^5223 ≤ (43823482977939/100000000000000 : ℝ)^4199 := by
    have hnat : (643965179 : ℕ)^5223*100000000000000^4199 ≤ 43823482977939^4199*1250000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      643965179 1250000000 43823482977939 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (760182423/5000000000 : ℝ)^5223 ≤ (9603983549063/100000000000000 : ℝ)^4199 := by
    have hnat : (760182423 : ℕ)^5223*100000000000000^4199 ≤ 9603983549063^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      760182423 5000000000 9603983549063 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5409971333/10000000000 : ℝ), (643965179/1250000000 : ℝ), (-760182423/5000000000 : ℝ)] ![(46572533450909/100000000000000 : ℝ), (43823482977939/100000000000000 : ℝ), (9603983549063/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5409971333/10000000000 : ℝ)|^5223 ≤ (46572533450909/100000000000000 : ℝ)^4199
        have hw : |(5409971333/10000000000 : ℝ)|=(5409971333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(643965179/1250000000 : ℝ)|^5223 ≤ (43823482977939/100000000000000 : ℝ)^4199
        have hw : |(643965179/1250000000 : ℝ)|=(643965179/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-760182423/5000000000 : ℝ)|^5223 ≤ (9603983549063/100000000000000 : ℝ)^4199
        have hw : |(-760182423/5000000000 : ℝ)|=(760182423/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1700_box_15 (p : ℝ) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (113639021/312500000 : ℝ)*x 0 + (1094500361/2500000000 : ℝ)*x 1 + (2189000589/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (113639021/312500000 : ℝ)^5223 ≤ (2841455993889/10000000000000 : ℝ)^4199 := by
    have hnat : (113639021 : ℕ)^5223*10000000000000^4199 ≤ 2841455993889^4199*312500000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      113639021 312500000 2841455993889 10000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094500361/2500000000 : ℝ)^5223 ≤ (35792721377001/100000000000000 : ℝ)^4199 := by
    have hnat : (1094500361 : ℕ)^5223*100000000000000^4199 ≤ 35792721377001^4199*2500000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094500361 2500000000 35792721377001 100000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2189000589/5000000000 : ℝ)^5223 ≤ (7158543734391/20000000000000 : ℝ)^4199 := by
    have hnat : (2189000589 : ℕ)^5223*20000000000000^4199 ≤ 7158543734391^4199*5000000000^5223 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2189000589 5000000000 7158543734391 20000000000000 5223 4199 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (5223/1024 : ℝ)) 5223 4199 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(113639021/312500000 : ℝ), (1094500361/2500000000 : ℝ), (2189000589/5000000000 : ℝ)] ![(2841455993889/10000000000000 : ℝ), (35792721377001/100000000000000 : ℝ), (7158543734391/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(113639021/312500000 : ℝ)|^5223 ≤ (2841455993889/10000000000000 : ℝ)^4199
        have hw : |(113639021/312500000 : ℝ)|=(113639021/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094500361/2500000000 : ℝ)|^5223 ≤ (35792721377001/100000000000000 : ℝ)^4199
        have hw : |(1094500361/2500000000 : ℝ)|=(1094500361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2189000589/5000000000 : ℝ)|^5223 ≤ (7158543734391/20000000000000 : ℝ)^4199
        have hw : |(2189000589/5000000000 : ℝ)|=(2189000589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1700_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4291/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4963/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(2083/3125 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(58167/100000 : ℝ) ∧ (1623/2000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (90279/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4291/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (4963/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4291/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (4963/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4291/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (4963/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4291/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (4963/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4291/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (4963/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4291/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (4963/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (4963/50000 : ℝ) ^ (5215/1024 : ℝ) ≤ (777675925695773/100000000000000000000 : ℝ) := by
    have hpowers : (4963/50000 : ℝ)^5215 ≤ (777675925695773/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4963 : ℕ)^5215*100000000000000000000^1024 ≤ 777675925695773^1024*50000^5215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4963 50000 777675925695773 100000000000000000000 5215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4963/50000 : ℝ)) (X := (777675925695773/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4291/25000 : ℝ) ^ (5215/1024 : ℝ) ≤ (3162463092367547/25000000000000000000 : ℝ) := by
    have hpowers : (4291/25000 : ℝ)^5215 ≤ (3162463092367547/25000000000000000000 : ℝ)^1024 := by
      have hnat : (4291 : ℕ)^5215*25000000000000000000^1024 ≤ 3162463092367547^1024*25000^5215 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4291 25000 3162463092367547 25000000000000000000 5215 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4291/25000 : ℝ)) (X := (3162463092367547/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000777675925695773/50000000000000000000 : ℝ) ≤ (10000030540179139/10000000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (50000777675925695773/50000000000000000000 : ℝ)^1024 ≤ (10000030540179139/10000000000000000 : ℝ)^5215 := by
      have hnat : (50000777675925695773 : ℕ)^1024*10000000000000000^5215 ≤ 10000030540179139^5215*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000777675925695773 50000000000000000000 10000030540179139 10000000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000030540179139/10000000000000000 : ℝ)) (X := (50000777675925695773/50000000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100013427528295165961/100000000000000000000 : ℝ) ≤ (10000263644241/10000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (100013427528295165961/100000000000000000000 : ℝ)^1024 ≤ (10000263644241/10000000000000 : ℝ)^5215 := by
      have hnat : (100013427528295165961 : ℕ)^1024*10000000000000^5215 ≤ 10000263644241^5215*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100013427528295165961 100000000000000000000 10000263644241 10000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000263644241/10000000000000 : ℝ)) (X := (100013427528295165961/100000000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12503162463092367547/12500000000000000000 : ℝ) ≤ (10000496748302861/10000000000000000 : ℝ) ^ (5215/1024 : ℝ) := by
    have hpowers : (12503162463092367547/12500000000000000000 : ℝ)^1024 ≤ (10000496748302861/10000000000000000 : ℝ)^5215 := by
      have hnat : (12503162463092367547 : ℕ)^1024*10000000000000000^5215 ≤ 10000496748302861^5215*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503162463092367547 12500000000000000000 10000496748302861 10000000000000000 1024 5215 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000496748302861/10000000000000000 : ℝ)) (X := (12503162463092367547/12500000000000000000 : ℝ)) (by norm_num) 5215 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(777675925695773/100000000000000000000 : ℝ) ≤ ((93994277231143563/94000000000000000 : ℝ)+2*(21191278351/65800000000000 : ℝ)*(4963/50000 : ℝ))^(5215/1024 : ℝ) := by
    rw [show (93994277231143563/94000000000000000 : ℝ)+2*(21191278351/65800000000000 : ℝ)*(4963/50000 : ℝ)=(10000030540179139/10000000000000000 : ℝ) by norm_num, show 1+2*(777675925695773/100000000000000000000 : ℝ)=(50000777675925695773/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3162463092367547/25000000000000000000 : ℝ)+(777675925695773/100000000000000000000 : ℝ) ≤ ((93994277231143563/94000000000000000 : ℝ)+(21191278351/65800000000000 : ℝ)*((4291/25000 : ℝ)+(4963/50000 : ℝ)))^(5215/1024 : ℝ) := by
    rw [show (93994277231143563/94000000000000000 : ℝ)+(21191278351/65800000000000 : ℝ)*((4291/25000 : ℝ)+(4963/50000 : ℝ))=(10000263644241/10000000000000 : ℝ) by norm_num, show 1+(3162463092367547/25000000000000000000 : ℝ)+(777675925695773/100000000000000000000 : ℝ)=(100013427528295165961/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3162463092367547/25000000000000000000 : ℝ) ≤ ((93994277231143563/94000000000000000 : ℝ)+2*(21191278351/65800000000000 : ℝ)*(4291/25000 : ℝ))^(5215/1024 : ℝ) := by
    rw [show (93994277231143563/94000000000000000 : ℝ)+2*(21191278351/65800000000000 : ℝ)*(4291/25000 : ℝ)=(10000496748302861/10000000000000000 : ℝ) by norm_num, show 1+2*(3162463092367547/25000000000000000000 : ℝ)=(12503162463092367547/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (93994277231143563/94000000000000000 : ℝ)*(X 1 0+X 2 0)+(21191278351/65800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (4963/50000 : ℝ)) (hi := (4291/25000 : ℝ)) (c := (93994277231143563/94000000000000000 : ℝ)) (alpha := (21191278351/65800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (93994277231143563/94000000000000000 : ℝ)*(X 0 1+X 2 1)+(21191278351/65800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (4963/50000 : ℝ)) (hi := (4291/25000 : ℝ)) (c := (93994277231143563/94000000000000000 : ℝ)) (alpha := (21191278351/65800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (93994277231143563/94000000000000000 : ℝ)*(X 0 2+X 1 2)+(21191278351/65800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (5215/1024 : ℝ)) (lo := (4963/50000 : ℝ)) (hi := (4291/25000 : ℝ)) (c := (93994277231143563/94000000000000000 : ℝ)) (alpha := (21191278351/65800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-70154609/625000000 : ℝ)*X 0 0+(1084515941/2000000000 : ℝ)*X 0 1+(5422579637/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1045161377/2000000000 : ℝ)*X 1 0+(-1402092119/10000000000 : ℝ)*X 1 1+(5422579647/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((522580689/1000000000 : ℝ)*X 2 0+(2711289809/5000000000 : ℝ)*X 2 1+(-175261519/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4500764157/10000000000 : ℝ)*X 0 0+(3948372939/10000000000 : ℝ)*X 0 1+(3948372897/10000000000 : ℝ)*X 0 2+(4500764157/10000000000 : ℝ)*X 1 0+(3948372939/10000000000 : ℝ)*X 1 1+(3948372897/10000000000 : ℝ)*X 1 2+(4500764157/10000000000 : ℝ)*X 2 0+(3948372939/10000000000 : ℝ)*X 2 1+(3948372897/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1796412383/10000000000 : ℝ)*X 0 0+(2588471323/5000000000 : ℝ)*X 0 1+(323558953/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5392795963/10000000000 : ℝ)*X 1 0+(-754884431/5000000000 : ℝ)*X 1 1+(647117863/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5392795909/10000000000 : ℝ)*X 2 0+(5176942967/10000000000 : ℝ)*X 2 1+(-94360553/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((929909589/2500000000 : ℝ)*X 0 0+(2169046331/5000000000 : ℝ)*X 0 1+(4338091913/10000000000 : ℝ)*X 0 2+(929909589/2500000000 : ℝ)*X 1 0+(2169046331/5000000000 : ℝ)*X 1 1+(4338091913/10000000000 : ℝ)*X 1 2+(929909589/2500000000 : ℝ)*X 2 0+(2169046331/5000000000 : ℝ)*X 2 1+(4338091913/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-165162139/1000000000 : ℝ)*X 0 0+(78065063/156250000 : ℝ)*X 0 1+(5465737339/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2598241439/5000000000 : ℝ)*X 1 0+(-1382366331/10000000000 : ℝ)*X 1 1+(2732868877/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((5196484159/10000000000 : ℝ)*X 2 0+(5465736393/10000000000 : ℝ)*X 2 1+(-276473293/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2316500761/5000000000 : ℝ)*X 0 0+(969929599/2500000000 : ℝ)*X 0 1+(3879721269/10000000000 : ℝ)*X 0 2+(2316500761/5000000000 : ℝ)*X 1 0+(969929599/2500000000 : ℝ)*X 1 1+(3879721269/10000000000 : ℝ)*X 1 2+(2316500761/5000000000 : ℝ)*X 2 0+(969929599/2500000000 : ℝ)*X 2 1+(3879721269/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-1262114823/10000000000 : ℝ)*X 0 0+(699325341/1250000000 : ℝ)*X 0 1+(1287930353/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5409971347/10000000000 : ℝ)*X 1 0+(-1520364781/10000000000 : ℝ)*X 1 1+(5151721467/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5409971333/10000000000 : ℝ)*X 2 0+(643965179/1250000000 : ℝ)*X 2 1+(-760182423/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((113639021/312500000 : ℝ)*X 0 0+(1094500361/2500000000 : ℝ)*X 0 1+(2189000589/5000000000 : ℝ)*X 0 2+(113639021/312500000 : ℝ)*X 1 0+(1094500361/2500000000 : ℝ)*X 1 1+(2189000589/5000000000 : ℝ)*X 1 2+(113639021/312500000 : ℝ)*X 2 0+(1094500361/2500000000 : ℝ)*X 2 1+(2189000589/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1700_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-2083/3125 : ℝ) ≤ (-2192914142155848148077006999/3290000000000000000000000000 : ℝ) := by norm_num
    linear_combination (68417047/100000000000000 : ℝ)*(upper1) + (936519/100000000000000 : ℝ)*(upper3) + (2370449/20000000000000 : ℝ)*(lower4) + (1039949/5000000000000 : ℝ)*(upper5) + (1331208497770707/100000000000000 : ℝ)*(major0) + (1331208497770707/100000000000000 : ℝ)*(major1) + (1331208497770707/100000000000000 : ℝ)*(major2) + (199006341849027/10000000000000 : ℝ)*(sp4) + (497515951528921/25000000000000 : ℝ)*(sp5) + (248758056250133/12500000000000 : ℝ)*(sp6) + (347281112544311/50000000000000 : ℝ)*(sp7) + (515755397/50000000000000 : ℝ)*(sp12) + (643885381/100000000000000 : ℝ)*(sp13) + (8295549553/100000000000000 : ℝ)*(sp15) + (27782820825527/4000000000000 : ℝ)*(f.failure) + (248758056250133/12500000000000 : ℝ)*(f.sum) + (15119067154883/3290000000000000000000000000 : ℝ)*base66 + (322099239034233287/65800000000000000000000000000000 : ℝ)*base67 + (147400780793766713/65800000000000000000000000000000 : ℝ)*base70 + (830601229259966713/65800000000000000000000000000000 : ℝ)*base72 + (17660084726327/3290000000000000000000000000 : ℝ)*base73 + (123500308091233287/65800000000000000000000000000000 : ℝ)*base75 + (114518039513433287/65800000000000000000000000000000 : ℝ)*base77 + (49303362454566713/65800000000000000000000000000000 : ℝ)*base80 + (8477599663763/3290000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (121711/100000000000000000000 : ℝ)*base90 + (121711/100000000000000000000 : ℝ)*base92 + (121711/100000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (58167/100000 : ℝ) ≤ (9568917601662413391350217283791/16450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1871913/100000000000000 : ℝ)*(upper2) + (157077/5000000000000 : ℝ)*(upper3) + (2480377/50000000000000 : ℝ)*(lower5) + (716563118675539/50000000000000 : ℝ)*(major0) + (716563118675539/50000000000000 : ℝ)*(major1) + (716563118675539/50000000000000 : ℝ)*(major2) + (2099115343979001/100000000000000 : ℝ)*(sp0) + (65597346951391/3125000000000 : ℝ)*(sp1) + (2099114106110371/100000000000000 : ℝ)*(sp2) + (149549386332471/20000000000000 : ℝ)*(sp3) + (125604869/100000000000000 : ℝ)*(sp7) + (33900237/20000000000000 : ℝ)*(sp8) + (205517837/50000000000000 : ℝ)*(sp9) + (281473963/20000000000000 : ℝ)*(sp10) + (93468382158403/12500000000000 : ℝ)*(f.failure) + (1049557756740093/50000000000000 : ℝ)*(f.sum) + (1494130064741/411250000000000000000000000 : ℝ)*base65 + (577733977619471801/32900000000000000000000000000000 : ℝ)*base68 + (529437795413871801/32900000000000000000000000000000 : ℝ)*base70 + (392371585664171801/32900000000000000000000000000000 : ℝ)*base72 + (288900902341/102812500000000000000000000 : ℝ)*base74 + (368334197567071801/32900000000000000000000000000000 : ℝ)*base76 + (196493601614871801/32900000000000000000000000000000 : ℝ)*base78 + (401753290608671801/32900000000000000000000000000000 : ℝ)*base80 + (45705991329/102812500000000000000000000 : ℝ)*base81 + (4423221/312500000000000000000 : ℝ)*base89 + (4423221/312500000000000000000 : ℝ)*base91 + (4423221/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (1623/2000 : ℝ) ≤ (13349623442442901869487895478843/16450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (38134127/100000000000000 : ℝ)*(upper0) + (39506869/100000000000000 : ℝ)*(lower1) + (32361317/10000000000000 : ℝ)*(lower3) + (27595407/100000000000000 : ℝ)*(lower5) + (1458932204199259/100000000000000 : ℝ)*(major0) + (1458932204199259/100000000000000 : ℝ)*(major1) + (1458932204199259/100000000000000 : ℝ)*(major2) + (1344660167/20000000000000 : ℝ)*(sp0) + (23257565723/25000000000000 : ℝ)*(sp1) + (4366441087/12500000000000 : ℝ)*(sp3) + (2129595213865791/100000000000000 : ℝ)*(sp8) + (1064754453451867/50000000000000 : ℝ)*(sp9) + (1064800968583313/50000000000000 : ℝ)*(sp10) + (761176631005229/100000000000000 : ℝ)*(sp11) + (380605781266963/50000000000000 : ℝ)*(f.failure) + (1064800968583313/50000000000000 : ℝ)*(f.sum) + (5030982698709/3290000000000000000000000000 : ℝ)*base65 + (441256766882628719/65800000000000000000000000000000 : ℝ)*base67 + (2867027740971281/65800000000000000000000000000000 : ℝ)*base70 + (217381974554028719/65800000000000000000000000000000 : ℝ)*base71 + (28479838852631/3290000000000000000000000000 : ℝ)*base74 + (807370121306228719/65800000000000000000000000000000 : ℝ)*base75 + (134895116794428719/65800000000000000000000000000000 : ℝ)*base77 + (712139770242828719/65800000000000000000000000000000 : ℝ)*base79 + (12430163934239/3290000000000000000000000000 : ℝ)*base81 + (10121141/1250000000000000000000 : ℝ)*base89 + (10121141/1250000000000000000000 : ℝ)*base91 + (10121141/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-90279/100000 : ℝ) ≤ (-7425256509852856299108756455721/8225000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (10287681/100000000000000 : ℝ)*(upper1) + (39197/160000000000 : ℝ)*(upper3) + (89403/2000000000000 : ℝ)*(lower4) + (753547638431473/50000000000000 : ℝ)*(major0) + (753547638431473/50000000000000 : ℝ)*(major1) + (753547638431473/50000000000000 : ℝ)*(major2) + (227892601/100000000000000 : ℝ)*(sp4) + (469154061/50000000000000 : ℝ)*(sp5) + (1700459703/100000000000000 : ℝ)*(sp6) + (1026145389/50000000000000 : ℝ)*(sp7) + (1128970726662249/50000000000000 : ℝ)*(sp12) + (141121296431811/6250000000000 : ℝ)*(sp13) + (564484995189349/25000000000000 : ℝ)*(sp14) + (98292380647743/12500000000000 : ℝ)*(sp15) + (393170548736361/50000000000000 : ℝ)*(f.failure) + (1128970840608549/50000000000000 : ℝ)*(f.sum) + (838978454271/205625000000000000000000000 : ℝ)*base65 + (312251371435661907/32900000000000000000000000000000 : ℝ)*base68 + (654341511838861907/32900000000000000000000000000000 : ℝ)*base70 + (95173569938461907/32900000000000000000000000000000 : ℝ)*base72 + (3922405566017/1645000000000000000000000000 : ℝ)*base74 + (770465537398738093/32900000000000000000000000000000 : ℝ)*base75 + (351288941085761907/32900000000000000000000000000000 : ℝ)*base78 + (268615347466361907/32900000000000000000000000000000 : ℝ)*base80 + (67189877760053/1645000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base87 + (6197327/1250000000000000000000 : ℝ)*base89 + (6197327/1250000000000000000000 : ℝ)*base91 + (6197327/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1700_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4291/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (4963/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2083/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(58167/100000 : ℝ) else (1623/2000 : ℝ) ≤ X j i ∧ X j i ≤ (90279/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1700_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1700_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (859/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1239/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2083/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(58167/100000 : ℝ) else (1623/2000 : ℝ) ≤ X j i ∧ X j i ≤ (90279/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1700_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1700_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1700_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (5215/1024 : ℝ) ≤ p) (hpb : p ≤ (5223/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (47914807/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (859/5000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1239/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(2083/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(58167/100000 : ℝ) else (1623/2000 : ℝ) ≤ X j i ∧ X j i ≤ (90279/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1700_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
