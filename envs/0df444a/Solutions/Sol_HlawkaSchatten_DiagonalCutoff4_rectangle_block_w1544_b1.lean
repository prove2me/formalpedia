-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1544_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:08:41.978991+00:00
-- url     : https://prove2.me/submissions/68f2d2df-cd9c-4a46-8969-eaf410c49a39

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
theorem support_rectangle_w1544_s3_0 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1821418417/10000000000 : ℝ)*x 0 + (339460351/625000000 : ℝ)*x 1 + (2608528061/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1821418417/10000000000 : ℝ)^4585 ≤ (11161778106539/100000000000000 : ℝ)^3561 := by
    have hnat : (1821418417 : ℕ)^4585*100000000000000^3561 ≤ 11161778106539^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821418417 10000000000 11161778106539 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (339460351/625000000 : ℝ)^4585 ≤ (4557005661021/10000000000000 : ℝ)^3561 := by
    have hnat : (339460351 : ℕ)^4585*10000000000000^3561 ≤ 4557005661021^3561*625000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      339460351 625000000 4557005661021 10000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2608528061/5000000000 : ℝ)^4585 ≤ (8653633054833/20000000000000 : ℝ)^3561 := by
    have hnat : (2608528061 : ℕ)^4585*20000000000000^3561 ≤ 8653633054833^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2608528061 5000000000 8653633054833 20000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1821418417/10000000000 : ℝ), (339460351/625000000 : ℝ), (2608528061/5000000000 : ℝ)] ![(11161778106539/100000000000000 : ℝ), (4557005661021/10000000000000 : ℝ), (8653633054833/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1821418417/10000000000 : ℝ)|^4585 ≤ (11161778106539/100000000000000 : ℝ)^3561
        have hw : |(-1821418417/10000000000 : ℝ)|=(1821418417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(339460351/625000000 : ℝ)|^4585 ≤ (4557005661021/10000000000000 : ℝ)^3561
        have hw : |(339460351/625000000 : ℝ)|=(339460351/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2608528061/5000000000 : ℝ)|^4585 ≤ (8653633054833/20000000000000 : ℝ)^3561
        have hw : |(2608528061/5000000000 : ℝ)|=(2608528061/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s3_1 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (66879407/125000000 : ℝ)*x 0 + (-1931159507/10000000000 : ℝ)*x 1 + (1304264169/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66879407/125000000 : ℝ)^4585 ≤ (44696769197767/100000000000000 : ℝ)^3561 := by
    have hnat : (66879407 : ℕ)^4585*100000000000000^3561 ≤ 44696769197767^3561*125000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66879407 125000000 44696769197767 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1931159507/10000000000 : ℝ)^4585 ≤ (12035059599301/100000000000000 : ℝ)^3561 := by
    have hnat : (1931159507 : ℕ)^4585*100000000000000^3561 ≤ 12035059599301^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931159507 10000000000 12035059599301 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1304264169/2500000000 : ℝ)^4585 ≤ (5408521398757/12500000000000 : ℝ)^3561 := by
    have hnat : (1304264169 : ℕ)^4585*12500000000000^3561 ≤ 5408521398757^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1304264169 2500000000 5408521398757 12500000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66879407/125000000 : ℝ), (-1931159507/10000000000 : ℝ), (1304264169/2500000000 : ℝ)] ![(44696769197767/100000000000000 : ℝ), (12035059599301/100000000000000 : ℝ), (5408521398757/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66879407/125000000 : ℝ)|^4585 ≤ (44696769197767/100000000000000 : ℝ)^3561
        have hw : |(66879407/125000000 : ℝ)|=(66879407/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1931159507/10000000000 : ℝ)|^4585 ≤ (12035059599301/100000000000000 : ℝ)^3561
        have hw : |(-1931159507/10000000000 : ℝ)|=(1931159507/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1304264169/2500000000 : ℝ)|^4585 ≤ (5408521398757/12500000000000 : ℝ)^3561
        have hw : |(1304264169/2500000000 : ℝ)|=(1304264169/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s3_2 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337587939/2500000000 : ℝ)*x 0 + (5217057003/10000000000 : ℝ)*x 1 + (-1931160149/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337587939/2500000000 : ℝ)^4585 ≤ (22348380274869/50000000000000 : ℝ)^3561 := by
    have hnat : (1337587939 : ℕ)^4585*50000000000000^3561 ≤ 22348380274869^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337587939 2500000000 22348380274869 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5217057003/10000000000 : ℝ)^4585 ≤ (21634087340963/50000000000000 : ℝ)^3561 := by
    have hnat : (5217057003 : ℕ)^4585*50000000000000^3561 ≤ 21634087340963^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5217057003 10000000000 21634087340963 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1931160149/10000000000 : ℝ)^4585 ≤ (12035064750787/100000000000000 : ℝ)^3561 := by
    have hnat : (1931160149 : ℕ)^4585*100000000000000^3561 ≤ 12035064750787^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1931160149 10000000000 12035064750787 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337587939/2500000000 : ℝ), (5217057003/10000000000 : ℝ), (-1931160149/10000000000 : ℝ)] ![(22348380274869/50000000000000 : ℝ), (21634087340963/50000000000000 : ℝ), (12035064750787/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337587939/2500000000 : ℝ)|^4585 ≤ (22348380274869/50000000000000 : ℝ)^3561
        have hw : |(1337587939/2500000000 : ℝ)|=(1337587939/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5217057003/10000000000 : ℝ)|^4585 ≤ (21634087340963/50000000000000 : ℝ)^3561
        have hw : |(5217057003/10000000000 : ℝ)|=(5217057003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1931160149/10000000000 : ℝ)|^4585 ≤ (12035064750787/100000000000000 : ℝ)^3561
        have hw : |(-1931160149/10000000000 : ℝ)|=(1931160149/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s3_3 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4254885247/10000000000 : ℝ)*x 0 + (1003103117/2500000000 : ℝ)*x 1 + (4509355889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4254885247/10000000000 : ℝ)^4585 ≤ (1331162132169/4000000000000 : ℝ)^3561 := by
    have hnat : (4254885247 : ℕ)^4585*4000000000000^3561 ≤ 1331162132169^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4254885247 10000000000 1331162132169 4000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1003103117/2500000000 : ℝ)^4585 ≤ (30857519102023/100000000000000 : ℝ)^3561 := by
    have hnat : (1003103117 : ℕ)^4585*100000000000000^3561 ≤ 30857519102023^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1003103117 2500000000 30857519102023 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4509355889/10000000000 : ℝ)^4585 ≤ (35863427572841/100000000000000 : ℝ)^3561 := by
    have hnat : (4509355889 : ℕ)^4585*100000000000000^3561 ≤ 35863427572841^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4509355889 10000000000 35863427572841 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4254885247/10000000000 : ℝ), (1003103117/2500000000 : ℝ), (4509355889/10000000000 : ℝ)] ![(1331162132169/4000000000000 : ℝ), (30857519102023/100000000000000 : ℝ), (35863427572841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4254885247/10000000000 : ℝ)|^4585 ≤ (1331162132169/4000000000000 : ℝ)^3561
        have hw : |(4254885247/10000000000 : ℝ)|=(4254885247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1003103117/2500000000 : ℝ)|^4585 ≤ (30857519102023/100000000000000 : ℝ)^3561
        have hw : |(1003103117/2500000000 : ℝ)|=(1003103117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4509355889/10000000000 : ℝ)|^4585 ≤ (35863427572841/100000000000000 : ℝ)^3561
        have hw : |(4509355889/10000000000 : ℝ)|=(4509355889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s3_4 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-182144739/1000000000 : ℝ)*x 0 + (1043637853/2000000000 : ℝ)*x 1 + (5430224283/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (182144739/1000000000 : ℝ)^4585 ≤ (5581003355707/50000000000000 : ℝ)^3561 := by
    have hnat : (182144739 : ℕ)^4585*50000000000000^3561 ≤ 5581003355707^3561*1000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      182144739 1000000000 5581003355707 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1043637853/2000000000 : ℝ)^4585 ≤ (2705016620121/6250000000000 : ℝ)^3561 := by
    have hnat : (1043637853 : ℕ)^4585*6250000000000^3561 ≤ 2705016620121^3561*2000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043637853 2000000000 2705016620121 6250000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5430224283/10000000000 : ℝ)^4585 ≤ (5694715918291/12500000000000 : ℝ)^3561 := by
    have hnat : (5430224283 : ℕ)^4585*12500000000000^3561 ≤ 5694715918291^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430224283 10000000000 5694715918291 12500000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-182144739/1000000000 : ℝ), (1043637853/2000000000 : ℝ), (5430224283/10000000000 : ℝ)] ![(5581003355707/50000000000000 : ℝ), (2705016620121/6250000000000 : ℝ), (5694715918291/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-182144739/1000000000 : ℝ)|^4585 ≤ (5581003355707/50000000000000 : ℝ)^3561
        have hw : |(-182144739/1000000000 : ℝ)|=(182144739/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1043637853/2000000000 : ℝ)|^4585 ≤ (2705016620121/6250000000000 : ℝ)^3561
        have hw : |(1043637853/2000000000 : ℝ)|=(1043637853/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5430224283/10000000000 : ℝ)|^4585 ≤ (5694715918291/12500000000000 : ℝ)^3561
        have hw : |(5430224283/10000000000 : ℝ)|=(5430224283/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s3_5 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2646918449/5000000000 : ℝ)*x 0 + (-26843629/156250000 : ℝ)*x 1 + (2715112177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2646918449/5000000000 : ℝ)^4585 ≤ (44089797879907/100000000000000 : ℝ)^3561 := by
    have hnat : (2646918449 : ℕ)^4585*100000000000000^3561 ≤ 44089797879907^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2646918449 5000000000 44089797879907 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (26843629/156250000 : ℝ)^4585 ≤ (5176236993199/50000000000000 : ℝ)^3561 := by
    have hnat : (26843629 : ℕ)^4585*50000000000000^3561 ≤ 5176236993199^3561*156250000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      26843629 156250000 5176236993199 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2715112177/5000000000 : ℝ)^4585 ≤ (45557728113283/100000000000000 : ℝ)^3561 := by
    have hnat : (2715112177 : ℕ)^4585*100000000000000^3561 ≤ 45557728113283^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2715112177 5000000000 45557728113283 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2646918449/5000000000 : ℝ), (-26843629/156250000 : ℝ), (2715112177/5000000000 : ℝ)] ![(44089797879907/100000000000000 : ℝ), (5176236993199/50000000000000 : ℝ), (45557728113283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2646918449/5000000000 : ℝ)|^4585 ≤ (44089797879907/100000000000000 : ℝ)^3561
        have hw : |(2646918449/5000000000 : ℝ)|=(2646918449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-26843629/156250000 : ℝ)|^4585 ≤ (5176236993199/50000000000000 : ℝ)^3561
        have hw : |(-26843629/156250000 : ℝ)|=(26843629/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2715112177/5000000000 : ℝ)|^4585 ≤ (45557728113283/100000000000000 : ℝ)^3561
        have hw : |(2715112177/5000000000 : ℝ)|=(2715112177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s3_6 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5293837333/10000000000 : ℝ)*x 0 + (5430224139/10000000000 : ℝ)*x 1 + (-343598391/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5293837333/10000000000 : ℝ)^4585 ≤ (11022450636153/25000000000000 : ℝ)^3561 := by
    have hnat : (5293837333 : ℕ)^4585*25000000000000^3561 ≤ 11022450636153^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5293837333 10000000000 11022450636153 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430224139/10000000000 : ℝ)^4585 ≤ (45557725790813/100000000000000 : ℝ)^3561 := by
    have hnat : (5430224139 : ℕ)^4585*100000000000000^3561 ≤ 45557725790813^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430224139 10000000000 45557725790813 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343598391/2000000000 : ℝ)^4585 ≤ (5176235825511/50000000000000 : ℝ)^3561 := by
    have hnat : (343598391 : ℕ)^4585*50000000000000^3561 ≤ 5176235825511^3561*2000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343598391 2000000000 5176235825511 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5293837333/10000000000 : ℝ), (5430224139/10000000000 : ℝ), (-343598391/2000000000 : ℝ)] ![(11022450636153/25000000000000 : ℝ), (45557725790813/100000000000000 : ℝ), (5176235825511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5293837333/10000000000 : ℝ)|^4585 ≤ (11022450636153/25000000000000 : ℝ)^3561
        have hw : |(5293837333/10000000000 : ℝ)|=(5293837333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430224139/10000000000 : ℝ)|^4585 ≤ (45557725790813/100000000000000 : ℝ)^3561
        have hw : |(5430224139/10000000000 : ℝ)|=(5430224139/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-343598391/2000000000 : ℝ)|^4585 ≤ (5176235825511/50000000000000 : ℝ)^3561
        have hw : |(-343598391/2000000000 : ℝ)|=(343598391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s3_7 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2127476537/5000000000 : ℝ)*x 0 + (2253364481/5000000000 : ℝ)*x 1 + (803011927/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127476537/5000000000 : ℝ)^4585 ≤ (415996704459/1250000000000 : ℝ)^3561 := by
    have hnat : (2127476537 : ℕ)^4585*1250000000000^3561 ≤ 415996704459^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127476537 5000000000 415996704459 1250000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2253364481/5000000000 : ℝ)^4585 ≤ (8959132450801/25000000000000 : ℝ)^3561 := by
    have hnat : (2253364481 : ℕ)^4585*25000000000000^3561 ≤ 8959132450801^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2253364481 5000000000 8959132450801 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (803011927/2000000000 : ℝ)^4585 ≤ (772093345711/2500000000000 : ℝ)^3561 := by
    have hnat : (803011927 : ℕ)^4585*2500000000000^3561 ≤ 772093345711^3561*2000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803011927 2000000000 772093345711 2500000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127476537/5000000000 : ℝ), (2253364481/5000000000 : ℝ), (803011927/2000000000 : ℝ)] ![(415996704459/1250000000000 : ℝ), (8959132450801/25000000000000 : ℝ), (772093345711/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127476537/5000000000 : ℝ)|^4585 ≤ (415996704459/1250000000000 : ℝ)^3561
        have hw : |(2127476537/5000000000 : ℝ)|=(2127476537/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2253364481/5000000000 : ℝ)|^4585 ≤ (8959132450801/25000000000000 : ℝ)^3561
        have hw : |(2253364481/5000000000 : ℝ)|=(2253364481/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(803011927/2000000000 : ℝ)|^4585 ≤ (772093345711/2500000000000 : ℝ)^3561
        have hw : |(803011927/2000000000 : ℝ)|=(803011927/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1544_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7943/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1333/12500 : ℝ)*pair X i i ≤ pair X i h) :
    (1099/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3883/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7943/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1333/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7943/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1333/12500 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7943/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1333/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7943/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1333/12500 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7943/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1333/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7943/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1333/12500 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1333/12500 : ℝ) ^ (4583/1024 : ℝ) ≤ (2230196021372441/50000000000000000000 : ℝ) := by
    have hpowers : (1333/12500 : ℝ)^4583 ≤ (2230196021372441/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1333 : ℕ)^4583*50000000000000000000^1024 ≤ 2230196021372441^1024*12500^4583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1333 12500 2230196021372441 50000000000000000000 4583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1333/12500 : ℝ)) (X := (2230196021372441/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7943/50000 : ℝ) ^ (4583/1024 : ℝ) ≤ (26550456492136823/100000000000000000000 : ℝ) := by
    have hpowers : (7943/50000 : ℝ)^4583 ≤ (26550456492136823/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7943 : ℕ)^4583*100000000000000000000^1024 ≤ 26550456492136823^1024*50000^4583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7943 50000 26550456492136823 100000000000000000000 4583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7943/50000 : ℝ)) (X := (26550456492136823/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002230196021372441/25000000000000000000 : ℝ) ≤ (5000099657064231/5000000000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (25002230196021372441/25000000000000000000 : ℝ)^1024 ≤ (5000099657064231/5000000000000000 : ℝ)^4583 := by
      have hnat : (25002230196021372441 : ℕ)^1024*5000000000000000^4583 ≤ 5000099657064231^4583*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002230196021372441 25000000000000000000 5000099657064231 5000000000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000099657064231/5000000000000000 : ℝ)) (X := (25002230196021372441/25000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20006202169706976341/20000000000000000000 : ℝ) ≤ (5000346402858127/5000000000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (20006202169706976341/20000000000000000000 : ℝ)^1024 ≤ (5000346402858127/5000000000000000 : ℝ)^4583 := by
      have hnat : (20006202169706976341 : ℕ)^1024*5000000000000000^4583 ≤ 5000346402858127^4583*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20006202169706976341 20000000000000000000 5000346402858127 5000000000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000346402858127/5000000000000000 : ℝ)) (X := (20006202169706976341/20000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026550456492136823/50000000000000000000 : ℝ) ≤ (5000593148652023/5000000000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (50026550456492136823/50000000000000000000 : ℝ)^1024 ≤ (5000593148652023/5000000000000000 : ℝ)^4583 := by
      have hnat : (50026550456492136823 : ℕ)^1024*5000000000000000^4583 ≤ 5000593148652023^4583*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026550456492136823 50000000000000000000 5000593148652023 5000000000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000593148652023/5000000000000000 : ℝ)) (X := (50026550456492136823/50000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2230196021372441/50000000000000000000 : ℝ) ≤ ((1864661272492657171/1865000000000000000 : ℝ)+2*(4406174891/4662500000000 : ℝ)*(1333/12500 : ℝ))^(4583/1024 : ℝ) := by
    rw [show (1864661272492657171/1865000000000000000 : ℝ)+2*(4406174891/4662500000000 : ℝ)*(1333/12500 : ℝ)=(5000099657064231/5000000000000000 : ℝ) by norm_num, show 1+2*(2230196021372441/50000000000000000000 : ℝ)=(25002230196021372441/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26550456492136823/100000000000000000000 : ℝ)+(2230196021372441/50000000000000000000 : ℝ) ≤ ((1864661272492657171/1865000000000000000 : ℝ)+(4406174891/4662500000000 : ℝ)*((7943/50000 : ℝ)+(1333/12500 : ℝ)))^(4583/1024 : ℝ) := by
    rw [show (1864661272492657171/1865000000000000000 : ℝ)+(4406174891/4662500000000 : ℝ)*((7943/50000 : ℝ)+(1333/12500 : ℝ))=(5000346402858127/5000000000000000 : ℝ) by norm_num, show 1+(26550456492136823/100000000000000000000 : ℝ)+(2230196021372441/50000000000000000000 : ℝ)=(20006202169706976341/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26550456492136823/100000000000000000000 : ℝ) ≤ ((1864661272492657171/1865000000000000000 : ℝ)+2*(4406174891/4662500000000 : ℝ)*(7943/50000 : ℝ))^(4583/1024 : ℝ) := by
    rw [show (1864661272492657171/1865000000000000000 : ℝ)+2*(4406174891/4662500000000 : ℝ)*(7943/50000 : ℝ)=(5000593148652023/5000000000000000 : ℝ) by norm_num, show 1+2*(26550456492136823/100000000000000000000 : ℝ)=(50026550456492136823/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1864661272492657171/1865000000000000000 : ℝ)*(X 1 0+X 2 0)+(4406174891/4662500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (1333/12500 : ℝ)) (hi := (7943/50000 : ℝ)) (c := (1864661272492657171/1865000000000000000 : ℝ)) (alpha := (4406174891/4662500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1864661272492657171/1865000000000000000 : ℝ)*(X 0 1+X 2 1)+(4406174891/4662500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (1333/12500 : ℝ)) (hi := (7943/50000 : ℝ)) (c := (1864661272492657171/1865000000000000000 : ℝ)) (alpha := (4406174891/4662500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1864661272492657171/1865000000000000000 : ℝ)*(X 0 2+X 1 2)+(4406174891/4662500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (1333/12500 : ℝ)) (hi := (7943/50000 : ℝ)) (c := (1864661272492657171/1865000000000000000 : ℝ)) (alpha := (4406174891/4662500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1821418417/10000000000 : ℝ)*X 0 0+(339460351/625000000 : ℝ)*X 0 1+(2608528061/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((66879407/125000000 : ℝ)*X 1 0+(-1931159507/10000000000 : ℝ)*X 1 1+(1304264169/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337587939/2500000000 : ℝ)*X 2 0+(5217057003/10000000000 : ℝ)*X 2 1+(-1931160149/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4254885247/10000000000 : ℝ)*X 0 0+(1003103117/2500000000 : ℝ)*X 0 1+(4509355889/10000000000 : ℝ)*X 0 2+(4254885247/10000000000 : ℝ)*X 1 0+(1003103117/2500000000 : ℝ)*X 1 1+(4509355889/10000000000 : ℝ)*X 1 2+(4254885247/10000000000 : ℝ)*X 2 0+(1003103117/2500000000 : ℝ)*X 2 1+(4509355889/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-182144739/1000000000 : ℝ)*X 0 0+(1043637853/2000000000 : ℝ)*X 0 1+(5430224283/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2646918449/5000000000 : ℝ)*X 1 0+(-26843629/156250000 : ℝ)*X 1 1+(2715112177/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5293837333/10000000000 : ℝ)*X 2 0+(5430224139/10000000000 : ℝ)*X 2 1+(-343598391/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2127476537/5000000000 : ℝ)*X 0 0+(2253364481/5000000000 : ℝ)*X 0 1+(803011927/2000000000 : ℝ)*X 0 2+(2127476537/5000000000 : ℝ)*X 1 0+(2253364481/5000000000 : ℝ)*X 1 1+(803011927/2000000000 : ℝ)*X 1 2+(2127476537/5000000000 : ℝ)*X 2 0+(2253364481/5000000000 : ℝ)*X 2 1+(803011927/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (367392683341597432633271019/46625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1577365683/100000000000000 : ℝ)*(base19) + (49789093/5000000000000 : ℝ)*(base23) + (17958391/25000000000000 : ℝ)*(upper2) + (116448961/20000000000000 : ℝ)*(upper3) + (3339271457833963/100000000000000 : ℝ)*(major0) + (3339271457833963/100000000000000 : ℝ)*(major1) + (3339271457833963/100000000000000 : ℝ)*(major2) + (2333095766746163/50000000000000 : ℝ)*(sp0) + (1166552540306563/25000000000000 : ℝ)*(sp1) + (4666209355895133/100000000000000 : ℝ)*(sp2) + (80492564602757/4000000000000 : ℝ)*(sp3) + (20205099609/100000000000000 : ℝ)*(sp4) + (1386914943/100000000000000 : ℝ)*(sp6) + (4199837299/25000000000000 : ℝ)*(sp7) + (50308272860453/2500000000000 : ℝ)*(f.failure) + (933242347718387/20000000000000 : ℝ)*(f.sum) + (13573981733591/1865000000000000000000000000 : ℝ)*base66 + (218360342072001327/186500000000000000000000000000000 : ℝ)*base68 + (1681741217883501327/186500000000000000000000000000000 : ℝ)*base70 + (912392386751001327/186500000000000000000000000000000 : ℝ)*base72 + (464131890241/116562500000000000000000000 : ℝ)*base74 + (235640434161998673/186500000000000000000000000000000 : ℝ)*base75 + (2147015942616501327/186500000000000000000000000000000 : ℝ)*base78 + (3089325540859501327/186500000000000000000000000000000 : ℝ)*base80 + (11000980877331/1865000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base87 + (412639/125000000000000000000 : ℝ)*base90 + (412639/125000000000000000000 : ℝ)*base92 + (412639/125000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (192964647361810644798269781/23312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (436414437/50000000000000 : ℝ)*(base19) + (1500574049/100000000000000 : ℝ)*(base23) + (92159941/50000000000000 : ℝ)*(upper3) + (60252447/100000000000000 : ℝ)*(lower4) + (18809767/20000000000000 : ℝ)*(upper5) + (1687522592854863/50000000000000 : ℝ)*(major0) + (1687522592854863/50000000000000 : ℝ)*(major1) + (1687522592854863/50000000000000 : ℝ)*(major2) + (58176821/500000000000 : ℝ)*(sp1) + (11737619733/50000000000000 : ℝ)*(sp2) + (4716201012060191/100000000000000 : ℝ)*(sp4) + (4716188503867117/100000000000000 : ℝ)*(sp5) + (4716176036246677/100000000000000 : ℝ)*(sp6) + (12711806771557/625000000000 : ℝ)*(sp7) + (12711806771557/625000000000 : ℝ)*(f.failure) + (4716201012060191/100000000000000 : ℝ)*(f.sum) + (2913225451711/932500000000000000000000000 : ℝ)*base66 + (929627305713622573/93250000000000000000000000000000 : ℝ)*base67 + (1872233162750122573/93250000000000000000000000000000 : ℝ)*base69 + (397154243127872573/93250000000000000000000000000000 : ℝ)*base71 + (107639160601/233125000000000000000000000 : ℝ)*base73 + (549132359063872573/93250000000000000000000000000000 : ℝ)*base75 + (801154303807122573/93250000000000000000000000000000 : ℝ)*base77 + (319099006405877427/93250000000000000000000000000000 : ℝ)*base80 + (9860429933113/1865000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (225991/31250000000000000000 : ℝ)*base90 + (225991/31250000000000000000 : ℝ)*base92 + (225991/31250000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1544_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7943/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1333/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3883/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1544_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1544_s4_0 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-455430361/2500000000 : ℝ)*x 0 + (5429346307/10000000000 : ℝ)*x 1 + (5218874833/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (455430361/2500000000 : ℝ)^4585 ≤ (11164169123967/100000000000000 : ℝ)^3561 := by
    have hnat : (455430361 : ℕ)^4585*100000000000000^3561 ≤ 11164169123967^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      455430361 2500000000 11164169123967 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429346307/10000000000 : ℝ)^4585 ≤ (22774121753389/50000000000000 : ℝ)^3561 := by
    have hnat : (5429346307 : ℕ)^4585*50000000000000^3561 ≤ 22774121753389^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429346307 10000000000 22774121753389 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5218874833/10000000000 : ℝ)^4585 ≤ (43287587356771/100000000000000 : ℝ)^3561 := by
    have hnat : (5218874833 : ℕ)^4585*100000000000000^3561 ≤ 43287587356771^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218874833 10000000000 43287587356771 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-455430361/2500000000 : ℝ), (5429346307/10000000000 : ℝ), (5218874833/10000000000 : ℝ)] ![(11164169123967/100000000000000 : ℝ), (22774121753389/50000000000000 : ℝ), (43287587356771/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-455430361/2500000000 : ℝ)|^4585 ≤ (11164169123967/100000000000000 : ℝ)^3561
        have hw : |(-455430361/2500000000 : ℝ)|=(455430361/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429346307/10000000000 : ℝ)|^4585 ≤ (22774121753389/50000000000000 : ℝ)^3561
        have hw : |(5429346307/10000000000 : ℝ)|=(5429346307/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5218874833/10000000000 : ℝ)|^4585 ≤ (43287587356771/100000000000000 : ℝ)^3561
        have hw : |(5218874833/10000000000 : ℝ)|=(5218874833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s4_1 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069963679/2000000000 : ℝ)*x 0 + (-1929454877/10000000000 : ℝ)*x 1 + (41751003/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069963679/2000000000 : ℝ)^4585 ≤ (22345511832591/50000000000000 : ℝ)^3561 := by
    have hnat : (1069963679 : ℕ)^4585*50000000000000^3561 ≤ 22345511832591^3561*2000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069963679 2000000000 22345511832591 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1929454877/10000000000 : ℝ)^4585 ≤ (12021383178357/100000000000000 : ℝ)^3561 := by
    have hnat : (1929454877 : ℕ)^4585*100000000000000^3561 ≤ 12021383178357^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929454877 10000000000 12021383178357 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (41751003/80000000 : ℝ)^4585 ≤ (43287593145099/100000000000000 : ℝ)^3561 := by
    have hnat : (41751003 : ℕ)^4585*100000000000000^3561 ≤ 43287593145099^3561*80000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41751003 80000000 43287593145099 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069963679/2000000000 : ℝ), (-1929454877/10000000000 : ℝ), (41751003/80000000 : ℝ)] ![(22345511832591/50000000000000 : ℝ), (12021383178357/100000000000000 : ℝ), (43287593145099/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069963679/2000000000 : ℝ)|^4585 ≤ (22345511832591/50000000000000 : ℝ)^3561
        have hw : |(1069963679/2000000000 : ℝ)|=(1069963679/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1929454877/10000000000 : ℝ)|^4585 ≤ (12021383178357/100000000000000 : ℝ)^3561
        have hw : |(-1929454877/10000000000 : ℝ)|=(1929454877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(41751003/80000000 : ℝ)|^4585 ≤ (43287593145099/100000000000000 : ℝ)^3561
        have hw : |(41751003/80000000 : ℝ)|=(41751003/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s4_2 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (334363759/625000000 : ℝ)*x 0 + (5218873963/10000000000 : ℝ)*x 1 + (-1929454411/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334363759/625000000 : ℝ)^4585 ≤ (44691042477333/100000000000000 : ℝ)^3561 := by
    have hnat : (334363759 : ℕ)^4585*100000000000000^3561 ≤ 44691042477333^3561*625000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334363759 625000000 44691042477333 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5218873963/10000000000 : ℝ)^4585 ≤ (43287578065543/100000000000000 : ℝ)^3561 := by
    have hnat : (5218873963 : ℕ)^4585*100000000000000^3561 ≤ 43287578065543^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5218873963 10000000000 43287578065543 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1929454411/10000000000 : ℝ)^4585 ≤ (6010689720033/50000000000000 : ℝ)^3561 := by
    have hnat : (1929454411 : ℕ)^4585*50000000000000^3561 ≤ 6010689720033^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929454411 10000000000 6010689720033 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334363759/625000000 : ℝ), (5218873963/10000000000 : ℝ), (-1929454411/10000000000 : ℝ)] ![(44691042477333/100000000000000 : ℝ), (43287578065543/100000000000000 : ℝ), (6010689720033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334363759/625000000 : ℝ)|^4585 ≤ (44691042477333/100000000000000 : ℝ)^3561
        have hw : |(334363759/625000000 : ℝ)|=(334363759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5218873963/10000000000 : ℝ)|^4585 ≤ (43287578065543/100000000000000 : ℝ)^3561
        have hw : |(5218873963/10000000000 : ℝ)|=(5218873963/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1929454411/10000000000 : ℝ)|^4585 ≤ (6010689720033/50000000000000 : ℝ)^3561
        have hw : |(-1929454411/10000000000 : ℝ)|=(1929454411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s4_3 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2127539109/5000000000 : ℝ)*x 0 + (200841889/500000000 : ℝ)*x 1 + (1126221401/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127539109/5000000000 : ℝ)^4585 ≤ (6656199325773/20000000000000 : ℝ)^3561 := by
    have hnat : (2127539109 : ℕ)^4585*20000000000000^3561 ≤ 6656199325773^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127539109 5000000000 6656199325773 20000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (200841889/500000000 : ℝ)^4585 ≤ (30901345476171/100000000000000 : ℝ)^3561 := by
    have hnat : (200841889 : ℕ)^4585*100000000000000^3561 ≤ 30901345476171^3561*500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      200841889 500000000 30901345476171 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1126221401/2500000000 : ℝ)^4585 ≤ (716353157723/2000000000000 : ℝ)^3561 := by
    have hnat : (1126221401 : ℕ)^4585*2000000000000^3561 ≤ 716353157723^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1126221401 2500000000 716353157723 2000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127539109/5000000000 : ℝ), (200841889/500000000 : ℝ), (1126221401/2500000000 : ℝ)] ![(6656199325773/20000000000000 : ℝ), (30901345476171/100000000000000 : ℝ), (716353157723/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127539109/5000000000 : ℝ)|^4585 ≤ (6656199325773/20000000000000 : ℝ)^3561
        have hw : |(2127539109/5000000000 : ℝ)|=(2127539109/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(200841889/500000000 : ℝ)|^4585 ≤ (30901345476171/100000000000000 : ℝ)^3561
        have hw : |(200841889/500000000 : ℝ)|=(200841889/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1126221401/2500000000 : ℝ)|^4585 ≤ (716353157723/2000000000000 : ℝ)^3561
        have hw : |(1126221401/2500000000 : ℝ)|=(1126221401/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s4_4 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-18217493/100000000 : ℝ)*x 0 + (5219966709/10000000000 : ℝ)*x 1 + (135706159/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (18217493/100000000 : ℝ)^4585 ≤ (5582194462951/50000000000000 : ℝ)^3561 := by
    have hnat : (18217493 : ℕ)^4585*50000000000000^3561 ≤ 5582194462951^3561*100000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      18217493 100000000 5582194462951 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219966709/10000000000 : ℝ)^4585 ≤ (43299248476369/100000000000000 : ℝ)^3561 := by
    have hnat : (5219966709 : ℕ)^4585*100000000000000^3561 ≤ 43299248476369^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219966709 10000000000 43299248476369 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135706159/250000000 : ℝ)^4585 ≤ (5692045321661/12500000000000 : ℝ)^3561 := by
    have hnat : (135706159 : ℕ)^4585*12500000000000^3561 ≤ 5692045321661^3561*250000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135706159 250000000 5692045321661 12500000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-18217493/100000000 : ℝ), (5219966709/10000000000 : ℝ), (135706159/250000000 : ℝ)] ![(5582194462951/50000000000000 : ℝ), (43299248476369/100000000000000 : ℝ), (5692045321661/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-18217493/100000000 : ℝ)|^4585 ≤ (5582194462951/50000000000000 : ℝ)^3561
        have hw : |(-18217493/100000000 : ℝ)|=(18217493/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219966709/10000000000 : ℝ)|^4585 ≤ (43299248476369/100000000000000 : ℝ)^3561
        have hw : |(5219966709/10000000000 : ℝ)|=(5219966709/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135706159/250000000 : ℝ)|^4585 ≤ (5692045321661/12500000000000 : ℝ)^3561
        have hw : |(135706159/250000000 : ℝ)|=(135706159/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s4_5 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294317379/10000000000 : ℝ)*x 0 + (-344016299/2000000000 : ℝ)*x 1 + (5428246397/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294317379/10000000000 : ℝ)^4585 ≤ (44094950365707/100000000000000 : ℝ)^3561 := by
    have hnat : (5294317379 : ℕ)^4585*100000000000000^3561 ≤ 44094950365707^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294317379 10000000000 44094950365707 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344016299/2000000000 : ℝ)^4585 ≤ (10368686648981/100000000000000 : ℝ)^3561 := by
    have hnat : (344016299 : ℕ)^4585*100000000000000^3561 ≤ 10368686648981^3561*2000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344016299 2000000000 10368686648981 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428246397/10000000000 : ℝ)^4585 ≤ (45536362972927/100000000000000 : ℝ)^3561 := by
    have hnat : (5428246397 : ℕ)^4585*100000000000000^3561 ≤ 45536362972927^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428246397 10000000000 45536362972927 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294317379/10000000000 : ℝ), (-344016299/2000000000 : ℝ), (5428246397/10000000000 : ℝ)] ![(44094950365707/100000000000000 : ℝ), (10368686648981/100000000000000 : ℝ), (45536362972927/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294317379/10000000000 : ℝ)|^4585 ≤ (44094950365707/100000000000000 : ℝ)^3561
        have hw : |(5294317379/10000000000 : ℝ)|=(5294317379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-344016299/2000000000 : ℝ)|^4585 ≤ (10368686648981/100000000000000 : ℝ)^3561
        have hw : |(-344016299/2000000000 : ℝ)|=(344016299/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428246397/10000000000 : ℝ)|^4585 ≤ (45536362972927/100000000000000 : ℝ)^3561
        have hw : |(5428246397/10000000000 : ℝ)|=(5428246397/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s4_6 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529431729/1000000000 : ℝ)*x 0 + (1357061597/2500000000 : ℝ)*x 1 + (-1720081631/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529431729/1000000000 : ℝ)^4585 ≤ (22047474705647/50000000000000 : ℝ)^3561 := by
    have hnat : (529431729 : ℕ)^4585*50000000000000^3561 ≤ 22047474705647^3561*1000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529431729 1000000000 22047474705647 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357061597/2500000000 : ℝ)^4585 ≤ (22768181437859/50000000000000 : ℝ)^3561 := by
    have hnat : (1357061597 : ℕ)^4585*50000000000000^3561 ≤ 22768181437859^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357061597 2500000000 22768181437859 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1720081631/10000000000 : ℝ)^4585 ≤ (10368687704537/100000000000000 : ℝ)^3561 := by
    have hnat : (1720081631 : ℕ)^4585*100000000000000^3561 ≤ 10368687704537^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1720081631 10000000000 10368687704537 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529431729/1000000000 : ℝ), (1357061597/2500000000 : ℝ), (-1720081631/10000000000 : ℝ)] ![(22047474705647/50000000000000 : ℝ), (22768181437859/50000000000000 : ℝ), (10368687704537/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529431729/1000000000 : ℝ)|^4585 ≤ (22047474705647/50000000000000 : ℝ)^3561
        have hw : |(529431729/1000000000 : ℝ)|=(529431729/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357061597/2500000000 : ℝ)|^4585 ≤ (22768181437859/50000000000000 : ℝ)^3561
        have hw : |(1357061597/2500000000 : ℝ)|=(1357061597/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1720081631/10000000000 : ℝ)|^4585 ≤ (10368687704537/100000000000000 : ℝ)^3561
        have hw : |(-1720081631/10000000000 : ℝ)|=(1720081631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s4_7 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2127570399/5000000000 : ℝ)*x 0 + (4502352373/10000000000 : ℝ)*x 1 + (4019391861/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2127570399/5000000000 : ℝ)^4585 ≤ (33281626849499/100000000000000 : ℝ)^3561 := by
    have hnat : (2127570399 : ℕ)^4585*100000000000000^3561 ≤ 33281626849499^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2127570399 5000000000 33281626849499 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502352373/10000000000 : ℝ)^4585 ≤ (35791726814949/100000000000000 : ℝ)^3561 := by
    have hnat : (4502352373 : ℕ)^4585*100000000000000^3561 ≤ 35791726814949^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502352373 10000000000 35791726814949 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4019391861/10000000000 : ℝ)^4585 ≤ (3865830788683/12500000000000 : ℝ)^3561 := by
    have hnat : (4019391861 : ℕ)^4585*12500000000000^3561 ≤ 3865830788683^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4019391861 10000000000 3865830788683 12500000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2127570399/5000000000 : ℝ), (4502352373/10000000000 : ℝ), (4019391861/10000000000 : ℝ)] ![(33281626849499/100000000000000 : ℝ), (35791726814949/100000000000000 : ℝ), (3865830788683/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2127570399/5000000000 : ℝ)|^4585 ≤ (33281626849499/100000000000000 : ℝ)^3561
        have hw : |(2127570399/5000000000 : ℝ)|=(2127570399/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502352373/10000000000 : ℝ)|^4585 ≤ (35791726814949/100000000000000 : ℝ)^3561
        have hw : |(4502352373/10000000000 : ℝ)|=(4502352373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4019391861/10000000000 : ℝ)|^4585 ≤ (3865830788683/12500000000000 : ℝ)^3561
        have hw : |(4019391861/10000000000 : ℝ)|=(4019391861/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1544_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3883/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (11029/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1549/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3883/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1099/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3883/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1099/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3883/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1099/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3883/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1099/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3883/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1099/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3883/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1099/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
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
  have hpowlo : (1099/10000 : ℝ) ^ (4583/1024 : ℝ) ≤ (5103907068405091/100000000000000000000 : ℝ) := by
    have hpowers : (1099/10000 : ℝ)^4583 ≤ (5103907068405091/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1099 : ℕ)^4583*100000000000000000000^1024 ≤ 5103907068405091^1024*10000^4583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1099 10000 5103907068405091 100000000000000000000 4583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1099/10000 : ℝ)) (X := (5103907068405091/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3883/25000 : ℝ) ^ (4583/1024 : ℝ) ≤ (24003172359661431/100000000000000000000 : ℝ) := by
    have hpowers : (3883/25000 : ℝ)^4583 ≤ (24003172359661431/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3883 : ℕ)^4583*100000000000000000000^1024 ≤ 24003172359661431^1024*25000^4583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3883 25000 24003172359661431 100000000000000000000 4583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3883/25000 : ℝ)) (X := (24003172359661431/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005103907068405091/50000000000000000000 : ℝ) ≤ (10000228068675593/10000000000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (50005103907068405091/50000000000000000000 : ℝ)^1024 ≤ (10000228068675593/10000000000000000 : ℝ)^4583 := by
      have hnat : (50005103907068405091 : ℕ)^1024*10000000000000000^4583 ≤ 10000228068675593^4583*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005103907068405091 50000000000000000000 10000228068675593 10000000000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000228068675593/10000000000000000 : ℝ)) (X := (50005103907068405091/50000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50014553539714033261/50000000000000000000 : ℝ) ≤ (10000650278886027/10000000000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (50014553539714033261/50000000000000000000 : ℝ)^1024 ≤ (10000650278886027/10000000000000000 : ℝ)^4583 := by
      have hnat : (50014553539714033261 : ℕ)^1024*10000000000000000^4583 ≤ 10000650278886027^4583*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50014553539714033261 50000000000000000000 10000650278886027 10000000000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000650278886027/10000000000000000 : ℝ)) (X := (50014553539714033261/50000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50024003172359661431/50000000000000000000 : ℝ) ≤ (10001072489096461/10000000000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (50024003172359661431/50000000000000000000 : ℝ)^1024 ≤ (10001072489096461/10000000000000000 : ℝ)^4583 := by
      have hnat : (50024003172359661431 : ℕ)^1024*10000000000000000^4583 ≤ 10001072489096461^4583*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50024003172359661431 50000000000000000000 10001072489096461 10000000000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001072489096461/10000000000000000 : ℝ)) (X := (50024003172359661431/50000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5103907068405091/100000000000000000000 : ℝ) ≤ ((22705877853749602043/22710000000000000000 : ℝ)+2*(211105105217/227100000000000 : ℝ)*(1099/10000 : ℝ))^(4583/1024 : ℝ) := by
    rw [show (22705877853749602043/22710000000000000000 : ℝ)+2*(211105105217/227100000000000 : ℝ)*(1099/10000 : ℝ)=(10000228068675593/10000000000000000 : ℝ) by norm_num, show 1+2*(5103907068405091/100000000000000000000 : ℝ)=(50005103907068405091/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(24003172359661431/100000000000000000000 : ℝ)+(5103907068405091/100000000000000000000 : ℝ) ≤ ((22705877853749602043/22710000000000000000 : ℝ)+(211105105217/227100000000000 : ℝ)*((3883/25000 : ℝ)+(1099/10000 : ℝ)))^(4583/1024 : ℝ) := by
    rw [show (22705877853749602043/22710000000000000000 : ℝ)+(211105105217/227100000000000 : ℝ)*((3883/25000 : ℝ)+(1099/10000 : ℝ))=(10000650278886027/10000000000000000 : ℝ) by norm_num, show 1+(24003172359661431/100000000000000000000 : ℝ)+(5103907068405091/100000000000000000000 : ℝ)=(50014553539714033261/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(24003172359661431/100000000000000000000 : ℝ) ≤ ((22705877853749602043/22710000000000000000 : ℝ)+2*(211105105217/227100000000000 : ℝ)*(3883/25000 : ℝ))^(4583/1024 : ℝ) := by
    rw [show (22705877853749602043/22710000000000000000 : ℝ)+2*(211105105217/227100000000000 : ℝ)*(3883/25000 : ℝ)=(10001072489096461/10000000000000000 : ℝ) by norm_num, show 1+2*(24003172359661431/100000000000000000000 : ℝ)=(50024003172359661431/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (22705877853749602043/22710000000000000000 : ℝ)*(X 1 0+X 2 0)+(211105105217/227100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (1099/10000 : ℝ)) (hi := (3883/25000 : ℝ)) (c := (22705877853749602043/22710000000000000000 : ℝ)) (alpha := (211105105217/227100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (22705877853749602043/22710000000000000000 : ℝ)*(X 0 1+X 2 1)+(211105105217/227100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (1099/10000 : ℝ)) (hi := (3883/25000 : ℝ)) (c := (22705877853749602043/22710000000000000000 : ℝ)) (alpha := (211105105217/227100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (22705877853749602043/22710000000000000000 : ℝ)*(X 0 2+X 1 2)+(211105105217/227100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (1099/10000 : ℝ)) (hi := (3883/25000 : ℝ)) (c := (22705877853749602043/22710000000000000000 : ℝ)) (alpha := (211105105217/227100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-455430361/2500000000 : ℝ)*X 0 0+(5429346307/10000000000 : ℝ)*X 0 1+(5218874833/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1069963679/2000000000 : ℝ)*X 1 0+(-1929454877/10000000000 : ℝ)*X 1 1+(41751003/80000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334363759/625000000 : ℝ)*X 2 0+(5218873963/10000000000 : ℝ)*X 2 1+(-1929454411/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2127539109/5000000000 : ℝ)*X 0 0+(200841889/500000000 : ℝ)*X 0 1+(1126221401/2500000000 : ℝ)*X 0 2+(2127539109/5000000000 : ℝ)*X 1 0+(200841889/500000000 : ℝ)*X 1 1+(1126221401/2500000000 : ℝ)*X 1 2+(2127539109/5000000000 : ℝ)*X 2 0+(200841889/500000000 : ℝ)*X 2 1+(1126221401/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-18217493/100000000 : ℝ)*X 0 0+(5219966709/10000000000 : ℝ)*X 0 1+(135706159/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294317379/10000000000 : ℝ)*X 1 0+(-344016299/2000000000 : ℝ)*X 1 1+(5428246397/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529431729/1000000000 : ℝ)*X 2 0+(1357061597/2500000000 : ℝ)*X 2 1+(-1720081631/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2127570399/5000000000 : ℝ)*X 0 0+(4502352373/10000000000 : ℝ)*X 0 1+(4019391861/10000000000 : ℝ)*X 0 2+(2127570399/5000000000 : ℝ)*X 1 0+(4502352373/10000000000 : ℝ)*X 1 1+(4019391861/10000000000 : ℝ)*X 1 2+(2127570399/5000000000 : ℝ)*X 2 0+(4502352373/10000000000 : ℝ)*X 2 1+(4019391861/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (517440959754062378451990729/47312500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (143046877/100000000000000 : ℝ)*(base15) + (12763451/2000000000000 : ℝ)*(lower2) + (18286089/10000000000000 : ℝ)*(upper3) + (15221007/50000000000000 : ℝ)*(upper4) + (16280493/2500000000000 : ℝ)*(upper5) + (850023642667797/25000000000000 : ℝ)*(major0) + (850023642667797/25000000000000 : ℝ)*(major1) + (850023642667797/25000000000000 : ℝ)*(major2) + (4751204289330729/100000000000000 : ℝ)*(sp0) + (1187801036570963/25000000000000 : ℝ)*(sp1) + (4751187019647301/100000000000000 : ℝ)*(sp2) + (1024490549208759/50000000000000 : ℝ)*(sp3) + (4317420857/25000000000000 : ℝ)*(sp6) + (169451931/5000000000000 : ℝ)*(sp7) + (2048984487456139/100000000000000 : ℝ)*(f.failure) + (4751204289330729/100000000000000 : ℝ)*(f.sum) + (3826008100163/946250000000000000000000000 : ℝ)*base65 + (3033831770522719757/189250000000000000000000000000000 : ℝ)*base67 + (1511602641917219757/189250000000000000000000000000000 : ℝ)*base69 + (151332050376530243/189250000000000000000000000000000 : ℝ)*base72 + (9361059541893/946250000000000000000000000 : ℝ)*base73 + (1327783881679469757/189250000000000000000000000000000 : ℝ)*base75 + (2113830737006469757/189250000000000000000000000000000 : ℝ)*base77 + (1978041197555719757/189250000000000000000000000000000 : ℝ)*base79 + (15485379680227/3785000000000000000000000000 : ℝ)*base81 + (20065057/5000000000000000000000 : ℝ)*base90 + (20065057/5000000000000000000000 : ℝ)*base92 + (20065057/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2053926104041213189095464531/189250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1045887593/100000000000000 : ℝ)*(base19) + (1345440837/100000000000000 : ℝ)*(base23) + (147464783/100000000000000 : ℝ)*(upper3) + (39229717/20000000000000 : ℝ)*(lower4) + (21645541/10000000000000 : ℝ)*(upper5) + (1717948985121383/50000000000000 : ℝ)*(major0) + (1717948985121383/50000000000000 : ℝ)*(major1) + (1717948985121383/50000000000000 : ℝ)*(major2) + (4160721729/25000000000000 : ℝ)*(sp1) + (175747903/1000000000000 : ℝ)*(sp2) + (480123504130497/10000000000000 : ℝ)*(sp4) + (240060867626523/5000000000000 : ℝ)*(sp5) + (4801216121073833/100000000000000 : ℝ)*(sp6) + (2070560537414619/100000000000000 : ℝ)*(sp7) + (2070560537414619/100000000000000 : ℝ)*(f.failure) + (480123504130497/10000000000000 : ℝ)*(f.sum) + (3882311341661/1419375000000000000000000000 : ℝ)*base66 + (3301560987207385469/1135500000000000000000000000000000 : ℝ)*base67 + (10970454851766385469/1135500000000000000000000000000000 : ℝ)*base69 + (3937053373720114531/1135500000000000000000000000000000 : ℝ)*base72 + (47744764213303/11355000000000000000000000000 : ℝ)*base74 + (22214815229106385469/1135500000000000000000000000000000 : ℝ)*base75 + (1447800746875114531/1135500000000000000000000000000000 : ℝ)*base78 + (11020371622530385469/1135500000000000000000000000000000 : ℝ)*base79 + (6309621323221/5677500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (5694703/5000000000000000000000 : ℝ)*base89 + (5694703/5000000000000000000000 : ℝ)*base91 + (5694703/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1544_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3883/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1099/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11029/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1544_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1544_s5_0 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1821754749/10000000000 : ℝ)*x 0 + (1357281121/2500000000 : ℝ)*x 1 + (5219074583/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1821754749/10000000000 : ℝ)^4585 ≤ (2232886384433/20000000000000 : ℝ)^3561 := by
    have hnat : (1821754749 : ℕ)^4585*20000000000000^3561 ≤ 2232886384433^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1821754749 10000000000 2232886384433 20000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1357281121/2500000000 : ℝ)^4585 ≤ (5693230932371/12500000000000 : ℝ)^3561 := by
    have hnat : (1357281121 : ℕ)^4585*12500000000000^3561 ≤ 5693230932371^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1357281121 2500000000 5693230932371 12500000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5219074583/10000000000 : ℝ)^4585 ≤ (43289720613107/100000000000000 : ℝ)^3561 := by
    have hnat : (5219074583 : ℕ)^4585*100000000000000^3561 ≤ 43289720613107^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219074583 10000000000 43289720613107 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1821754749/10000000000 : ℝ), (1357281121/2500000000 : ℝ), (5219074583/10000000000 : ℝ)] ![(2232886384433/20000000000000 : ℝ), (5693230932371/12500000000000 : ℝ), (43289720613107/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1821754749/10000000000 : ℝ)|^4585 ≤ (2232886384433/20000000000000 : ℝ)^3561
        have hw : |(-1821754749/10000000000 : ℝ)|=(1821754749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1357281121/2500000000 : ℝ)|^4585 ≤ (5693230932371/12500000000000 : ℝ)^3561
        have hw : |(1357281121/2500000000 : ℝ)|=(1357281121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5219074583/10000000000 : ℝ)|^4585 ≤ (43289720613107/100000000000000 : ℝ)^3561
        have hw : |(5219074583/10000000000 : ℝ)|=(5219074583/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s5_1 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5349762009/10000000000 : ℝ)*x 0 + (-1929265219/10000000000 : ℝ)*x 1 + (81548041/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5349762009/10000000000 : ℝ)^4585 ≤ (11172604295327/25000000000000 : ℝ)^3561 := by
    have hnat : (5349762009 : ℕ)^4585*25000000000000^3561 ≤ 11172604295327^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5349762009 10000000000 11172604295327 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1929265219/10000000000 : ℝ)^4585 ≤ (600993087377/5000000000000 : ℝ)^3561 := by
    have hnat : (1929265219 : ℕ)^4585*5000000000000^3561 ≤ 600993087377^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1929265219 10000000000 600993087377 5000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81548041/156250000 : ℝ)^4585 ≤ (21644860525487/50000000000000 : ℝ)^3561 := by
    have hnat : (81548041 : ℕ)^4585*50000000000000^3561 ≤ 21644860525487^3561*156250000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81548041 156250000 21644860525487 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5349762009/10000000000 : ℝ), (-1929265219/10000000000 : ℝ), (81548041/156250000 : ℝ)] ![(11172604295327/25000000000000 : ℝ), (600993087377/5000000000000 : ℝ), (21644860525487/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5349762009/10000000000 : ℝ)|^4585 ≤ (11172604295327/25000000000000 : ℝ)^3561
        have hw : |(5349762009/10000000000 : ℝ)|=(5349762009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1929265219/10000000000 : ℝ)|^4585 ≤ (600993087377/5000000000000 : ℝ)^3561
        have hw : |(-1929265219/10000000000 : ℝ)|=(1929265219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81548041/156250000 : ℝ)|^4585 ≤ (21644860525487/50000000000000 : ℝ)^3561
        have hw : |(81548041/156250000 : ℝ)|=(81548041/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s5_2 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337440509/2500000000 : ℝ)*x 0 + (5219074593/10000000000 : ℝ)*x 1 + (-77170609/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337440509/2500000000 : ℝ)^4585 ≤ (22345208735859/50000000000000 : ℝ)^3561 := by
    have hnat : (1337440509 : ℕ)^4585*50000000000000^3561 ≤ 22345208735859^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337440509 2500000000 22345208735859 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5219074593/10000000000 : ℝ)^4585 ≤ (43289720719903/100000000000000 : ℝ)^3561 := by
    have hnat : (5219074593 : ℕ)^4585*100000000000000^3561 ≤ 43289720719903^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5219074593 10000000000 43289720719903 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (77170609/400000000 : ℝ)^4585 ≤ (12019861795671/100000000000000 : ℝ)^3561 := by
    have hnat : (77170609 : ℕ)^4585*100000000000000^3561 ≤ 12019861795671^3561*400000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      77170609 400000000 12019861795671 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337440509/2500000000 : ℝ), (5219074593/10000000000 : ℝ), (-77170609/400000000 : ℝ)] ![(22345208735859/50000000000000 : ℝ), (43289720719903/100000000000000 : ℝ), (12019861795671/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337440509/2500000000 : ℝ)|^4585 ≤ (22345208735859/50000000000000 : ℝ)^3561
        have hw : |(1337440509/2500000000 : ℝ)|=(1337440509/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5219074593/10000000000 : ℝ)|^4585 ≤ (43289720719903/100000000000000 : ℝ)^3561
        have hw : |(5219074593/10000000000 : ℝ)|=(5219074593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-77170609/400000000 : ℝ)|^4585 ≤ (12019861795671/100000000000000 : ℝ)^3561
        have hw : |(-77170609/400000000 : ℝ)|=(77170609/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s5_3 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4255096907/10000000000 : ℝ)*x 0 + (401732767/1000000000 : ℝ)*x 1 + (2252196601/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4255096907/10000000000 : ℝ)^4585 ≤ (8320296209693/25000000000000 : ℝ)^3561 := by
    have hnat : (4255096907 : ℕ)^4585*25000000000000^3561 ≤ 8320296209693^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4255096907 10000000000 8320296209693 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (401732767/1000000000 : ℝ)^4585 ≤ (30906197988553/100000000000000 : ℝ)^3561 := by
    have hnat : (401732767 : ℕ)^4585*100000000000000^3561 ≤ 30906197988553^3561*1000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      401732767 1000000000 30906197988553 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2252196601/5000000000 : ℝ)^4585 ≤ (8953154288079/25000000000000 : ℝ)^3561 := by
    have hnat : (2252196601 : ℕ)^4585*25000000000000^3561 ≤ 8953154288079^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2252196601 5000000000 8953154288079 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4255096907/10000000000 : ℝ), (401732767/1000000000 : ℝ), (2252196601/5000000000 : ℝ)] ![(8320296209693/25000000000000 : ℝ), (30906197988553/100000000000000 : ℝ), (8953154288079/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4255096907/10000000000 : ℝ)|^4585 ≤ (8320296209693/25000000000000 : ℝ)^3561
        have hw : |(4255096907/10000000000 : ℝ)|=(4255096907/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(401732767/1000000000 : ℝ)|^4585 ≤ (30906197988553/100000000000000 : ℝ)^3561
        have hw : |(401732767/1000000000 : ℝ)|=(401732767/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2252196601/5000000000 : ℝ)|^4585 ≤ (8953154288079/25000000000000 : ℝ)^3561
        have hw : |(2252196601/5000000000 : ℝ)|=(2252196601/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s5_4 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-910891133/5000000000 : ℝ)*x 0 + (5220163087/10000000000 : ℝ)*x 1 + (2714014047/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (910891133/5000000000 : ℝ)^4585 ≤ (2232929810061/20000000000000 : ℝ)^3561 := by
    have hnat : (910891133 : ℕ)^4585*20000000000000^3561 ≤ 2232929810061^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      910891133 5000000000 2232929810061 20000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5220163087/10000000000 : ℝ)^4585 ≤ (43301345846957/100000000000000 : ℝ)^3561 := by
    have hnat : (5220163087 : ℕ)^4585*100000000000000^3561 ≤ 43301345846957^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5220163087 10000000000 43301345846957 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714014047/5000000000 : ℝ)^4585 ≤ (45534005083981/100000000000000 : ℝ)^3561 := by
    have hnat : (2714014047 : ℕ)^4585*100000000000000^3561 ≤ 45534005083981^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714014047 5000000000 45534005083981 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-910891133/5000000000 : ℝ), (5220163087/10000000000 : ℝ), (2714014047/5000000000 : ℝ)] ![(2232929810061/20000000000000 : ℝ), (43301345846957/100000000000000 : ℝ), (45534005083981/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-910891133/5000000000 : ℝ)|^4585 ≤ (2232929810061/20000000000000 : ℝ)^3561
        have hw : |(-910891133/5000000000 : ℝ)|=(910891133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5220163087/10000000000 : ℝ)|^4585 ≤ (43301345846957/100000000000000 : ℝ)^3561
        have hw : |(5220163087/10000000000 : ℝ)|=(5220163087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714014047/5000000000 : ℝ)|^4585 ≤ (45534005083981/100000000000000 : ℝ)^3561
        have hw : |(2714014047/5000000000 : ℝ)|=(2714014047/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s5_5 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5294370777/10000000000 : ℝ)*x 0 + (-344062349/2000000000 : ℝ)*x 1 + (5428027923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5294370777/10000000000 : ℝ)^4585 ≤ (1763820919711/4000000000000 : ℝ)^3561 := by
    have hnat : (5294370777 : ℕ)^4585*4000000000000^3561 ≤ 1763820919711^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5294370777 10000000000 1763820919711 4000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (344062349/2000000000 : ℝ)^4585 ≤ (10370473754063/100000000000000 : ℝ)^3561 := by
    have hnat : (344062349 : ℕ)^4585*100000000000000^3561 ≤ 10370473754063^3561*2000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      344062349 2000000000 10370473754063 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5428027923/10000000000 : ℝ)^4585 ≤ (22767001618511/50000000000000 : ℝ)^3561 := by
    have hnat : (5428027923 : ℕ)^4585*50000000000000^3561 ≤ 22767001618511^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428027923 10000000000 22767001618511 50000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5294370777/10000000000 : ℝ), (-344062349/2000000000 : ℝ), (5428027923/10000000000 : ℝ)] ![(1763820919711/4000000000000 : ℝ), (10370473754063/100000000000000 : ℝ), (22767001618511/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5294370777/10000000000 : ℝ)|^4585 ≤ (1763820919711/4000000000000 : ℝ)^3561
        have hw : |(5294370777/10000000000 : ℝ)|=(5294370777/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-344062349/2000000000 : ℝ)|^4585 ≤ (10370473754063/100000000000000 : ℝ)^3561
        have hw : |(-344062349/2000000000 : ℝ)|=(344062349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5428027923/10000000000 : ℝ)|^4585 ≤ (22767001618511/50000000000000 : ℝ)^3561
        have hw : |(5428027923/10000000000 : ℝ)|=(5428027923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s5_6 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2647185297/5000000000 : ℝ)*x 0 + (5428027959/10000000000 : ℝ)*x 1 + (-430077987/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2647185297/5000000000 : ℝ)^4585 ≤ (1763820841213/4000000000000 : ℝ)^3561 := by
    have hnat : (2647185297 : ℕ)^4585*4000000000000^3561 ≤ 1763820841213^3561*5000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2647185297 5000000000 1763820841213 4000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5428027959/10000000000 : ℝ)^4585 ≤ (9106800725171/20000000000000 : ℝ)^3561 := by
    have hnat : (5428027959 : ℕ)^4585*20000000000000^3561 ≤ 9106800725171^3561*10000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5428027959 10000000000 9106800725171 20000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430077987/2500000000 : ℝ)^4585 ≤ (2074095065939/20000000000000 : ℝ)^3561 := by
    have hnat : (430077987 : ℕ)^4585*20000000000000^3561 ≤ 2074095065939^3561*2500000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430077987 2500000000 2074095065939 20000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2647185297/5000000000 : ℝ), (5428027959/10000000000 : ℝ), (-430077987/2500000000 : ℝ)] ![(1763820841213/4000000000000 : ℝ), (9106800725171/20000000000000 : ℝ), (2074095065939/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2647185297/5000000000 : ℝ)|^4585 ≤ (1763820841213/4000000000000 : ℝ)^3561
        have hw : |(2647185297/5000000000 : ℝ)|=(2647185297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5428027959/10000000000 : ℝ)|^4585 ≤ (9106800725171/20000000000000 : ℝ)^3561
        have hw : |(5428027959/10000000000 : ℝ)|=(5428027959/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-430077987/2500000000 : ℝ)|^4585 ≤ (2074095065939/20000000000000 : ℝ)^3561
        have hw : |(-430077987/2500000000 : ℝ)|=(430077987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1544_s5_7 (p : ℝ) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (10637903/25000000 : ℝ)*x 0 + (562733667/1250000000 : ℝ)*x 1 + (803974033/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (10637903/25000000 : ℝ)^4585 ≤ (8320458077817/25000000000000 : ℝ)^3561 := by
    have hnat : (10637903 : ℕ)^4585*25000000000000^3561 ≤ 8320458077817^3561*25000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10637903 25000000 8320458077817 25000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (562733667/1250000000 : ℝ)^4585 ≤ (35786782749223/100000000000000 : ℝ)^3561 := by
    have hnat : (562733667 : ℕ)^4585*100000000000000^3561 ≤ 35786782749223^3561*1250000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562733667 1250000000 35786782749223 100000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (803974033/2000000000 : ℝ)^4585 ≤ (1237255396919/4000000000000 : ℝ)^3561 := by
    have hnat : (803974033 : ℕ)^4585*4000000000000^3561 ≤ 1237255396919^3561*2000000000^4585 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      803974033 2000000000 1237255396919 4000000000000 4585 3561 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4585/1024 : ℝ)) 4585 3561 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(10637903/25000000 : ℝ), (562733667/1250000000 : ℝ), (803974033/2000000000 : ℝ)] ![(8320458077817/25000000000000 : ℝ), (35786782749223/100000000000000 : ℝ), (1237255396919/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(10637903/25000000 : ℝ)|^4585 ≤ (8320458077817/25000000000000 : ℝ)^3561
        have hw : |(10637903/25000000 : ℝ)|=(10637903/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(562733667/1250000000 : ℝ)|^4585 ≤ (35786782749223/100000000000000 : ℝ)^3561
        have hw : |(562733667/1250000000 : ℝ)|=(562733667/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(803974033/2000000000 : ℝ)|^4585 ≤ (1237255396919/4000000000000 : ℝ)^3561
        have hw : |(803974033/2000000000 : ℝ)|=(803974033/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1544_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (11033/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3097/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11029/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11029/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11029/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1549/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11029/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11029/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1549/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11029/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11029/100000 : ℝ) ^ (4583/1024 : ℝ) ≤ (129636771435149/2500000000000000000 : ℝ) := by
    have hpowers : (11029/100000 : ℝ)^4583 ≤ (129636771435149/2500000000000000000 : ℝ)^1024 := by
      have hnat : (11029 : ℕ)^4583*2500000000000000000^1024 ≤ 129636771435149^1024*100000^4583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11029 100000 129636771435149 2500000000000000000 4583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11029/100000 : ℝ)) (X := (129636771435149/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1549/10000 : ℝ) ^ (4583/1024 : ℝ) ≤ (4742807641159199/20000000000000000000 : ℝ) := by
    have hpowers : (1549/10000 : ℝ)^4583 ≤ (4742807641159199/20000000000000000000 : ℝ)^1024 := by
      have hnat : (1549 : ℕ)^4583*20000000000000000000^1024 ≤ 4742807641159199^1024*10000^4583 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1549 10000 4742807641159199 20000000000000000000 4583 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1549/10000 : ℝ)) (X := (4742807641159199/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250129636771435149/1250000000000000000 : ℝ) ≤ (10000231713216151/10000000000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (1250129636771435149/1250000000000000000 : ℝ)^1024 ≤ (10000231713216151/10000000000000000 : ℝ)^4583 := by
      have hnat : (1250129636771435149 : ℕ)^1024*10000000000000000^4583 ≤ 10000231713216151^4583*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250129636771435149 1250000000000000000 10000231713216151 10000000000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000231713216151/10000000000000000 : ℝ)) (X := (1250129636771435149/1250000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (20005779901812640391/20000000000000000000 : ℝ) ≤ (10000645642093687/10000000000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (20005779901812640391/20000000000000000000 : ℝ)^1024 ≤ (10000645642093687/10000000000000000 : ℝ)^4583 := by
      have hnat : (20005779901812640391 : ℕ)^1024*10000000000000000^4583 ≤ 10000645642093687^4583*20000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20005779901812640391 20000000000000000000 10000645642093687 10000000000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000645642093687/10000000000000000 : ℝ)) (X := (20005779901812640391/20000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10004742807641159199/10000000000000000000 : ℝ) ≤ (10001059570971223/10000000000000000 : ℝ) ^ (4583/1024 : ℝ) := by
    have hpowers : (10004742807641159199/10000000000000000000 : ℝ)^1024 ≤ (10001059570971223/10000000000000000 : ℝ)^4583 := by
      have hnat : (10004742807641159199 : ℕ)^1024*10000000000000000^4583 ≤ 10001059570971223^4583*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004742807641159199 10000000000000000000 10001059570971223 10000000000000000 1024 4583 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001059570971223/10000000000000000 : ℝ)) (X := (10004742807641159199/10000000000000000000 : ℝ)) (by norm_num) 4583 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(129636771435149/2500000000000000000 : ℝ) ≤ ((14867301076492186841/14870000000000000000 : ℝ)+2*(4311759141/4646875000000 : ℝ)*(11029/100000 : ℝ))^(4583/1024 : ℝ) := by
    rw [show (14867301076492186841/14870000000000000000 : ℝ)+2*(4311759141/4646875000000 : ℝ)*(11029/100000 : ℝ)=(10000231713216151/10000000000000000 : ℝ) by norm_num, show 1+2*(129636771435149/2500000000000000000 : ℝ)=(1250129636771435149/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(4742807641159199/20000000000000000000 : ℝ)+(129636771435149/2500000000000000000 : ℝ) ≤ ((14867301076492186841/14870000000000000000 : ℝ)+(4311759141/4646875000000 : ℝ)*((1549/10000 : ℝ)+(11029/100000 : ℝ)))^(4583/1024 : ℝ) := by
    rw [show (14867301076492186841/14870000000000000000 : ℝ)+(4311759141/4646875000000 : ℝ)*((1549/10000 : ℝ)+(11029/100000 : ℝ))=(10000645642093687/10000000000000000 : ℝ) by norm_num, show 1+(4742807641159199/20000000000000000000 : ℝ)+(129636771435149/2500000000000000000 : ℝ)=(20005779901812640391/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(4742807641159199/20000000000000000000 : ℝ) ≤ ((14867301076492186841/14870000000000000000 : ℝ)+2*(4311759141/4646875000000 : ℝ)*(1549/10000 : ℝ))^(4583/1024 : ℝ) := by
    rw [show (14867301076492186841/14870000000000000000 : ℝ)+2*(4311759141/4646875000000 : ℝ)*(1549/10000 : ℝ)=(10001059570971223/10000000000000000 : ℝ) by norm_num, show 1+2*(4742807641159199/20000000000000000000 : ℝ)=(10004742807641159199/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14867301076492186841/14870000000000000000 : ℝ)*(X 1 0+X 2 0)+(4311759141/4646875000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (11029/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (14867301076492186841/14870000000000000000 : ℝ)) (alpha := (4311759141/4646875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14867301076492186841/14870000000000000000 : ℝ)*(X 0 1+X 2 1)+(4311759141/4646875000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (11029/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (14867301076492186841/14870000000000000000 : ℝ)) (alpha := (4311759141/4646875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14867301076492186841/14870000000000000000 : ℝ)*(X 0 2+X 1 2)+(4311759141/4646875000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4583/1024 : ℝ)) (lo := (11029/100000 : ℝ)) (hi := (1549/10000 : ℝ)) (c := (14867301076492186841/14870000000000000000 : ℝ)) (alpha := (4311759141/4646875000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1821754749/10000000000 : ℝ)*X 0 0+(1357281121/2500000000 : ℝ)*X 0 1+(5219074583/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5349762009/10000000000 : ℝ)*X 1 0+(-1929265219/10000000000 : ℝ)*X 1 1+(81548041/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1337440509/2500000000 : ℝ)*X 2 0+(5219074593/10000000000 : ℝ)*X 2 1+(-77170609/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4255096907/10000000000 : ℝ)*X 0 0+(401732767/1000000000 : ℝ)*X 0 1+(2252196601/5000000000 : ℝ)*X 0 2+(4255096907/10000000000 : ℝ)*X 1 0+(401732767/1000000000 : ℝ)*X 1 1+(2252196601/5000000000 : ℝ)*X 1 2+(4255096907/10000000000 : ℝ)*X 2 0+(401732767/1000000000 : ℝ)*X 2 1+(2252196601/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-910891133/5000000000 : ℝ)*X 0 0+(5220163087/10000000000 : ℝ)*X 0 1+(2714014047/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5294370777/10000000000 : ℝ)*X 1 0+(-344062349/2000000000 : ℝ)*X 1 1+(5428027923/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2647185297/5000000000 : ℝ)*X 2 0+(5428027959/10000000000 : ℝ)*X 2 1+(-430077987/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((10637903/25000000 : ℝ)*X 0 0+(562733667/1250000000 : ℝ)*X 0 1+(803974033/2000000000 : ℝ)*X 0 2+(10637903/25000000 : ℝ)*X 1 0+(562733667/1250000000 : ℝ)*X 1 1+(803974033/2000000000 : ℝ)*X 1 2+(10637903/25000000 : ℝ)*X 2 0+(562733667/1250000000 : ℝ)*X 2 1+(803974033/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1544_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3850313724267914267093930151/371750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (225167137/12500000000000 : ℝ)*(base19) + (1694111771/100000000000000 : ℝ)*(base23) + (17554311/25000000000000 : ℝ)*(lower2) + (130368913/50000000000000 : ℝ)*(upper3) + (10244977/6250000000000 : ℝ)*(upper5) + (3406985838099637/100000000000000 : ℝ)*(major0) + (3406985838099637/100000000000000 : ℝ)*(major1) + (3406985838099637/100000000000000 : ℝ)*(major2) + (4760804317336753/100000000000000 : ℝ)*(sp0) + (4760832187069263/100000000000000 : ℝ)*(sp1) + (4760832294294589/100000000000000 : ℝ)*(sp2) + (256640469690563/12500000000000 : ℝ)*(sp3) + (29671069607/100000000000000 : ℝ)*(sp4) + (13585026197/100000000000000 : ℝ)*(sp7) + (2053137342550701/100000000000000 : ℝ)*(f.failure) + (119020849710159/2500000000000 : ℝ)*(f.sum) + (17522475095129/7435000000000000000000000000 : ℝ)*base65 + (9316445172178323283/1487000000000000000000000000000000 : ℝ)*base68 + (16275819652597323283/1487000000000000000000000000000000 : ℝ)*base70 + (3982452397272323283/1487000000000000000000000000000000 : ℝ)*base72 + (4938951678519/7435000000000000000000000000 : ℝ)*base73 + (4073637512382323283/1487000000000000000000000000000000 : ℝ)*base76 + (14961559032891323283/1487000000000000000000000000000000 : ℝ)*base78 + (1608662764029676717/1487000000000000000000000000000000 : ℝ)*base79 + (183506012659/1858750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (3513863/5000000000000000000000 : ℝ)*base90 + (3513863/5000000000000000000000 : ℝ)*base92 + (3513863/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (568251349487405748251946801/92937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (427834031/50000000000000 : ℝ)*(base19) + (945089799/100000000000000 : ℝ)*(base23) + (215924429/100000000000000 : ℝ)*(lower1) + (55150141/100000000000000 : ℝ)*(upper3) + (9088731/6250000000000 : ℝ)*(lower4) + (12163493/12500000000000 : ℝ)*(upper5) + (860685982639313/25000000000000 : ℝ)*(major0) + (860685982639313/25000000000000 : ℝ)*(major1) + (860685982639313/25000000000000 : ℝ)*(major2) + (906177847/50000000000000 : ℝ)*(sp1) + (1202700392006713/25000000000000 : ℝ)*(sp4) + (601349862500387/12500000000000 : ℝ)*(sp5) + (4810800622937053/100000000000000 : ℝ)*(sp6) + (1037343044638179/50000000000000 : ℝ)*(sp7) + (1037343044638179/50000000000000 : ℝ)*(f.failure) + (1202700392006713/25000000000000 : ℝ)*(f.sum) + (423209958757/929375000000000000000000000 : ℝ)*base66 + (2088645534072480233/371750000000000000000000000000000 : ℝ)*base67 + (5102545927746980233/371750000000000000000000000000000 : ℝ)*base69 + (499490854906980233/371750000000000000000000000000000 : ℝ)*base71 + (1620295848573/3717500000000000000000000000 : ℝ)*base74 + (1324780557881019767/371750000000000000000000000000000 : ℝ)*base76 + (466678473499980233/371750000000000000000000000000000 : ℝ)*base77 + (2777924791732230233/371750000000000000000000000000000 : ℝ)*base79 + (885201279643/3717500000000000000000000000 : ℝ)*base82 + (9121577/2500000000000000000000 : ℝ)*base90 + (9121577/2500000000000000000000 : ℝ)*base92 + (9121577/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1544_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1549/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11029/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1544_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1544_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7943/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1333/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1544_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1544_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1544_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4583/1024 : ℝ) ≤ p) (hpb : p ≤ (4585/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (82970237/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7943/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1333/12500 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11033/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3097/20000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1544_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
