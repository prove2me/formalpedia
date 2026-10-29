-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1577_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:29:13.505337+00:00
-- url     : https://prove2.me/submissions/afaaf143-d08d-4bb8-b290-a788f01d497e

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
theorem support_rectangle_w1577_s0_0 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1619010983/10000000000 : ℝ)*x 0 + (733063129/1250000000 : ℝ)*x 1 + (2441074271/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1619010983/10000000000 : ℝ)^4651 ≤ (4841385581271/50000000000000 : ℝ)^3627 := by
    have hnat : (1619010983 : ℕ)^4651*50000000000000^3627 ≤ 4841385581271^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1619010983 10000000000 4841385581271 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (733063129/1250000000 : ℝ)^4651 ≤ (50442525383589/100000000000000 : ℝ)^3627 := by
    have hnat : (733063129 : ℕ)^4651*100000000000000^3627 ≤ 50442525383589^3627*1250000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      733063129 1250000000 50442525383589 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2441074271/5000000000 : ℝ)^4651 ≤ (7974940687737/20000000000000 : ℝ)^3627 := by
    have hnat : (2441074271 : ℕ)^4651*20000000000000^3627 ≤ 7974940687737^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441074271 5000000000 7974940687737 20000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1619010983/10000000000 : ℝ), (733063129/1250000000 : ℝ), (2441074271/5000000000 : ℝ)] ![(4841385581271/50000000000000 : ℝ), (50442525383589/100000000000000 : ℝ), (7974940687737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1619010983/10000000000 : ℝ)|^4651 ≤ (4841385581271/50000000000000 : ℝ)^3627
        have hw : |(-1619010983/10000000000 : ℝ)|=(1619010983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(733063129/1250000000 : ℝ)|^4651 ≤ (50442525383589/100000000000000 : ℝ)^3627
        have hw : |(733063129/1250000000 : ℝ)|=(733063129/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2441074271/5000000000 : ℝ)|^4651 ≤ (7974940687737/20000000000000 : ℝ)^3627
        have hw : |(2441074271/5000000000 : ℝ)|=(2441074271/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s0_1 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2731993599/5000000000 : ℝ)*x 0 + (-541303299/2500000000 : ℝ)*x 1 + (305134283/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2731993599/5000000000 : ℝ)^4651 ≤ (9213646897209/20000000000000 : ℝ)^3627 := by
    have hnat : (2731993599 : ℕ)^4651*20000000000000^3627 ≤ 9213646897209^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2731993599 5000000000 9213646897209 20000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (541303299/2500000000 : ℝ)^4651 ≤ (14057062212187/100000000000000 : ℝ)^3627 := by
    have hnat : (541303299 : ℕ)^4651*100000000000000^3627 ≤ 14057062212187^3627*2500000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541303299 2500000000 14057062212187 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (305134283/625000000 : ℝ)^4651 ≤ (19937351646029/50000000000000 : ℝ)^3627 := by
    have hnat : (305134283 : ℕ)^4651*50000000000000^3627 ≤ 19937351646029^3627*625000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      305134283 625000000 19937351646029 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2731993599/5000000000 : ℝ), (-541303299/2500000000 : ℝ), (305134283/625000000 : ℝ)] ![(9213646897209/20000000000000 : ℝ), (14057062212187/100000000000000 : ℝ), (19937351646029/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2731993599/5000000000 : ℝ)|^4651 ≤ (9213646897209/20000000000000 : ℝ)^3627
        have hw : |(2731993599/5000000000 : ℝ)|=(2731993599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-541303299/2500000000 : ℝ)|^4651 ≤ (14057062212187/100000000000000 : ℝ)^3627
        have hw : |(-541303299/2500000000 : ℝ)|=(541303299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(305134283/625000000 : ℝ)|^4651 ≤ (19937351646029/50000000000000 : ℝ)^3627
        have hw : |(305134283/625000000 : ℝ)|=(305134283/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s0_2 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5463987261/10000000000 : ℝ)*x 0 + (2441074223/5000000000 : ℝ)*x 1 + (-2165213217/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5463987261/10000000000 : ℝ)^4651 ≤ (46068235167177/100000000000000 : ℝ)^3627 := by
    have hnat : (5463987261 : ℕ)^4651*100000000000000^3627 ≤ 46068235167177^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5463987261 10000000000 46068235167177 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2441074223/5000000000 : ℝ)^4651 ≤ (9968675608311/25000000000000 : ℝ)^3627 := by
    have hnat : (2441074223 : ℕ)^4651*25000000000000^3627 ≤ 9968675608311^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441074223 5000000000 9968675608311 25000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2165213217/10000000000 : ℝ)^4651 ≤ (2811412477403/20000000000000 : ℝ)^3627 := by
    have hnat : (2165213217 : ℕ)^4651*20000000000000^3627 ≤ 2811412477403^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2165213217 10000000000 2811412477403 20000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5463987261/10000000000 : ℝ), (2441074223/5000000000 : ℝ), (-2165213217/10000000000 : ℝ)] ![(46068235167177/100000000000000 : ℝ), (9968675608311/25000000000000 : ℝ), (2811412477403/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5463987261/10000000000 : ℝ)|^4651 ≤ (46068235167177/100000000000000 : ℝ)^3627
        have hw : |(5463987261/10000000000 : ℝ)|=(5463987261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2441074223/5000000000 : ℝ)|^4651 ≤ (9968675608311/25000000000000 : ℝ)^3627
        have hw : |(2441074223/5000000000 : ℝ)|=(2441074223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2165213217/10000000000 : ℝ)|^4651 ≤ (2811412477403/20000000000000 : ℝ)^3627
        have hw : |(-2165213217/10000000000 : ℝ)|=(2165213217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s0_3 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4128048979/10000000000 : ℝ)*x 0 + (96674011/312500000 : ℝ)*x 1 + (1355885979/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4128048979/10000000000 : ℝ)^4651 ≤ (6431158810261/20000000000000 : ℝ)^3627 := by
    have hnat : (4128048979 : ℕ)^4651*20000000000000^3627 ≤ 6431158810261^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128048979 10000000000 6431158810261 20000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (96674011/312500000 : ℝ)^4651 ≤ (694149095631/3125000000000 : ℝ)^3627 := by
    have hnat : (96674011 : ℕ)^4651*3125000000000^3627 ≤ 694149095631^3627*312500000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      96674011 312500000 694149095631 3125000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355885979/2500000000 : ℝ)^4651 ≤ (45631434868917/100000000000000 : ℝ)^3627 := by
    have hnat : (1355885979 : ℕ)^4651*100000000000000^3627 ≤ 45631434868917^3627*2500000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355885979 2500000000 45631434868917 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4128048979/10000000000 : ℝ), (96674011/312500000 : ℝ), (1355885979/2500000000 : ℝ)] ![(6431158810261/20000000000000 : ℝ), (694149095631/3125000000000 : ℝ), (45631434868917/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4128048979/10000000000 : ℝ)|^4651 ≤ (6431158810261/20000000000000 : ℝ)^3627
        have hw : |(4128048979/10000000000 : ℝ)|=(4128048979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(96674011/312500000 : ℝ)|^4651 ≤ (694149095631/3125000000000 : ℝ)^3627
        have hw : |(96674011/312500000 : ℝ)|=(96674011/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355885979/2500000000 : ℝ)|^4651 ≤ (45631434868917/100000000000000 : ℝ)^3627
        have hw : |(1355885979/2500000000 : ℝ)|=(1355885979/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s0_4 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-811006973/5000000000 : ℝ)*x 0 + (4906865543/10000000000 : ℝ)*x 1 + (1459728433/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (811006973/5000000000 : ℝ)^4651 ≤ (4852903719589/50000000000000 : ℝ)^3627 := by
    have hnat : (811006973 : ℕ)^4651*50000000000000^3627 ≤ 4852903719589^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      811006973 5000000000 4852903719589 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4906865543/10000000000 : ℝ)^4651 ≤ (313544982909/781250000000 : ℝ)^3627 := by
    have hnat : (4906865543 : ℕ)^4651*781250000000^3627 ≤ 313544982909^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4906865543 10000000000 313544982909 781250000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1459728433/2500000000 : ℝ)^4651 ≤ (10032086945569/20000000000000 : ℝ)^3627 := by
    have hnat : (1459728433 : ℕ)^4651*20000000000000^3627 ≤ 10032086945569^3627*2500000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1459728433 2500000000 10032086945569 20000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-811006973/5000000000 : ℝ), (4906865543/10000000000 : ℝ), (1459728433/2500000000 : ℝ)] ![(4852903719589/50000000000000 : ℝ), (313544982909/781250000000 : ℝ), (10032086945569/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-811006973/5000000000 : ℝ)|^4651 ≤ (4852903719589/50000000000000 : ℝ)^3627
        have hw : |(-811006973/5000000000 : ℝ)|=(811006973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4906865543/10000000000 : ℝ)|^4651 ≤ (313544982909/781250000000 : ℝ)^3627
        have hw : |(4906865543/10000000000 : ℝ)|=(4906865543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1459728433/2500000000 : ℝ)|^4651 ≤ (10032086945569/20000000000000 : ℝ)^3627
        have hw : |(1459728433/2500000000 : ℝ)|=(1459728433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s0_5 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5195427143/10000000000 : ℝ)*x 0 + (-604224259/5000000000 : ℝ)*x 1 + (5838913443/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5195427143/10000000000 : ℝ)^4651 ≤ (1349532929497/3125000000000 : ℝ)^3627 := by
    have hnat : (5195427143 : ℕ)^4651*3125000000000^3627 ≤ 1349532929497^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5195427143 10000000000 1349532929497 3125000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (604224259/5000000000 : ℝ)^4651 ≤ (665451469829/10000000000000 : ℝ)^3627 := by
    have hnat : (604224259 : ℕ)^4651*10000000000000^3627 ≤ 665451469829^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      604224259 5000000000 665451469829 10000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5838913443/10000000000 : ℝ)^4651 ≤ (50160431544191/100000000000000 : ℝ)^3627 := by
    have hnat : (5838913443 : ℕ)^4651*100000000000000^3627 ≤ 50160431544191^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5838913443 10000000000 50160431544191 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5195427143/10000000000 : ℝ), (-604224259/5000000000 : ℝ), (5838913443/10000000000 : ℝ)] ![(1349532929497/3125000000000 : ℝ), (665451469829/10000000000000 : ℝ), (50160431544191/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5195427143/10000000000 : ℝ)|^4651 ≤ (1349532929497/3125000000000 : ℝ)^3627
        have hw : |(5195427143/10000000000 : ℝ)|=(5195427143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-604224259/5000000000 : ℝ)|^4651 ≤ (665451469829/10000000000000 : ℝ)^3627
        have hw : |(-604224259/5000000000 : ℝ)|=(604224259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5838913443/10000000000 : ℝ)|^4651 ≤ (50160431544191/100000000000000 : ℝ)^3627
        have hw : |(5838913443/10000000000 : ℝ)|=(5838913443/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s0_6 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (162357071/312500000 : ℝ)*x 0 + (2919457259/5000000000 : ℝ)*x 1 + (-302112039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (162357071/312500000 : ℝ)^4651 ≤ (84345789961/195312500000 : ℝ)^3627 := by
    have hnat : (162357071 : ℕ)^4651*195312500000^3627 ≤ 84345789961^3627*312500000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      162357071 312500000 84345789961 195312500000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2919457259/5000000000 : ℝ)^4651 ≤ (25080221693251/50000000000000 : ℝ)^3627 := by
    have hnat : (2919457259 : ℕ)^4651*50000000000000^3627 ≤ 25080221693251^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2919457259 5000000000 25080221693251 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (302112039/2500000000 : ℝ)^4651 ≤ (1330902428417/20000000000000 : ℝ)^3627 := by
    have hnat : (302112039 : ℕ)^4651*20000000000000^3627 ≤ 1330902428417^3627*2500000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      302112039 2500000000 1330902428417 20000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(162357071/312500000 : ℝ), (2919457259/5000000000 : ℝ), (-302112039/2500000000 : ℝ)] ![(84345789961/195312500000 : ℝ), (25080221693251/50000000000000 : ℝ), (1330902428417/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(162357071/312500000 : ℝ)|^4651 ≤ (84345789961/195312500000 : ℝ)^3627
        have hw : |(162357071/312500000 : ℝ)|=(162357071/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2919457259/5000000000 : ℝ)|^4651 ≤ (25080221693251/50000000000000 : ℝ)^3627
        have hw : |(2919457259/5000000000 : ℝ)|=(2919457259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-302112039/2500000000 : ℝ)|^4651 ≤ (1330902428417/20000000000000 : ℝ)^3627
        have hw : |(-302112039/2500000000 : ℝ)|=(302112039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s0_7 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2067584767/5000000000 : ℝ)*x 0 + (42919333/80000000 : ℝ)*x 1 + (1577133137/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2067584767/5000000000 : ℝ)^4651 ≤ (1007091785637/3125000000000 : ℝ)^3627 := by
    have hnat : (2067584767 : ℕ)^4651*3125000000000^3627 ≤ 1007091785637^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2067584767 5000000000 1007091785637 3125000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42919333/80000000 : ℝ)^4651 ≤ (22499937420753/50000000000000 : ℝ)^3627 := by
    have hnat : (42919333 : ℕ)^4651*50000000000000^3627 ≤ 22499937420753^3627*80000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42919333 80000000 22499937420753 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1577133137/5000000000 : ℝ)^4651 ≤ (11386594004423/50000000000000 : ℝ)^3627 := by
    have hnat : (1577133137 : ℕ)^4651*50000000000000^3627 ≤ 11386594004423^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1577133137 5000000000 11386594004423 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2067584767/5000000000 : ℝ), (42919333/80000000 : ℝ), (1577133137/5000000000 : ℝ)] ![(1007091785637/3125000000000 : ℝ), (22499937420753/50000000000000 : ℝ), (11386594004423/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2067584767/5000000000 : ℝ)|^4651 ≤ (1007091785637/3125000000000 : ℝ)^3627
        have hw : |(2067584767/5000000000 : ℝ)|=(2067584767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42919333/80000000 : ℝ)|^4651 ≤ (22499937420753/50000000000000 : ℝ)^3627
        have hw : |(42919333/80000000 : ℝ)|=(42919333/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1577133137/5000000000 : ℝ)|^4651 ≤ (11386594004423/50000000000000 : ℝ)^3627
        have hw : |(1577133137/5000000000 : ℝ)|=(1577133137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1577_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168591139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (3627/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (24669/100000 : ℝ)*pair X 0 0 := by
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
  have hpowlo : (0 : ℝ) ^ (4649/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4649 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4649*1^1024 ≤ 0^1024*1^4649 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4649 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4649/1024 : ℝ) ≤ (97547654959934427/6250000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4649 ≤ (97547654959934427/6250000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4649*6250000000000000000^1024 ≤ 97547654959934427^1024*5^4649 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 97547654959934427 6250000000000000000 4649 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (97547654959934427/6250000000000000000 : ℝ)) (by norm_num) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4649/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4649 := by
      have hnat : (1 : ℕ)^1024*1^4649 ≤ 1^4649*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4649 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6347547654959934427/6250000000000000000 : ℝ) ≤ (10034170462563889/10000000000000000 : ℝ) ^ (4649/1024 : ℝ) := by
    have hpowers : (6347547654959934427/6250000000000000000 : ℝ)^1024 ≤ (10034170462563889/10000000000000000 : ℝ)^4649 := by
      have hnat : (6347547654959934427 : ℕ)^1024*10000000000000000^4649 ≤ 10034170462563889^4649*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6347547654959934427 6250000000000000000 10034170462563889 10000000000000000 1024 4649 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10034170462563889/10000000000000000 : ℝ)) (X := (6347547654959934427/6250000000000000000 : ℝ)) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (3222547654959934427/3125000000000000000 : ℝ) ≤ (5034170462563889/5000000000000000 : ℝ) ^ (4649/1024 : ℝ) := by
    have hpowers : (3222547654959934427/3125000000000000000 : ℝ)^1024 ≤ (5034170462563889/5000000000000000 : ℝ)^4649 := by
      have hnat : (3222547654959934427 : ℕ)^1024*5000000000000000^4649 ≤ 5034170462563889^4649*3125000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3222547654959934427 3125000000000000000 5034170462563889 5000000000000000 1024 4649 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5034170462563889/5000000000000000 : ℝ)) (X := (3222547654959934427/3125000000000000000 : ℝ)) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(34170462563889/4000000000000000 : ℝ)*(0 : ℝ))^(4649/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(34170462563889/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(97547654959934427/6250000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(34170462563889/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4649/1024 : ℝ) := by
    rw [show (1 : ℝ)+(34170462563889/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10034170462563889/10000000000000000 : ℝ) by norm_num, show 1+(97547654959934427/6250000000000000000 : ℝ)+(0 : ℝ)=(6347547654959934427/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(97547654959934427/6250000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(34170462563889/4000000000000000 : ℝ)*(2/5 : ℝ))^(4649/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(34170462563889/4000000000000000 : ℝ)*(2/5 : ℝ)=(5034170462563889/5000000000000000 : ℝ) by norm_num, show 1+2*(97547654959934427/6250000000000000000 : ℝ)=(3222547654959934427/3125000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(34170462563889/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4649/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34170462563889/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(34170462563889/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4649/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34170462563889/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(34170462563889/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4649/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (34170462563889/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1619010983/10000000000 : ℝ)*X 0 0+(733063129/1250000000 : ℝ)*X 0 1+(2441074271/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2731993599/5000000000 : ℝ)*X 1 0+(-541303299/2500000000 : ℝ)*X 1 1+(305134283/625000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5463987261/10000000000 : ℝ)*X 2 0+(2441074223/5000000000 : ℝ)*X 2 1+(-2165213217/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4128048979/10000000000 : ℝ)*X 0 0+(96674011/312500000 : ℝ)*X 0 1+(1355885979/2500000000 : ℝ)*X 0 2+(4128048979/10000000000 : ℝ)*X 1 0+(96674011/312500000 : ℝ)*X 1 1+(1355885979/2500000000 : ℝ)*X 1 2+(4128048979/10000000000 : ℝ)*X 2 0+(96674011/312500000 : ℝ)*X 2 1+(1355885979/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-811006973/5000000000 : ℝ)*X 0 0+(4906865543/10000000000 : ℝ)*X 0 1+(1459728433/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5195427143/10000000000 : ℝ)*X 1 0+(-604224259/5000000000 : ℝ)*X 1 1+(5838913443/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((162357071/312500000 : ℝ)*X 2 0+(2919457259/5000000000 : ℝ)*X 2 1+(-302112039/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2067584767/5000000000 : ℝ)*X 0 0+(42919333/80000000 : ℝ)*X 0 1+(1577133137/5000000000 : ℝ)*X 0 2+(2067584767/5000000000 : ℝ)*X 1 0+(42919333/80000000 : ℝ)*X 1 1+(1577133137/5000000000 : ℝ)*X 1 2+(2067584767/5000000000 : ℝ)*X 2 0+(42919333/80000000 : ℝ)*X 2 1+(1577133137/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1305011312859176739/250000000000000000000000 : ℝ) := by norm_num
    linear_combination (24081851/50000000000000 : ℝ)*(base1) + (259835293/25000000000000 : ℝ)*(base19) + (262769593/25000000000000 : ℝ)*(base23) + (33873351/25000000000000 : ℝ)*(upper3) + (132265437/100000000000000 : ℝ)*(upper5) + (180895050634121/25000000000000 : ℝ)*(major0) + (180895050634121/25000000000000 : ℝ)*(major1) + (180895050634121/25000000000000 : ℝ)*(major2) + (814371269861/80000000000 : ℝ)*(sp0) + (2035933765113/200000000000 : ℝ)*(sp1) + (10179668708193/1000000000000 : ℝ)*(sp2) + (214595302785753/50000000000000 : ℝ)*(sp3) + (970683781/25000000000000 : ℝ)*(sp4) + (103464911/6250000000000 : ℝ)*(sp7) + (53649038646723/12500000000000 : ℝ)*(f.failure) + (127245990237209/12500000000000 : ℝ)*(f.sum) + (79863719343431/50000000000000000000000000000 : ℝ)*base66 + (938198281456569/100000000000000000000000000000 : ℝ)*base67 + (301538432943431/100000000000000000000000000000 : ℝ)*base70 + (291738630056569/100000000000000000000000000000 : ℝ)*base71 + (143354420256569/50000000000000000000000000000 : ℝ)*base73 + (300906606143431/100000000000000000000000000000 : ℝ)*base76 + (59613600056569/100000000000000000000000000000 : ℝ)*base77 + (424229734656569/100000000000000000000000000000 : ℝ)*base79 + (265556835143431/50000000000000000000000000000 : ℝ)*base82 + (812503/1250000000000000000000 : ℝ)*base90 + (812503/1250000000000000000000 : ℝ)*base92 + (812503/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (42851565920046822941181/12500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (828199421/100000000000000 : ℝ)*(base19) + (250269587/25000000000000 : ℝ)*(base23) + (408801827/100000000000000 : ℝ)*(base39) + (10792391/20000000000000 : ℝ)*(upper3) + (79666389/20000000000000 : ℝ)*(upper5) + (190657382579017/25000000000000 : ℝ)*(major0) + (190657382579017/25000000000000 : ℝ)*(major1) + (381314560757121/50000000000000 : ℝ)*(major2) + (2713854377/100000000000000 : ℝ)*(sp1) + (43987583/2500000000000 : ℝ)*(sp2) + (214580816237343/20000000000000 : ℝ)*(sp4) + (1072900539132917/100000000000000 : ℝ)*(sp5) + (536450864703437/50000000000000 : ℝ)*(sp6) + (90470891274549/20000000000000 : ℝ)*(sp7) + (90470891274549/20000000000000 : ℝ)*(f.failure) + (1072904489988541/100000000000000 : ℝ)*(f.sum) + (31058421432441/40000000000000000000000000000 : ℝ)*base66 + (1665338699796431/200000000000000000000000000000 : ℝ)*base68 + (336376297682887/100000000000000000000000000000 : ℝ)*base70 + (1239845847196431/200000000000000000000000000000 : ℝ)*base72 + (186215872912441/40000000000000000000000000000 : ℝ)*base74 + (119369711617113/100000000000000000000000000000 : ℝ)*base75 + (796414154482887/100000000000000000000000000000 : ℝ)*base78 + (681281354382887/100000000000000000000000000000 : ℝ)*base80 + (249193913982887/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (17621311/2000000000000000000000 : ℝ)*base89 + (17621311/2000000000000000000000 : ℝ)*base91 + (2378689/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1577_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168591139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3627/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (24669/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1577_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1577_s1_0 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1755856699/10000000000 : ℝ)*x 0 + (1106178943/2000000000 : ℝ)*x 1 + (5127521611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1755856699/10000000000 : ℝ)^4651 ≤ (2686135700431/25000000000000 : ℝ)^3627 := by
    have hnat : (1755856699 : ℕ)^4651*25000000000000^3627 ≤ 2686135700431^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1755856699 10000000000 2686135700431 25000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1106178943/2000000000 : ℝ)^4651 ≤ (11698214936963/25000000000000 : ℝ)^3627 := by
    have hnat : (1106178943 : ℕ)^4651*25000000000000^3627 ≤ 11698214936963^3627*2000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1106178943 2000000000 11698214936963 25000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5127521611/10000000000 : ℝ)^4651 ≤ (8492519486517/20000000000000 : ℝ)^3627 := by
    have hnat : (5127521611 : ℕ)^4651*20000000000000^3627 ≤ 8492519486517^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5127521611 10000000000 8492519486517 20000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1755856699/10000000000 : ℝ), (1106178943/2000000000 : ℝ), (5127521611/10000000000 : ℝ)] ![(2686135700431/25000000000000 : ℝ), (11698214936963/25000000000000 : ℝ), (8492519486517/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1755856699/10000000000 : ℝ)|^4651 ≤ (2686135700431/25000000000000 : ℝ)^3627
        have hw : |(-1755856699/10000000000 : ℝ)|=(1755856699/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1106178943/2000000000 : ℝ)|^4651 ≤ (11698214936963/25000000000000 : ℝ)^3627
        have hw : |(1106178943/2000000000 : ℝ)|=(1106178943/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5127521611/10000000000 : ℝ)|^4651 ≤ (8492519486517/20000000000000 : ℝ)^3627
        have hw : |(5127521611/10000000000 : ℝ)|=(5127521611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s1_1 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335953783/625000000 : ℝ)*x 0 + (-491673689/2500000000 : ℝ)*x 1 + (2563760637/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335953783/625000000 : ℝ)^4651 ≤ (45111163186619/100000000000000 : ℝ)^3627 := by
    have hnat : (335953783 : ℕ)^4651*100000000000000^3627 ≤ 45111163186619^3627*625000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335953783 625000000 45111163186619 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (491673689/2500000000 : ℝ)^4651 ≤ (12426242940347/100000000000000 : ℝ)^3627 := by
    have hnat : (491673689 : ℕ)^4651*100000000000000^3627 ≤ 12426242940347^3627*2500000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      491673689 2500000000 12426242940347 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2563760637/5000000000 : ℝ)^4651 ≤ (8492518770773/20000000000000 : ℝ)^3627 := by
    have hnat : (2563760637 : ℕ)^4651*20000000000000^3627 ≤ 8492518770773^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563760637 5000000000 8492518770773 20000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335953783/625000000 : ℝ), (-491673689/2500000000 : ℝ), (2563760637/5000000000 : ℝ)] ![(45111163186619/100000000000000 : ℝ), (12426242940347/100000000000000 : ℝ), (8492518770773/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335953783/625000000 : ℝ)|^4651 ≤ (45111163186619/100000000000000 : ℝ)^3627
        have hw : |(335953783/625000000 : ℝ)|=(335953783/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-491673689/2500000000 : ℝ)|^4651 ≤ (12426242940347/100000000000000 : ℝ)^3627
        have hw : |(-491673689/2500000000 : ℝ)|=(491673689/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2563760637/5000000000 : ℝ)|^4651 ≤ (8492518770773/20000000000000 : ℝ)^3627
        have hw : |(2563760637/5000000000 : ℝ)|=(2563760637/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s1_2 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (268763017/500000000 : ℝ)*x 0 + (2563760743/5000000000 : ℝ)*x 1 + (-1966694729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (268763017/500000000 : ℝ)^4651 ≤ (2819447572713/6250000000000 : ℝ)^3627 := by
    have hnat : (268763017 : ℕ)^4651*6250000000000^3627 ≤ 2819447572713^3627*500000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      268763017 500000000 2819447572713 6250000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2563760743/5000000000 : ℝ)^4651 ≤ (42462596105167/100000000000000 : ℝ)^3627 := by
    have hnat : (2563760743 : ℕ)^4651*100000000000000^3627 ≤ 42462596105167^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2563760743 5000000000 42462596105167 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1966694729/10000000000 : ℝ)^4651 ≤ (3106560680397/25000000000000 : ℝ)^3627 := by
    have hnat : (1966694729 : ℕ)^4651*25000000000000^3627 ≤ 3106560680397^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1966694729 10000000000 3106560680397 25000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(268763017/500000000 : ℝ), (2563760743/5000000000 : ℝ), (-1966694729/10000000000 : ℝ)] ![(2819447572713/6250000000000 : ℝ), (42462596105167/100000000000000 : ℝ), (3106560680397/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(268763017/500000000 : ℝ)|^4651 ≤ (2819447572713/6250000000000 : ℝ)^3627
        have hw : |(268763017/500000000 : ℝ)|=(268763017/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2563760743/5000000000 : ℝ)|^4651 ≤ (42462596105167/100000000000000 : ℝ)^3627
        have hw : |(2563760743/5000000000 : ℝ)|=(2563760743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1966694729/10000000000 : ℝ)|^4651 ≤ (3106560680397/25000000000000 : ℝ)^3627
        have hw : |(-1966694729/10000000000 : ℝ)|=(1966694729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s1_3 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4225913633/10000000000 : ℝ)*x 0 + (1884627699/5000000000 : ℝ)*x 1 + (4725986019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4225913633/10000000000 : ℝ)^4651 ≤ (4142074662349/12500000000000 : ℝ)^3627 := by
    have hnat : (4225913633 : ℕ)^4651*12500000000000^3627 ≤ 4142074662349^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4225913633 10000000000 4142074662349 12500000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1884627699/5000000000 : ℝ)^4651 ≤ (28616800369387/100000000000000 : ℝ)^3627 := by
    have hnat : (1884627699 : ℕ)^4651*100000000000000^3627 ≤ 28616800369387^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1884627699 5000000000 28616800369387 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4725986019/10000000000 : ℝ)^4651 ≤ (9561650578847/25000000000000 : ℝ)^3627 := by
    have hnat : (4725986019 : ℕ)^4651*25000000000000^3627 ≤ 9561650578847^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4725986019 10000000000 9561650578847 25000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4225913633/10000000000 : ℝ), (1884627699/5000000000 : ℝ), (4725986019/10000000000 : ℝ)] ![(4142074662349/12500000000000 : ℝ), (28616800369387/100000000000000 : ℝ), (9561650578847/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4225913633/10000000000 : ℝ)|^4651 ≤ (4142074662349/12500000000000 : ℝ)^3627
        have hw : |(4225913633/10000000000 : ℝ)|=(4225913633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1884627699/5000000000 : ℝ)|^4651 ≤ (28616800369387/100000000000000 : ℝ)^3627
        have hw : |(1884627699/5000000000 : ℝ)|=(1884627699/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4725986019/10000000000 : ℝ)|^4651 ≤ (9561650578847/25000000000000 : ℝ)^3627
        have hw : |(4725986019/10000000000 : ℝ)|=(4725986019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s1_4 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-219507401/1250000000 : ℝ)*x 0 + (641455439/1250000000 : ℝ)*x 1 + (345419539/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (219507401/1250000000 : ℝ)^4651 ≤ (5373065946887/50000000000000 : ℝ)^3627 := by
    have hnat : (219507401 : ℕ)^4651*50000000000000^3627 ≤ 5373065946887^3627*1250000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      219507401 1250000000 5373065946887 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (641455439/1250000000 : ℝ)^4651 ≤ (425063742987/1000000000000 : ℝ)^3627 := by
    have hnat : (641455439 : ℕ)^4651*1000000000000^3627 ≤ 425063742987^3627*1250000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      641455439 1250000000 425063742987 1000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (345419539/625000000 : ℝ)^4651 ≤ (2921718361827/6250000000000 : ℝ)^3627 := by
    have hnat : (345419539 : ℕ)^4651*6250000000000^3627 ≤ 2921718361827^3627*625000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      345419539 625000000 2921718361827 6250000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-219507401/1250000000 : ℝ), (641455439/1250000000 : ℝ), (345419539/625000000 : ℝ)] ![(5373065946887/50000000000000 : ℝ), (425063742987/1000000000000 : ℝ), (2921718361827/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-219507401/1250000000 : ℝ)|^4651 ≤ (5373065946887/50000000000000 : ℝ)^3627
        have hw : |(-219507401/1250000000 : ℝ)|=(219507401/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(641455439/1250000000 : ℝ)|^4651 ≤ (425063742987/1000000000000 : ℝ)^3627
        have hw : |(641455439/1250000000 : ℝ)|=(641455439/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(345419539/625000000 : ℝ)|^4651 ≤ (2921718361827/6250000000000 : ℝ)^3627
        have hw : |(345419539/625000000 : ℝ)|=(345419539/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s1_5 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (526826569/1000000000 : ℝ)*x 0 + (-1567503429/10000000000 : ℝ)*x 1 + (5526713209/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (526826569/1000000000 : ℝ)^4651 ≤ (21981480708873/50000000000000 : ℝ)^3627 := by
    have hnat : (526826569 : ℕ)^4651*50000000000000^3627 ≤ 21981480708873^3627*1000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526826569 1000000000 21981480708873 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1567503429/10000000000 : ℝ)^4651 ≤ (9289538436981/100000000000000 : ℝ)^3627 := by
    have hnat : (1567503429 : ℕ)^4651*100000000000000^3627 ≤ 9289538436981^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1567503429 10000000000 9289538436981 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5526713209/10000000000 : ℝ)^4651 ≤ (46747500134443/100000000000000 : ℝ)^3627 := by
    have hnat : (5526713209 : ℕ)^4651*100000000000000^3627 ≤ 46747500134443^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5526713209 10000000000 46747500134443 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(526826569/1000000000 : ℝ), (-1567503429/10000000000 : ℝ), (5526713209/10000000000 : ℝ)] ![(21981480708873/50000000000000 : ℝ), (9289538436981/100000000000000 : ℝ), (46747500134443/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(526826569/1000000000 : ℝ)|^4651 ≤ (21981480708873/50000000000000 : ℝ)^3627
        have hw : |(526826569/1000000000 : ℝ)|=(526826569/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1567503429/10000000000 : ℝ)|^4651 ≤ (9289538436981/100000000000000 : ℝ)^3627
        have hw : |(-1567503429/10000000000 : ℝ)|=(1567503429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5526713209/10000000000 : ℝ)|^4651 ≤ (46747500134443/100000000000000 : ℝ)^3627
        have hw : |(5526713209/10000000000 : ℝ)|=(5526713209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s1_6 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1053652999/2000000000 : ℝ)*x 0 + (221068539/400000000 : ℝ)*x 1 + (-1567504027/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1053652999/2000000000 : ℝ)^4651 ≤ (43962953980659/100000000000000 : ℝ)^3627 := by
    have hnat : (1053652999 : ℕ)^4651*100000000000000^3627 ≤ 43962953980659^3627*2000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053652999 2000000000 43962953980659 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (221068539/400000000 : ℝ)^4651 ≤ (1460859469363/3125000000000 : ℝ)^3627 := by
    have hnat : (221068539 : ℕ)^4651*3125000000000^3627 ≤ 1460859469363^3627*400000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      221068539 400000000 1460859469363 3125000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1567504027/10000000000 : ℝ)^4651 ≤ (2322385745369/25000000000000 : ℝ)^3627 := by
    have hnat : (1567504027 : ℕ)^4651*25000000000000^3627 ≤ 2322385745369^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1567504027 10000000000 2322385745369 25000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1053652999/2000000000 : ℝ), (221068539/400000000 : ℝ), (-1567504027/10000000000 : ℝ)] ![(43962953980659/100000000000000 : ℝ), (1460859469363/3125000000000 : ℝ), (2322385745369/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1053652999/2000000000 : ℝ)|^4651 ≤ (43962953980659/100000000000000 : ℝ)^3627
        have hw : |(1053652999/2000000000 : ℝ)|=(1053652999/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(221068539/400000000 : ℝ)|^4651 ≤ (1460859469363/3125000000000 : ℝ)^3627
        have hw : |(221068539/400000000 : ℝ)|=(221068539/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1567504027/10000000000 : ℝ)|^4651 ≤ (2322385745369/25000000000000 : ℝ)^3627
        have hw : |(-1567504027/10000000000 : ℝ)|=(1567504027/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s1_7 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (845278611/2000000000 : ℝ)*x 0 + (4716210147/10000000000 : ℝ)*x 1 + (472396757/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (845278611/2000000000 : ℝ)^4651 ≤ (33141418008623/100000000000000 : ℝ)^3627 := by
    have hnat : (845278611 : ℕ)^4651*100000000000000^3627 ≤ 33141418008623^3627*2000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      845278611 2000000000 33141418008623 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4716210147/10000000000 : ℝ)^4651 ≤ (38145181330891/100000000000000 : ℝ)^3627 := by
    have hnat : (4716210147 : ℕ)^4651*100000000000000^3627 ≤ 38145181330891^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4716210147 10000000000 38145181330891 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (472396757/1250000000 : ℝ)^4651 ≤ (1148536026131/4000000000000 : ℝ)^3627 := by
    have hnat : (472396757 : ℕ)^4651*4000000000000^3627 ≤ 1148536026131^3627*1250000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472396757 1250000000 1148536026131 4000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(845278611/2000000000 : ℝ), (4716210147/10000000000 : ℝ), (472396757/1250000000 : ℝ)] ![(33141418008623/100000000000000 : ℝ), (38145181330891/100000000000000 : ℝ), (1148536026131/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(845278611/2000000000 : ℝ)|^4651 ≤ (33141418008623/100000000000000 : ℝ)^3627
        have hw : |(845278611/2000000000 : ℝ)|=(845278611/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4716210147/10000000000 : ℝ)|^4651 ≤ (38145181330891/100000000000000 : ℝ)^3627
        have hw : |(4716210147/10000000000 : ℝ)|=(4716210147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(472396757/1250000000 : ℝ)|^4651 ≤ (1148536026131/4000000000000 : ℝ)^3627
        have hw : |(472396757/1250000000 : ℝ)|=(472396757/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1577_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168591139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24669/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9147/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4423/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (24669/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3627/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (24669/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3627/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (24669/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3627/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (24669/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3627/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (24669/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3627/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (24669/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3627/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3627/100000 : ℝ) ^ (4649/1024 : ℝ) ≤ (5771911059243/20000000000000000000 : ℝ) := by
    have hpowers : (3627/100000 : ℝ)^4649 ≤ (5771911059243/20000000000000000000 : ℝ)^1024 := by
      have hnat : (3627 : ℕ)^4649*20000000000000000000^1024 ≤ 5771911059243^1024*100000^4649 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3627 100000 5771911059243 20000000000000000000 4649 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3627/100000 : ℝ)) (X := (5771911059243/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (24669/100000 : ℝ) ^ (4649/1024 : ℝ) ≤ (86958947458903521/50000000000000000000 : ℝ) := by
    have hpowers : (24669/100000 : ℝ)^4649 ≤ (86958947458903521/50000000000000000000 : ℝ)^1024 := by
      have hnat : (24669 : ℕ)^4649*50000000000000000000^1024 ≤ 86958947458903521^1024*100000^4649 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        24669 100000 86958947458903521 50000000000000000000 4649 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (24669/100000 : ℝ)) (X := (86958947458903521/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000005771911059243/10000000000000000000 : ℝ) ≤ (1250000158916853/1250000000000000 : ℝ) ^ (4649/1024 : ℝ) := by
    have hpowers : (10000005771911059243/10000000000000000000 : ℝ)^1024 ≤ (1250000158916853/1250000000000000 : ℝ)^4649 := by
      have hnat : (10000005771911059243 : ℕ)^1024*1250000000000000^4649 ≤ 1250000158916853^4649*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000005771911059243 10000000000000000000 1250000158916853 1250000000000000 1024 4649 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000158916853/1250000000000000 : ℝ)) (X := (10000005771911059243/10000000000000000000 : ℝ)) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100173946754473103257/100000000000000000000 : ℝ) ≤ (156309824964203/156250000000000 : ℝ) ^ (4649/1024 : ℝ) := by
    have hpowers : (100173946754473103257/100000000000000000000 : ℝ)^1024 ≤ (156309824964203/156250000000000 : ℝ)^4649 := by
      have hnat : (100173946754473103257 : ℕ)^1024*156250000000000^4649 ≤ 156309824964203^4649*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100173946754473103257 100000000000000000000 156309824964203 156250000000000 1024 4649 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156309824964203/156250000000000 : ℝ)) (X := (100173946754473103257/100000000000000000000 : ℝ)) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25086958947458903521/25000000000000000000 : ℝ) ≤ (250191408102079/250000000000000 : ℝ) ^ (4649/1024 : ℝ) := by
    have hpowers : (25086958947458903521/25000000000000000000 : ℝ)^1024 ≤ (250191408102079/250000000000000 : ℝ)^4649 := by
      have hnat : (25086958947458903521 : ℕ)^1024*250000000000000^4649 ≤ 250191408102079^4649*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25086958947458903521 25000000000000000000 250191408102079 250000000000000 1024 4649 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250191408102079/250000000000000 : ℝ)) (X := (25086958947458903521/25000000000000000000 : ℝ)) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5771911059243/20000000000000000000 : ℝ) ≤ ((52180620504739373/52187500000000000 : ℝ)+2*(68348685253/37575000000000 : ℝ)*(3627/100000 : ℝ))^(4649/1024 : ℝ) := by
    rw [show (52180620504739373/52187500000000000 : ℝ)+2*(68348685253/37575000000000 : ℝ)*(3627/100000 : ℝ)=(1250000158916853/1250000000000000 : ℝ) by norm_num, show 1+2*(5771911059243/20000000000000000000 : ℝ)=(10000005771911059243/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(86958947458903521/50000000000000000000 : ℝ)+(5771911059243/20000000000000000000 : ℝ) ≤ ((52180620504739373/52187500000000000 : ℝ)+(68348685253/37575000000000 : ℝ)*((24669/100000 : ℝ)+(3627/100000 : ℝ)))^(4649/1024 : ℝ) := by
    rw [show (52180620504739373/52187500000000000 : ℝ)+(68348685253/37575000000000 : ℝ)*((24669/100000 : ℝ)+(3627/100000 : ℝ))=(156309824964203/156250000000000 : ℝ) by norm_num, show 1+(86958947458903521/50000000000000000000 : ℝ)+(5771911059243/20000000000000000000 : ℝ)=(100173946754473103257/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(86958947458903521/50000000000000000000 : ℝ) ≤ ((52180620504739373/52187500000000000 : ℝ)+2*(68348685253/37575000000000 : ℝ)*(24669/100000 : ℝ))^(4649/1024 : ℝ) := by
    rw [show (52180620504739373/52187500000000000 : ℝ)+2*(68348685253/37575000000000 : ℝ)*(24669/100000 : ℝ)=(250191408102079/250000000000000 : ℝ) by norm_num, show 1+2*(86958947458903521/50000000000000000000 : ℝ)=(25086958947458903521/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (52180620504739373/52187500000000000 : ℝ)*(X 1 0+X 2 0)+(68348685253/37575000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4649/1024 : ℝ)) (lo := (3627/100000 : ℝ)) (hi := (24669/100000 : ℝ)) (c := (52180620504739373/52187500000000000 : ℝ)) (alpha := (68348685253/37575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (52180620504739373/52187500000000000 : ℝ)*(X 0 1+X 2 1)+(68348685253/37575000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4649/1024 : ℝ)) (lo := (3627/100000 : ℝ)) (hi := (24669/100000 : ℝ)) (c := (52180620504739373/52187500000000000 : ℝ)) (alpha := (68348685253/37575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (52180620504739373/52187500000000000 : ℝ)*(X 0 2+X 1 2)+(68348685253/37575000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4649/1024 : ℝ)) (lo := (3627/100000 : ℝ)) (hi := (24669/100000 : ℝ)) (c := (52180620504739373/52187500000000000 : ℝ)) (alpha := (68348685253/37575000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1755856699/10000000000 : ℝ)*X 0 0+(1106178943/2000000000 : ℝ)*X 0 1+(5127521611/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((335953783/625000000 : ℝ)*X 1 0+(-491673689/2500000000 : ℝ)*X 1 1+(2563760637/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((268763017/500000000 : ℝ)*X 2 0+(2563760743/5000000000 : ℝ)*X 2 1+(-1966694729/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4225913633/10000000000 : ℝ)*X 0 0+(1884627699/5000000000 : ℝ)*X 0 1+(4725986019/10000000000 : ℝ)*X 0 2+(4225913633/10000000000 : ℝ)*X 1 0+(1884627699/5000000000 : ℝ)*X 1 1+(4725986019/10000000000 : ℝ)*X 1 2+(4225913633/10000000000 : ℝ)*X 2 0+(1884627699/5000000000 : ℝ)*X 2 1+(4725986019/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-219507401/1250000000 : ℝ)*X 0 0+(641455439/1250000000 : ℝ)*X 0 1+(345419539/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((526826569/1000000000 : ℝ)*X 1 0+(-1567503429/10000000000 : ℝ)*X 1 1+(5526713209/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1053652999/2000000000 : ℝ)*X 2 0+(221068539/400000000 : ℝ)*X 2 1+(-1567504027/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((845278611/2000000000 : ℝ)*X 0 0+(4716210147/10000000000 : ℝ)*X 0 1+(472396757/1250000000 : ℝ)*X 0 2+(845278611/2000000000 : ℝ)*X 1 0+(4716210147/10000000000 : ℝ)*X 1 1+(472396757/1250000000 : ℝ)*X 1 2+(845278611/2000000000 : ℝ)*X 2 0+(4716210147/10000000000 : ℝ)*X 2 1+(472396757/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7931082405650905133236363/1304687500000000000000000000000 : ℝ) := by norm_num
    linear_combination (110299337/6250000000000 : ℝ)*(base19) + (3284379/200000000000 : ℝ)*(base23) + (85275991/50000000000000 : ℝ)*(upper3) + (9646559/50000000000000 : ℝ)*(upper4) + (144217901/100000000000000 : ℝ)*(upper5) + (440545694654083/25000000000000 : ℝ)*(major0) + (440545694654083/25000000000000 : ℝ)*(major1) + (440545694654083/25000000000000 : ℝ)*(major2) + (38736089529891/1562500000000 : ℝ)*(sp0) + (15494519628751/625000000000 : ℝ)*(sp1) + (619780815800013/25000000000000 : ℝ)*(sp2) + (130654156276347/12500000000000 : ℝ)*(sp3) + (948467283/6250000000000 : ℝ)*(sp4) + (7199001879/100000000000000 : ℝ)*(sp7) + (209048089842531/20000000000000 : ℝ)*(f.failure) + (154945306586847/6250000000000 : ℝ)*(f.sum) + (10081547131189/7515000000000000000000000000 : ℝ)*base65 + (326137722817882387/23484375000000000000000000000000 : ℝ)*base67 + (117495628743777131/11742187500000000000000000000000 : ℝ)*base69 + (300883695045569887/23484375000000000000000000000000 : ℝ)*base71 + (5396454538969/7515000000000000000000000000 : ℝ)*base73 + (31728898164777131/11742187500000000000000000000000 : ℝ)*base75 + (142996992551819887/23484375000000000000000000000000 : ℝ)*base77 + (291485053250257387/23484375000000000000000000000000 : ℝ)*base79 + (5618775991771/1878750000000000000000000000 : ℝ)*base81 + (8067191/2000000000000000000000 : ℝ)*base90 + (8067191/2000000000000000000000 : ℝ)*base92 + (8067191/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13929332097360558517496231/1565625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (313848543/20000000000000 : ℝ)*(base19) + (175577917/12500000000000 : ℝ)*(base23) + (12416763/12500000000000 : ℝ)*(upper2) + (16157583/5000000000000 : ℝ)*(upper3) + (29505097/20000000000000 : ℝ)*(upper5) + (44979911076749/2500000000000 : ℝ)*(major0) + (44979911076749/2500000000000 : ℝ)*(major1) + (44979911076749/2500000000000 : ℝ)*(major2) + (6599465267/50000000000000 : ℝ)*(sp1) + (12250991071/100000000000000 : ℝ)*(sp2) + (632799362216833/25000000000000 : ℝ)*(sp4) + (1265591340347041/50000000000000 : ℝ)*(sp5) + (632795948313231/25000000000000 : ℝ)*(sp6) + (106719514070663/10000000000000 : ℝ)*(sp7) + (106719514070663/10000000000000 : ℝ)*(f.failure) + (632799362216833/25000000000000 : ℝ)*(f.sum) + (808100332061/751500000000000000000000000 : ℝ)*base65 + (9959840711193911/2348437500000000000000000000000 : ℝ)*base67 + (5554190799529607/1174218750000000000000000000000 : ℝ)*base70 + (6004746495937661/2348437500000000000000000000000 : ℝ)*base71 + (54027032309/18787500000000000000000000 : ℝ)*base73 + (9686773463662661/2348437500000000000000000000000 : ℝ)*base75 + (11828376003806411/2348437500000000000000000000000 : ℝ)*base77 + (297080261798357/1174218750000000000000000000000 : ℝ)*base80 + (1524379724863/300600000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (1655157/1000000000000000000000 : ℝ)*base89 + (1655157/1000000000000000000000 : ℝ)*base91 + (1655157/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1577_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168591139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (24669/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3627/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9147/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4423/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1577_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1577_s2_0 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1773832463/10000000000 : ℝ)*x 0 + (135992789/250000000 : ℝ)*x 1 + (130174563/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1773832463/10000000000 : ℝ)^4651 ≤ (10885800024559/100000000000000 : ℝ)^3627 := by
    have hnat : (1773832463 : ℕ)^4651*100000000000000^3627 ≤ 10885800024559^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773832463 10000000000 10885800024559 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (135992789/250000000 : ℝ)^4651 ≤ (715717817971/1562500000000 : ℝ)^3627 := by
    have hnat : (135992789 : ℕ)^4651*1562500000000^3627 ≤ 715717817971^3627*250000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135992789 250000000 715717817971 1562500000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (130174563/250000000 : ℝ)^4651 ≤ (5413532450653/12500000000000 : ℝ)^3627 := by
    have hnat : (130174563 : ℕ)^4651*12500000000000^3627 ≤ 5413532450653^3627*250000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      130174563 250000000 5413532450653 12500000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1773832463/10000000000 : ℝ), (135992789/250000000 : ℝ), (130174563/250000000 : ℝ)] ![(10885800024559/100000000000000 : ℝ), (715717817971/1562500000000 : ℝ), (5413532450653/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1773832463/10000000000 : ℝ)|^4651 ≤ (10885800024559/100000000000000 : ℝ)^3627
        have hw : |(-1773832463/10000000000 : ℝ)|=(1773832463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(135992789/250000000 : ℝ)|^4651 ≤ (715717817971/1562500000000 : ℝ)^3627
        have hw : |(135992789/250000000 : ℝ)|=(135992789/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(130174563/250000000 : ℝ)|^4651 ≤ (5413532450653/12500000000000 : ℝ)^3627
        have hw : |(130174563/250000000 : ℝ)|=(130174563/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s2_1 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351668317/10000000000 : ℝ)*x 0 + (-946622939/5000000000 : ℝ)*x 1 + (5206982559/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351668317/10000000000 : ℝ)^4651 ≤ (8971485390313/20000000000000 : ℝ)^3627 := by
    have hnat : (5351668317 : ℕ)^4651*20000000000000^3627 ≤ 8971485390313^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351668317 10000000000 8971485390313 20000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (946622939/5000000000 : ℝ)^4651 ≤ (11834313013859/100000000000000 : ℝ)^3627 := by
    have hnat : (946622939 : ℕ)^4651*100000000000000^3627 ≤ 11834313013859^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946622939 5000000000 11834313013859 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5206982559/10000000000 : ℝ)^4651 ≤ (2165413001059/5000000000000 : ℝ)^3627 := by
    have hnat : (5206982559 : ℕ)^4651*5000000000000^3627 ≤ 2165413001059^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5206982559 10000000000 2165413001059 5000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351668317/10000000000 : ℝ), (-946622939/5000000000 : ℝ), (5206982559/10000000000 : ℝ)] ![(8971485390313/20000000000000 : ℝ), (11834313013859/100000000000000 : ℝ), (2165413001059/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351668317/10000000000 : ℝ)|^4651 ≤ (8971485390313/20000000000000 : ℝ)^3627
        have hw : |(5351668317/10000000000 : ℝ)|=(5351668317/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-946622939/5000000000 : ℝ)|^4651 ≤ (11834313013859/100000000000000 : ℝ)^3627
        have hw : |(-946622939/5000000000 : ℝ)|=(946622939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5206982559/10000000000 : ℝ)|^4651 ≤ (2165413001059/5000000000000 : ℝ)^3627
        have hw : |(5206982559/10000000000 : ℝ)|=(5206982559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s2_2 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5351668247/10000000000 : ℝ)*x 0 + (650872823/1250000000 : ℝ)*x 1 + (-946622969/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5351668247/10000000000 : ℝ)^4651 ≤ (44857426199177/100000000000000 : ℝ)^3627 := by
    have hnat : (5351668247 : ℕ)^4651*100000000000000^3627 ≤ 44857426199177^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5351668247 10000000000 44857426199177 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (650872823/1250000000 : ℝ)^4651 ≤ (43308260287819/100000000000000 : ℝ)^3627 := by
    have hnat : (650872823 : ℕ)^4651*100000000000000^3627 ≤ 43308260287819^3627*1250000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      650872823 1250000000 43308260287819 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (946622969/5000000000 : ℝ)^4651 ≤ (5917156747397/50000000000000 : ℝ)^3627 := by
    have hnat : (946622969 : ℕ)^4651*50000000000000^3627 ≤ 5917156747397^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      946622969 5000000000 5917156747397 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5351668247/10000000000 : ℝ), (650872823/1250000000 : ℝ), (-946622969/5000000000 : ℝ)] ![(44857426199177/100000000000000 : ℝ), (43308260287819/100000000000000 : ℝ), (5917156747397/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5351668247/10000000000 : ℝ)|^4651 ≤ (44857426199177/100000000000000 : ℝ)^3627
        have hw : |(5351668247/10000000000 : ℝ)|=(5351668247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(650872823/1250000000 : ℝ)|^4651 ≤ (43308260287819/100000000000000 : ℝ)^3627
        have hw : |(650872823/1250000000 : ℝ)|=(650872823/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-946622969/5000000000 : ℝ)|^4651 ≤ (5917156747397/50000000000000 : ℝ)^3627
        have hw : |(-946622969/5000000000 : ℝ)|=(946622969/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s2_3 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (423895609/1000000000 : ℝ)*x 0 + (397019169/1000000000 : ℝ)*x 1 + (452218363/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (423895609/1000000000 : ℝ)^4651 ≤ (33267797505857/100000000000000 : ℝ)^3627 := by
    have hnat : (423895609 : ℕ)^4651*100000000000000^3627 ≤ 33267797505857^3627*1000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423895609 1000000000 33267797505857 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (397019169/1000000000 : ℝ)^4651 ≤ (30587580603519/100000000000000 : ℝ)^3627 := by
    have hnat : (397019169 : ℕ)^4651*100000000000000^3627 ≤ 30587580603519^3627*1000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397019169 1000000000 30587580603519 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (452218363/1000000000 : ℝ)^4651 ≤ (18072310936527/50000000000000 : ℝ)^3627 := by
    have hnat : (452218363 : ℕ)^4651*50000000000000^3627 ≤ 18072310936527^3627*1000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      452218363 1000000000 18072310936527 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(423895609/1000000000 : ℝ), (397019169/1000000000 : ℝ), (452218363/1000000000 : ℝ)] ![(33267797505857/100000000000000 : ℝ), (30587580603519/100000000000000 : ℝ), (18072310936527/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(423895609/1000000000 : ℝ)|^4651 ≤ (33267797505857/100000000000000 : ℝ)^3627
        have hw : |(423895609/1000000000 : ℝ)|=(423895609/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(397019169/1000000000 : ℝ)|^4651 ≤ (30587580603519/100000000000000 : ℝ)^3627
        have hw : |(397019169/1000000000 : ℝ)|=(397019169/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(452218363/1000000000 : ℝ)|^4651 ≤ (18072310936527/50000000000000 : ℝ)^3627
        have hw : |(452218363/1000000000 : ℝ)|=(452218363/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s2_4 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1773870883/10000000000 : ℝ)*x 0 + (5208362757/10000000000 : ℝ)*x 1 + (1359580039/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1773870883/10000000000 : ℝ)^4651 ≤ (5443051185627/50000000000000 : ℝ)^3627 := by
    have hnat : (1773870883 : ℕ)^4651*50000000000000^3627 ≤ 5443051185627^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1773870883 10000000000 5443051185627 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5208362757/10000000000 : ℝ)^4651 ≤ (21661490573749/50000000000000 : ℝ)^3627 := by
    have hnat : (5208362757 : ℕ)^4651*50000000000000^3627 ≤ 21661490573749^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5208362757 10000000000 21661490573749 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1359580039/2500000000 : ℝ)^4651 ≤ (11447729116031/25000000000000 : ℝ)^3627 := by
    have hnat : (1359580039 : ℕ)^4651*25000000000000^3627 ≤ 11447729116031^3627*2500000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1359580039 2500000000 11447729116031 25000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1773870883/10000000000 : ℝ), (5208362757/10000000000 : ℝ), (1359580039/2500000000 : ℝ)] ![(5443051185627/50000000000000 : ℝ), (21661490573749/50000000000000 : ℝ), (11447729116031/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1773870883/10000000000 : ℝ)|^4651 ≤ (5443051185627/50000000000000 : ℝ)^3627
        have hw : |(-1773870883/10000000000 : ℝ)|=(1773870883/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5208362757/10000000000 : ℝ)|^4651 ≤ (21661490573749/50000000000000 : ℝ)^3627
        have hw : |(5208362757/10000000000 : ℝ)|=(5208362757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1359580039/2500000000 : ℝ)|^4651 ≤ (11447729116031/25000000000000 : ℝ)^3627
        have hw : |(1359580039/2500000000 : ℝ)|=(1359580039/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s2_5 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2645019377/5000000000 : ℝ)*x 0 + (-830954429/5000000000 : ℝ)*x 1 + (135958029/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2645019377/5000000000 : ℝ)^4651 ≤ (5524510923157/12500000000000 : ℝ)^3627 := by
    have hnat : (2645019377 : ℕ)^4651*12500000000000^3627 ≤ 5524510923157^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2645019377 5000000000 5524510923157 12500000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (830954429/5000000000 : ℝ)^4651 ≤ (10012985299463/100000000000000 : ℝ)^3627 := by
    have hnat : (830954429 : ℕ)^4651*100000000000000^3627 ≤ 10012985299463^3627*5000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      830954429 5000000000 10012985299463 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (135958029/250000000 : ℝ)^4651 ≤ (5723865913071/12500000000000 : ℝ)^3627 := by
    have hnat : (135958029 : ℕ)^4651*12500000000000^3627 ≤ 5723865913071^3627*250000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      135958029 250000000 5723865913071 12500000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2645019377/5000000000 : ℝ), (-830954429/5000000000 : ℝ), (135958029/250000000 : ℝ)] ![(5524510923157/12500000000000 : ℝ), (10012985299463/100000000000000 : ℝ), (5723865913071/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2645019377/5000000000 : ℝ)|^4651 ≤ (5524510923157/12500000000000 : ℝ)^3627
        have hw : |(2645019377/5000000000 : ℝ)|=(2645019377/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-830954429/5000000000 : ℝ)|^4651 ≤ (10012985299463/100000000000000 : ℝ)^3627
        have hw : |(-830954429/5000000000 : ℝ)|=(830954429/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(135958029/250000000 : ℝ)|^4651 ≤ (5723865913071/12500000000000 : ℝ)^3627
        have hw : |(135958029/250000000 : ℝ)|=(135958029/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s2_6 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (529003921/1000000000 : ℝ)*x 0 + (5438322301/10000000000 : ℝ)*x 1 + (-166190663/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (529003921/1000000000 : ℝ)^4651 ≤ (22098046135263/50000000000000 : ℝ)^3627 := by
    have hnat : (529003921 : ℕ)^4651*50000000000000^3627 ≤ 22098046135263^3627*1000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      529003921 1000000000 22098046135263 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5438322301/10000000000 : ℝ)^4651 ≤ (11447734906059/25000000000000 : ℝ)^3627 := by
    have hnat : (5438322301 : ℕ)^4651*25000000000000^3627 ≤ 11447734906059^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5438322301 10000000000 11447734906059 25000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (166190663/1000000000 : ℝ)^4651 ≤ (62581050537/625000000000 : ℝ)^3627 := by
    have hnat : (166190663 : ℕ)^4651*625000000000^3627 ≤ 62581050537^3627*1000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166190663 1000000000 62581050537 625000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(529003921/1000000000 : ℝ), (5438322301/10000000000 : ℝ), (-166190663/1000000000 : ℝ)] ![(22098046135263/50000000000000 : ℝ), (11447734906059/25000000000000 : ℝ), (62581050537/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(529003921/1000000000 : ℝ)|^4651 ≤ (22098046135263/50000000000000 : ℝ)^3627
        have hw : |(529003921/1000000000 : ℝ)|=(529003921/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5438322301/10000000000 : ℝ)|^4651 ≤ (11447734906059/25000000000000 : ℝ)^3627
        have hw : |(5438322301/10000000000 : ℝ)|=(5438322301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-166190663/1000000000 : ℝ)|^4651 ≤ (62581050537/625000000000 : ℝ)^3627
        have hw : |(-166190663/1000000000 : ℝ)|=(166190663/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1577_s2_7 (p : ℝ) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4239048167/10000000000 : ℝ)*x 0 + (4518911327/10000000000 : ℝ)*x 1 + (397349197/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4239048167/10000000000 : ℝ)^4651 ≤ (4158590519663/12500000000000 : ℝ)^3627 := by
    have hnat : (4239048167 : ℕ)^4651*12500000000000^3627 ≤ 4158590519663^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4239048167 10000000000 4158590519663 12500000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4518911327/10000000000 : ℝ)^4651 ≤ (18055543239471/50000000000000 : ℝ)^3627 := by
    have hnat : (4518911327 : ℕ)^4651*50000000000000^3627 ≤ 18055543239471^3627*10000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518911327 10000000000 18055543239471 50000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (397349197/1000000000 : ℝ)^4651 ≤ (30620189355013/100000000000000 : ℝ)^3627 := by
    have hnat : (397349197 : ℕ)^4651*100000000000000^3627 ≤ 30620189355013^3627*1000000000^4651 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397349197 1000000000 30620189355013 100000000000000 4651 3627 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4651/1024 : ℝ)) 4651 3627 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4239048167/10000000000 : ℝ), (4518911327/10000000000 : ℝ), (397349197/1000000000 : ℝ)] ![(4158590519663/12500000000000 : ℝ), (18055543239471/50000000000000 : ℝ), (30620189355013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4239048167/10000000000 : ℝ)|^4651 ≤ (4158590519663/12500000000000 : ℝ)^3627
        have hw : |(4239048167/10000000000 : ℝ)|=(4239048167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4518911327/10000000000 : ℝ)|^4651 ≤ (18055543239471/50000000000000 : ℝ)^3627
        have hw : |(4518911327/10000000000 : ℝ)|=(4518911327/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(397349197/1000000000 : ℝ)|^4651 ≤ (30620189355013/100000000000000 : ℝ)^3627
        have hw : |(397349197/1000000000 : ℝ)|=(397349197/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1577_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168591139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4423/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9147/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5429/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7897/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4423/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9147/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4423/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9147/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4423/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9147/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4423/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9147/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4423/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9147/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4423/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9147/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9147/100000 : ℝ) ^ (4649/1024 : ℝ) ≤ (1923820853412359/100000000000000000000 : ℝ) := by
    have hpowers : (9147/100000 : ℝ)^4649 ≤ (1923820853412359/100000000000000000000 : ℝ)^1024 := by
      have hnat : (9147 : ℕ)^4649*100000000000000000000^1024 ≤ 1923820853412359^1024*100000^4649 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9147 100000 1923820853412359 100000000000000000000 4649 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9147/100000 : ℝ)) (X := (1923820853412359/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4423/25000 : ℝ) ^ (4649/1024 : ℝ) ≤ (38448365469845771/100000000000000000000 : ℝ) := by
    have hpowers : (4423/25000 : ℝ)^4649 ≤ (38448365469845771/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4423 : ℕ)^4649*100000000000000000000^1024 ≤ 38448365469845771^1024*25000^4649 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4423 25000 38448365469845771 100000000000000000000 4649 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4423/25000 : ℝ)) (X := (38448365469845771/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50001923820853412359/50000000000000000000 : ℝ) ≤ (10000084747816873/10000000000000000 : ℝ) ^ (4649/1024 : ℝ) := by
    have hpowers : (50001923820853412359/50000000000000000000 : ℝ)^1024 ≤ (10000084747816873/10000000000000000 : ℝ)^4649 := by
      have hnat : (50001923820853412359 : ℕ)^1024*10000000000000000^4649 ≤ 10000084747816873^4649*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50001923820853412359 50000000000000000000 10000084747816873 10000000000000000 1024 4649 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000084747816873/10000000000000000 : ℝ)) (X := (50001923820853412359/50000000000000000000 : ℝ)) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004037218632325813/10000000000000000000 : ℝ) ≤ (31252778461317/31250000000000 : ℝ) ^ (4649/1024 : ℝ) := by
    have hpowers : (10004037218632325813/10000000000000000000 : ℝ)^1024 ≤ (31252778461317/31250000000000 : ℝ)^4649 := by
      have hnat : (10004037218632325813 : ℕ)^1024*31250000000000^4649 ≤ 31252778461317^4649*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004037218632325813 10000000000000000000 31252778461317 31250000000000 1024 4649 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31252778461317/31250000000000 : ℝ)) (X := (10004037218632325813/10000000000000000000 : ℝ)) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50038448365469845771/50000000000000000000 : ℝ) ≤ (10001693467426007/10000000000000000 : ℝ) ^ (4649/1024 : ℝ) := by
    have hpowers : (50038448365469845771/50000000000000000000 : ℝ)^1024 ≤ (10001693467426007/10000000000000000 : ℝ)^4649 := by
      have hnat : (50038448365469845771 : ℕ)^1024*10000000000000000^4649 ≤ 10001693467426007^4649*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50038448365469845771 50000000000000000000 10001693467426007 10000000000000000 1024 4649 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001693467426007/10000000000000000 : ℝ)) (X := (50038448365469845771/50000000000000000000 : ℝ)) (by norm_num) 4649 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1923820853412359/100000000000000000000 : ℝ) ≤ ((85436009211830431087/85450000000000000000 : ℝ)+2*(804359804567/854500000000000 : ℝ)*(9147/100000 : ℝ))^(4649/1024 : ℝ) := by
    rw [show (85436009211830431087/85450000000000000000 : ℝ)+2*(804359804567/854500000000000 : ℝ)*(9147/100000 : ℝ)=(10000084747816873/10000000000000000 : ℝ) by norm_num, show 1+2*(1923820853412359/100000000000000000000 : ℝ)=(50001923820853412359/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38448365469845771/100000000000000000000 : ℝ)+(1923820853412359/100000000000000000000 : ℝ) ≤ ((85436009211830431087/85450000000000000000 : ℝ)+(804359804567/854500000000000 : ℝ)*((4423/25000 : ℝ)+(9147/100000 : ℝ)))^(4649/1024 : ℝ) := by
    rw [show (85436009211830431087/85450000000000000000 : ℝ)+(804359804567/854500000000000 : ℝ)*((4423/25000 : ℝ)+(9147/100000 : ℝ))=(31252778461317/31250000000000 : ℝ) by norm_num, show 1+(38448365469845771/100000000000000000000 : ℝ)+(1923820853412359/100000000000000000000 : ℝ)=(10004037218632325813/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38448365469845771/100000000000000000000 : ℝ) ≤ ((85436009211830431087/85450000000000000000 : ℝ)+2*(804359804567/854500000000000 : ℝ)*(4423/25000 : ℝ))^(4649/1024 : ℝ) := by
    rw [show (85436009211830431087/85450000000000000000 : ℝ)+2*(804359804567/854500000000000 : ℝ)*(4423/25000 : ℝ)=(10001693467426007/10000000000000000 : ℝ) by norm_num, show 1+2*(38448365469845771/100000000000000000000 : ℝ)=(50038448365469845771/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (85436009211830431087/85450000000000000000 : ℝ)*(X 1 0+X 2 0)+(804359804567/854500000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4649/1024 : ℝ)) (lo := (9147/100000 : ℝ)) (hi := (4423/25000 : ℝ)) (c := (85436009211830431087/85450000000000000000 : ℝ)) (alpha := (804359804567/854500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (85436009211830431087/85450000000000000000 : ℝ)*(X 0 1+X 2 1)+(804359804567/854500000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4649/1024 : ℝ)) (lo := (9147/100000 : ℝ)) (hi := (4423/25000 : ℝ)) (c := (85436009211830431087/85450000000000000000 : ℝ)) (alpha := (804359804567/854500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (85436009211830431087/85450000000000000000 : ℝ)*(X 0 2+X 1 2)+(804359804567/854500000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4649/1024 : ℝ)) (lo := (9147/100000 : ℝ)) (hi := (4423/25000 : ℝ)) (c := (85436009211830431087/85450000000000000000 : ℝ)) (alpha := (804359804567/854500000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1773832463/10000000000 : ℝ)*X 0 0+(135992789/250000000 : ℝ)*X 0 1+(130174563/250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5351668317/10000000000 : ℝ)*X 1 0+(-946622939/5000000000 : ℝ)*X 1 1+(5206982559/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5351668247/10000000000 : ℝ)*X 2 0+(650872823/1250000000 : ℝ)*X 2 1+(-946622969/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((423895609/1000000000 : ℝ)*X 0 0+(397019169/1000000000 : ℝ)*X 0 1+(452218363/1000000000 : ℝ)*X 0 2+(423895609/1000000000 : ℝ)*X 1 0+(397019169/1000000000 : ℝ)*X 1 1+(452218363/1000000000 : ℝ)*X 1 2+(423895609/1000000000 : ℝ)*X 2 0+(397019169/1000000000 : ℝ)*X 2 1+(452218363/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1773870883/10000000000 : ℝ)*X 0 0+(5208362757/10000000000 : ℝ)*X 0 1+(1359580039/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2645019377/5000000000 : ℝ)*X 1 0+(-830954429/5000000000 : ℝ)*X 1 1+(135958029/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((529003921/1000000000 : ℝ)*X 2 0+(5438322301/10000000000 : ℝ)*X 2 1+(-166190663/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4239048167/10000000000 : ℝ)*X 0 0+(4518911327/10000000000 : ℝ)*X 0 1+(397349197/1000000000 : ℝ)*X 0 2+(4239048167/10000000000 : ℝ)*X 1 0+(4518911327/10000000000 : ℝ)*X 1 1+(397349197/1000000000 : ℝ)*X 1 2+(4239048167/10000000000 : ℝ)*X 2 0+(4518911327/10000000000 : ℝ)*X 2 1+(397349197/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1577_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (3054419681933063213319738741/267031250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (200727481/10000000000000 : ℝ)*(base19) + (1780453397/100000000000000 : ℝ)*(base23) + (18261799/20000000000000 : ℝ)*(lower2) + (82670843/25000000000000 : ℝ)*(upper3) + (138301237/100000000000000 : ℝ)*(upper5) + (381784262436181/12500000000000 : ℝ)*(major0) + (381784262436181/12500000000000 : ℝ)*(major1) + (381784262436181/12500000000000 : ℝ)*(major2) + (537109263986687/12500000000000 : ℝ)*(sp0) + (1074225030687897/25000000000000 : ℝ)*(sp1) + (4296900349573/100000000000 : ℝ)*(sp2) + (1811631969652383/100000000000000 : ℝ)*(sp3) + (14009066451/50000000000000 : ℝ)*(sp4) + (13718018929/100000000000000 : ℝ)*(sp7) + (113227855479457/6250000000000 : ℝ)*(f.failure) + (2148451065013199/50000000000000 : ℝ)*(f.sum) + (10748584060759/42725000000000000000000000000 : ℝ)*base66 + (2872776405045716253/1068125000000000000000000000000000 : ℝ)*base68 + (6117956370248841253/1068125000000000000000000000000000 : ℝ)*base70 + (4752251699319466253/1068125000000000000000000000000000 : ℝ)*base72 + (161403716023991/42725000000000000000000000000 : ℝ)*base73 + (12097844633711341253/1068125000000000000000000000000000 : ℝ)*base76 + (6198706694908033747/1068125000000000000000000000000000 : ℝ)*base77 + (15373563911941966253/1068125000000000000000000000000000 : ℝ)*base80 + (17244558666129/10681250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (3268477/625000000000000000000 : ℝ)*base90 + (3268477/625000000000000000000 : ℝ)*base92 + (3268477/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (365386005387126659415117/21362500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1212191533/100000000000000 : ℝ)*(base23) + (21322087/25000000000000 : ℝ)*(lower2) + (269820419/100000000000000 : ℝ)*(upper3) + (107127257/50000000000000 : ℝ)*(lower4) + (88053039/100000000000000 : ℝ)*(upper5) + (1545521159704161/50000000000000 : ℝ)*(major0) + (1545521159704161/50000000000000 : ℝ)*(major1) + (1545521159704161/50000000000000 : ℝ)*(major2) + (7209430623/100000000000000 : ℝ)*(sp1) + (7269743223/12500000000000 : ℝ)*(sp2) + (2174314637591259/50000000000000 : ℝ)*(sp4) + (869724413150379/20000000000000 : ℝ)*(sp5) + (10871424762613/250000000000 : ℝ)*(sp6) + (114590924593623/6250000000000 : ℝ)*(sp7) + (114590924593623/6250000000000 : ℝ)*(f.failure) + (2174314637591259/50000000000000 : ℝ)*(f.sum) + (142857929310953/5340625000000000000000000000 : ℝ)*base65 + (12026456522548646993/4272500000000000000000000000000000 : ℝ)*base68 + (4927202615433646993/4272500000000000000000000000000000 : ℝ)*base70 + (18350722329113853007/4272500000000000000000000000000000 : ℝ)*base71 + (154513169764687/21362500000000000000000000000 : ℝ)*base73 + (38901565690786146993/4272500000000000000000000000000000 : ℝ)*base76 + (25250799887006353007/4272500000000000000000000000000000 : ℝ)*base77 + (26645868174026353007/4272500000000000000000000000000000 : ℝ)*base79 + (12383331631887/21362500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (1206597/625000000000000000000 : ℝ)*base89 + (1206597/625000000000000000000 : ℝ)*base91 + (1206597/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1577_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168591139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4423/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9147/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5429/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7897/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1577_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1577_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168591139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5429/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7897/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1577_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1577_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1577_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4649/1024 : ℝ) ≤ p) (hpb : p ≤ (4651/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168591139/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5429/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7897/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1577_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
