-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1575_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:28:36.965777+00:00
-- url     : https://prove2.me/submissions/08037c25-f59a-4afa-b807-94146192ee95

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
theorem support_rectangle_w1575_s6_0 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-444701957/2500000000 : ℝ)*x 0 + (5425150359/10000000000 : ℝ)*x 1 + (326264629/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (444701957/2500000000 : ℝ)^4647 ≤ (10919090825891/100000000000000 : ℝ)^3623 := by
    have hnat : (444701957 : ℕ)^4647*100000000000000^3623 ≤ 10919090825891^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      444701957 2500000000 10919090825891 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5425150359/10000000000 : ℝ)^4647 ≤ (45640066708823/100000000000000 : ℝ)^3623 := by
    have hnat : (5425150359 : ℕ)^4647*100000000000000^3623 ≤ 45640066708823^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5425150359 10000000000 45640066708823 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (326264629/625000000 : ℝ)^4647 ≤ (43440842449213/100000000000000 : ℝ)^3623 := by
    have hnat : (326264629 : ℕ)^4647*100000000000000^3623 ≤ 43440842449213^3623*625000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      326264629 625000000 43440842449213 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-444701957/2500000000 : ℝ), (5425150359/10000000000 : ℝ), (326264629/625000000 : ℝ)] ![(10919090825891/100000000000000 : ℝ), (45640066708823/100000000000000 : ℝ), (43440842449213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-444701957/2500000000 : ℝ)|^4647 ≤ (10919090825891/100000000000000 : ℝ)^3623
        have hw : |(-444701957/2500000000 : ℝ)|=(444701957/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5425150359/10000000000 : ℝ)|^4647 ≤ (45640066708823/100000000000000 : ℝ)^3623
        have hw : |(5425150359/10000000000 : ℝ)|=(5425150359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(326264629/625000000 : ℝ)|^4647 ≤ (43440842449213/100000000000000 : ℝ)^3623
        have hw : |(326264629/625000000 : ℝ)|=(326264629/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s6_1 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336970081/2500000000 : ℝ)*x 0 + (-1883630147/10000000000 : ℝ)*x 1 + (2610117387/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336970081/2500000000 : ℝ)^4647 ≤ (22403986816957/50000000000000 : ℝ)^3623 := by
    have hnat : (1336970081 : ℕ)^4647*50000000000000^3623 ≤ 22403986816957^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336970081 2500000000 22403986816957 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1883630147/10000000000 : ℝ)^4647 ≤ (11751176321319/100000000000000 : ℝ)^3623 := by
    have hnat : (1883630147 : ℕ)^4647*100000000000000^3623 ≤ 11751176321319^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883630147 10000000000 11751176321319 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2610117387/5000000000 : ℝ)^4647 ≤ (43440850027499/100000000000000 : ℝ)^3623 := by
    have hnat : (2610117387 : ℕ)^4647*100000000000000^3623 ≤ 43440850027499^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2610117387 5000000000 43440850027499 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336970081/2500000000 : ℝ), (-1883630147/10000000000 : ℝ), (2610117387/5000000000 : ℝ)] ![(22403986816957/50000000000000 : ℝ), (11751176321319/100000000000000 : ℝ), (43440850027499/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336970081/2500000000 : ℝ)|^4647 ≤ (22403986816957/50000000000000 : ℝ)^3623
        have hw : |(1336970081/2500000000 : ℝ)|=(1336970081/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1883630147/10000000000 : ℝ)|^4647 ≤ (11751176321319/100000000000000 : ℝ)^3623
        have hw : |(-1883630147/10000000000 : ℝ)|=(1883630147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2610117387/5000000000 : ℝ)|^4647 ≤ (43440850027499/100000000000000 : ℝ)^3623
        have hw : |(2610117387/5000000000 : ℝ)|=(2610117387/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s6_2 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1336970123/2500000000 : ℝ)*x 0 + (652529311/1250000000 : ℝ)*x 1 + (-1883630303/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1336970123/2500000000 : ℝ)^4647 ≤ (44807975439371/100000000000000 : ℝ)^3623 := by
    have hnat : (1336970123 : ℕ)^4647*100000000000000^3623 ≤ 44807975439371^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1336970123 2500000000 44807975439371 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (652529311/1250000000 : ℝ)^4647 ≤ (43440846974837/100000000000000 : ℝ)^3623 := by
    have hnat : (652529311 : ℕ)^4647*100000000000000^3623 ≤ 43440846974837^3623*1250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      652529311 1250000000 43440846974837 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1883630303/10000000000 : ℝ)^4647 ≤ (11751177569607/100000000000000 : ℝ)^3623 := by
    have hnat : (1883630303 : ℕ)^4647*100000000000000^3623 ≤ 11751177569607^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1883630303 10000000000 11751177569607 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1336970123/2500000000 : ℝ), (652529311/1250000000 : ℝ), (-1883630303/10000000000 : ℝ)] ![(44807975439371/100000000000000 : ℝ), (43440846974837/100000000000000 : ℝ), (11751177569607/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1336970123/2500000000 : ℝ)|^4647 ≤ (44807975439371/100000000000000 : ℝ)^3623
        have hw : |(1336970123/2500000000 : ℝ)|=(1336970123/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(652529311/1250000000 : ℝ)|^4647 ≤ (43440846974837/100000000000000 : ℝ)^3623
        have hw : |(652529311/1250000000 : ℝ)|=(652529311/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1883630303/10000000000 : ℝ)|^4647 ≤ (11751177569607/100000000000000 : ℝ)^3623
        have hw : |(-1883630303/10000000000 : ℝ)|=(1883630303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s6_3 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265081857/625000000 : ℝ)*x 0 + (2002114019/5000000000 : ℝ)*x 1 + (1122398117/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265081857/625000000 : ℝ)^4647 ≤ (33282586438877/100000000000000 : ℝ)^3623 := by
    have hnat : (265081857 : ℕ)^4647*100000000000000^3623 ≤ 33282586438877^3623*625000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265081857 625000000 33282586438877 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2002114019/5000000000 : ℝ)^4647 ≤ (30915425938833/100000000000000 : ℝ)^3623 := by
    have hnat : (2002114019 : ℕ)^4647*100000000000000^3623 ≤ 30915425938833^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2002114019 5000000000 30915425938833 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1122398117/2500000000 : ℝ)^4647 ≤ (35801987610137/100000000000000 : ℝ)^3623 := by
    have hnat : (1122398117 : ℕ)^4647*100000000000000^3623 ≤ 35801987610137^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1122398117 2500000000 35801987610137 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265081857/625000000 : ℝ), (2002114019/5000000000 : ℝ), (1122398117/2500000000 : ℝ)] ![(33282586438877/100000000000000 : ℝ), (30915425938833/100000000000000 : ℝ), (35801987610137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265081857/625000000 : ℝ)|^4647 ≤ (33282586438877/100000000000000 : ℝ)^3623
        have hw : |(265081857/625000000 : ℝ)|=(265081857/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2002114019/5000000000 : ℝ)|^4647 ≤ (30915425938833/100000000000000 : ℝ)^3623
        have hw : |(2002114019/5000000000 : ℝ)|=(2002114019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1122398117/2500000000 : ℝ)|^4647 ≤ (35801987610137/100000000000000 : ℝ)^3623
        have hw : |(1122398117/2500000000 : ℝ)|=(1122398117/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s6_4 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1778834701/10000000000 : ℝ)*x 0 + (5221302731/10000000000 : ℝ)*x 1 + (542407359/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1778834701/10000000000 : ℝ)^4647 ≤ (10919302407963/100000000000000 : ℝ)^3623 := by
    have hnat : (1778834701 : ℕ)^4647*100000000000000^3623 ≤ 10919302407963^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1778834701 10000000000 10919302407963 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5221302731/10000000000 : ℝ)^4647 ≤ (5431531168419/12500000000000 : ℝ)^3623 := by
    have hnat : (5221302731 : ℕ)^4647*12500000000000^3623 ≤ 5431531168419^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5221302731 10000000000 5431531168419 12500000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (542407359/1000000000 : ℝ)^4647 ≤ (45628448232123/100000000000000 : ℝ)^3623 := by
    have hnat : (542407359 : ℕ)^4647*100000000000000^3623 ≤ 45628448232123^3623*1000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542407359 1000000000 45628448232123 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1778834701/10000000000 : ℝ), (5221302731/10000000000 : ℝ), (542407359/1000000000 : ℝ)] ![(10919302407963/100000000000000 : ℝ), (5431531168419/12500000000000 : ℝ), (45628448232123/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1778834701/10000000000 : ℝ)|^4647 ≤ (10919302407963/100000000000000 : ℝ)^3623
        have hw : |(-1778834701/10000000000 : ℝ)|=(1778834701/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5221302731/10000000000 : ℝ)|^4647 ≤ (5431531168419/12500000000000 : ℝ)^3623
        have hw : |(5221302731/10000000000 : ℝ)|=(5221302731/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(542407359/1000000000 : ℝ)|^4647 ≤ (45628448232123/100000000000000 : ℝ)^3623
        have hw : |(542407359/1000000000 : ℝ)|=(542407359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s6_5 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1323408571/2500000000 : ℝ)*x 0 + (542407359/1000000000 : ℝ)*x 1 + (-1679791143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1323408571/2500000000 : ℝ)^4647 ≤ (691028775183/1562500000000 : ℝ)^3623 := by
    have hnat : (1323408571 : ℕ)^4647*1562500000000^3623 ≤ 691028775183^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1323408571 2500000000 691028775183 1562500000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (542407359/1000000000 : ℝ)^4647 ≤ (45628448232123/100000000000000 : ℝ)^3623 := by
    have hnat : (542407359 : ℕ)^4647*100000000000000^3623 ≤ 45628448232123^3623*1000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      542407359 1000000000 45628448232123 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1679791143/10000000000 : ℝ)^4647 ≤ (10145710144647/100000000000000 : ℝ)^3623 := by
    have hnat : (1679791143 : ℕ)^4647*100000000000000^3623 ≤ 10145710144647^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1679791143 10000000000 10145710144647 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1323408571/2500000000 : ℝ), (542407359/1000000000 : ℝ), (-1679791143/10000000000 : ℝ)] ![(691028775183/1562500000000 : ℝ), (45628448232123/100000000000000 : ℝ), (10145710144647/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1323408571/2500000000 : ℝ)|^4647 ≤ (691028775183/1562500000000 : ℝ)^3623
        have hw : |(1323408571/2500000000 : ℝ)|=(1323408571/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(542407359/1000000000 : ℝ)|^4647 ≤ (45628448232123/100000000000000 : ℝ)^3623
        have hw : |(542407359/1000000000 : ℝ)|=(542407359/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1679791143/10000000000 : ℝ)|^4647 ≤ (10145710144647/100000000000000 : ℝ)^3623
        have hw : |(-1679791143/10000000000 : ℝ)|=(1679791143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_s6_6 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (848274533/2000000000 : ℝ)*x 0 + (4487061623/10000000000 : ℝ)*x 1 + (2003388819/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (848274533/2000000000 : ℝ)^4647 ≤ (33283220073299/100000000000000 : ℝ)^3623 := by
    have hnat : (848274533 : ℕ)^4647*100000000000000^3623 ≤ 33283220073299^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      848274533 2000000000 33283220073299 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487061623/10000000000 : ℝ)^4647 ≤ (35776103365249/100000000000000 : ℝ)^3623 := by
    have hnat : (4487061623 : ℕ)^4647*100000000000000^3623 ≤ 35776103365249^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487061623 10000000000 35776103365249 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2003388819/5000000000 : ℝ)^4647 ≤ (3867584568733/12500000000000 : ℝ)^3623 := by
    have hnat : (2003388819 : ℕ)^4647*12500000000000^3623 ≤ 3867584568733^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2003388819 5000000000 3867584568733 12500000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(848274533/2000000000 : ℝ), (4487061623/10000000000 : ℝ), (2003388819/5000000000 : ℝ)] ![(33283220073299/100000000000000 : ℝ), (35776103365249/100000000000000 : ℝ), (3867584568733/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(848274533/2000000000 : ℝ)|^4647 ≤ (33283220073299/100000000000000 : ℝ)^3623
        have hw : |(848274533/2000000000 : ℝ)|=(848274533/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487061623/10000000000 : ℝ)|^4647 ≤ (35776103365249/100000000000000 : ℝ)^3623
        have hw : |(4487061623/10000000000 : ℝ)|=(4487061623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2003388819/5000000000 : ℝ)|^4647 ≤ (3867584568733/12500000000000 : ℝ)^3623
        have hw : |(2003388819/5000000000 : ℝ)|=(2003388819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1575_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5569/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3871/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11137/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11137/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11137/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11137/100000 : ℝ) ^ (4645/1024 : ℝ) ≤ (474257320530811/10000000000000000000 : ℝ) := by
    have hpowers : (11137/100000 : ℝ)^4645 ≤ (474257320530811/10000000000000000000 : ℝ)^1024 := by
      have hnat : (11137 : ℕ)^4645*10000000000000000000^1024 ≤ 474257320530811^1024*100000^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11137 100000 474257320530811 10000000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11137/100000 : ℝ)) (X := (474257320530811/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4645/1024 : ℝ) ≤ (10572372015202783/50000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4645 ≤ (10572372015202783/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4645*50000000000000000000^1024 ≤ 10572372015202783^1024*25000^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 10572372015202783 50000000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (10572372015202783/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000474257320530811/5000000000000000000 : ℝ) ≤ (2000041818862677/2000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (5000474257320530811/5000000000000000000 : ℝ)^1024 ≤ (2000041818862677/2000000000000000 : ℝ)^4645 := by
      have hnat : (5000474257320530811 : ℕ)^1024*2000000000000000^4645 ≤ 2000041818862677^4645*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000474257320530811 5000000000000000000 2000041818862677 2000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000041818862677/2000000000000000 : ℝ)) (X := (5000474257320530811/5000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25006471829308928419/25000000000000000000 : ℝ) ≤ (10000570633767223/10000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (25006471829308928419/25000000000000000000 : ℝ)^1024 ≤ (10000570633767223/10000000000000000 : ℝ)^4645 := by
      have hnat : (25006471829308928419 : ℕ)^1024*10000000000000000^4645 ≤ 10000570633767223^4645*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006471829308928419 25000000000000000000 10000570633767223 10000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000570633767223/10000000000000000 : ℝ)) (X := (25006471829308928419/25000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010572372015202783/25000000000000000000 : ℝ) ≤ (10000932173221061/10000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (25010572372015202783/25000000000000000000 : ℝ)^1024 ≤ (10000932173221061/10000000000000000 : ℝ)^4645 := by
      have hnat : (25010572372015202783 : ℕ)^1024*10000000000000000^4645 ≤ 10000932173221061^4645*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010572372015202783 25000000000000000000 10000932173221061 10000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000932173221061/10000000000000000 : ℝ)) (X := (25010572372015202783/25000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(474257320530811/10000000000000000000 : ℝ) ≤ ((6208979429026499569/6210000000000000000 : ℝ)+2*(180769726919/217350000000000 : ℝ)*(11137/100000 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (6208979429026499569/6210000000000000000 : ℝ)+2*(180769726919/217350000000000 : ℝ)*(11137/100000 : ℝ)=(2000041818862677/2000000000000000 : ℝ) by norm_num, show 1+2*(474257320530811/10000000000000000000 : ℝ)=(5000474257320530811/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10572372015202783/50000000000000000000 : ℝ)+(474257320530811/10000000000000000000 : ℝ) ≤ ((6208979429026499569/6210000000000000000 : ℝ)+(180769726919/217350000000000 : ℝ)*((3871/25000 : ℝ)+(11137/100000 : ℝ)))^(4645/1024 : ℝ) := by
    rw [show (6208979429026499569/6210000000000000000 : ℝ)+(180769726919/217350000000000 : ℝ)*((3871/25000 : ℝ)+(11137/100000 : ℝ))=(10000570633767223/10000000000000000 : ℝ) by norm_num, show 1+(10572372015202783/50000000000000000000 : ℝ)+(474257320530811/10000000000000000000 : ℝ)=(25006471829308928419/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10572372015202783/50000000000000000000 : ℝ) ≤ ((6208979429026499569/6210000000000000000 : ℝ)+2*(180769726919/217350000000000 : ℝ)*(3871/25000 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (6208979429026499569/6210000000000000000 : ℝ)+2*(180769726919/217350000000000 : ℝ)*(3871/25000 : ℝ)=(10000932173221061/10000000000000000 : ℝ) by norm_num, show 1+2*(10572372015202783/50000000000000000000 : ℝ)=(25010572372015202783/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (6208979429026499569/6210000000000000000 : ℝ)*(X 1 0+X 2 0)+(180769726919/217350000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (11137/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (6208979429026499569/6210000000000000000 : ℝ)) (alpha := (180769726919/217350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (6208979429026499569/6210000000000000000 : ℝ)*(X 0 1+X 2 1)+(180769726919/217350000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (11137/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (6208979429026499569/6210000000000000000 : ℝ)) (alpha := (180769726919/217350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (6208979429026499569/6210000000000000000 : ℝ)*(X 0 2+X 1 2)+(180769726919/217350000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (11137/100000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (6208979429026499569/6210000000000000000 : ℝ)) (alpha := (180769726919/217350000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-444701957/2500000000 : ℝ)*X 0 0+(5425150359/10000000000 : ℝ)*X 0 1+(326264629/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1336970081/2500000000 : ℝ)*X 1 0+(-1883630147/10000000000 : ℝ)*X 1 1+(2610117387/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1336970123/2500000000 : ℝ)*X 2 0+(652529311/1250000000 : ℝ)*X 2 1+(-1883630303/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((265081857/625000000 : ℝ)*X 0 0+(2002114019/5000000000 : ℝ)*X 0 1+(1122398117/2500000000 : ℝ)*X 0 2+(265081857/625000000 : ℝ)*X 1 0+(2002114019/5000000000 : ℝ)*X 1 1+(1122398117/2500000000 : ℝ)*X 1 2+(265081857/625000000 : ℝ)*X 2 0+(2002114019/5000000000 : ℝ)*X 2 1+(1122398117/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1778834701/10000000000 : ℝ)*X 0 0+(5221302731/10000000000 : ℝ)*X 0 1+(542407359/1000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1323408571/2500000000 : ℝ)*X 2 0+(542407359/1000000000 : ℝ)*X 2 1+(-1679791143/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s6_5 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((848274533/2000000000 : ℝ)*X 0 0+(4487061623/10000000000 : ℝ)*X 0 1+(2003388819/5000000000 : ℝ)*X 0 2+(848274533/2000000000 : ℝ)*X 1 0+(4487061623/10000000000 : ℝ)*X 1 1+(2003388819/5000000000 : ℝ)*X 1 2+(848274533/2000000000 : ℝ)*X 2 0+(4487061623/10000000000 : ℝ)*X 2 1+(2003388819/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_s6_6 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (15023835438980053573631857/4500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (119987699/100000000000000 : ℝ)*(base23) + (82692947/100000000000000 : ℝ)*(lower2) + (1581569/12500000000000 : ℝ)*(upper3) + (81497739/100000000000000 : ℝ)*(lower4) + (3470194827754627/100000000000000 : ℝ)*(major0) + (3470194827754627/100000000000000 : ℝ)*(major1) + (3470194827754627/100000000000000 : ℝ)*(major2) + (305003577730111/6250000000000 : ℝ)*(sp0) + (305004601306969/6250000000000 : ℝ)*(sp1) + (4880070436738869/100000000000000 : ℝ)*(sp2) + (1030155745742579/50000000000000 : ℝ)*(sp3) + (511788429/3125000000000 : ℝ)*(sp4) + (383023117/12500000000000 : ℝ)*(sp5) + (4431824919/100000000000000 : ℝ)*(sp6) + (2060315923310077/100000000000000 : ℝ)*(f.failure) + (305004601306969/6250000000000 : ℝ)*(f.sum) + (6044283385543/3105000000000000000000000000 : ℝ)*base65 + (3011588528592055763/621000000000000000000000000000000 : ℝ)*base67 + (4686013087095055763/621000000000000000000000000000000 : ℝ)*base69 + (1348517842878055763/621000000000000000000000000000000 : ℝ)*base71 + (3066322779647/3105000000000000000000000000 : ℝ)*base74 + (1023020422743055763/621000000000000000000000000000000 : ℝ)*base75 + (1247703413682055763/621000000000000000000000000000000 : ℝ)*base77 + (3093306191832055763/621000000000000000000000000000000 : ℝ)*base79 + (12313209032263/3105000000000000000000000000 : ℝ)*base81 + (7117633/10000000000000000000000 : ℝ)*base89 + (7117633/10000000000000000000000 : ℝ)*base91 + (7117633/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(upper0) + hcertificate_margin
theorem rectangle_w1575_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1575_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1575_box_0 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-787901447/5000000000 : ℝ)*x 0 + (5396055867/10000000000 : ℝ)*x 1 + (2698028049/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (787901447/5000000000 : ℝ)^4647 ≤ (9347271868377/100000000000000 : ℝ)^3623 := by
    have hnat : (787901447 : ℕ)^4647*100000000000000^3623 ≤ 9347271868377^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      787901447 5000000000 9347271868377 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5396055867/10000000000 : ℝ)^4647 ≤ (22663181404751/50000000000000 : ℝ)^3623 := by
    have hnat : (5396055867 : ℕ)^4647*50000000000000^3623 ≤ 22663181404751^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5396055867 10000000000 22663181404751 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2698028049/5000000000 : ℝ)^4647 ≤ (45326365298307/100000000000000 : ℝ)^3623 := by
    have hnat : (2698028049 : ℕ)^4647*100000000000000^3623 ≤ 45326365298307^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2698028049 5000000000 45326365298307 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-787901447/5000000000 : ℝ), (5396055867/10000000000 : ℝ), (2698028049/5000000000 : ℝ)] ![(9347271868377/100000000000000 : ℝ), (22663181404751/50000000000000 : ℝ), (45326365298307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-787901447/5000000000 : ℝ)|^4647 ≤ (9347271868377/100000000000000 : ℝ)^3623
        have hw : |(-787901447/5000000000 : ℝ)|=(787901447/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5396055867/10000000000 : ℝ)|^4647 ≤ (22663181404751/50000000000000 : ℝ)^3623
        have hw : |(5396055867/10000000000 : ℝ)|=(5396055867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2698028049/5000000000 : ℝ)|^4647 ≤ (45326365298307/100000000000000 : ℝ)^3623
        have hw : |(2698028049/5000000000 : ℝ)|=(2698028049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_1 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054228639/2000000000 : ℝ)*x 0 + (-87473613/500000000 : ℝ)*x 1 + (107921119/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054228639/2000000000 : ℝ)^4647 ≤ (2199248769793/5000000000000 : ℝ)^3623 := by
    have hnat : (1054228639 : ℕ)^4647*5000000000000^3623 ≤ 2199248769793^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054228639 2000000000 2199248769793 5000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (87473613/500000000 : ℝ)^4647 ≤ (10688660883873/100000000000000 : ℝ)^3623 := by
    have hnat : (87473613 : ℕ)^4647*100000000000000^3623 ≤ 10688660883873^3623*500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      87473613 500000000 10688660883873 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (107921119/200000000 : ℝ)^4647 ≤ (11331590925937/25000000000000 : ℝ)^3623 := by
    have hnat : (107921119 : ℕ)^4647*25000000000000^3623 ≤ 11331590925937^3623*200000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107921119 200000000 11331590925937 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054228639/2000000000 : ℝ), (-87473613/500000000 : ℝ), (107921119/200000000 : ℝ)] ![(2199248769793/5000000000000 : ℝ), (10688660883873/100000000000000 : ℝ), (11331590925937/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054228639/2000000000 : ℝ)|^4647 ≤ (2199248769793/5000000000000 : ℝ)^3623
        have hw : |(1054228639/2000000000 : ℝ)|=(1054228639/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-87473613/500000000 : ℝ)|^4647 ≤ (10688660883873/100000000000000 : ℝ)^3623
        have hw : |(-87473613/500000000 : ℝ)|=(87473613/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(107921119/200000000 : ℝ)|^4647 ≤ (11331590925937/25000000000000 : ℝ)^3623
        have hw : |(107921119/200000000 : ℝ)|=(107921119/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_2 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1054228643/2000000000 : ℝ)*x 0 + (215842233/400000000 : ℝ)*x 1 + (-349894481/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1054228643/2000000000 : ℝ)^4647 ≤ (43984975609919/100000000000000 : ℝ)^3623 := by
    have hnat : (1054228643 : ℕ)^4647*100000000000000^3623 ≤ 43984975609919^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1054228643 2000000000 43984975609919 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215842233/400000000 : ℝ)^4647 ≤ (177056102957/390625000000 : ℝ)^3623 := by
    have hnat : (215842233 : ℕ)^4647*390625000000^3623 ≤ 177056102957^3623*400000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215842233 400000000 177056102957 390625000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (349894481/2000000000 : ℝ)^4647 ≤ (5344331010081/50000000000000 : ℝ)^3623 := by
    have hnat : (349894481 : ℕ)^4647*50000000000000^3623 ≤ 5344331010081^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      349894481 2000000000 5344331010081 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1054228643/2000000000 : ℝ), (215842233/400000000 : ℝ), (-349894481/2000000000 : ℝ)] ![(43984975609919/100000000000000 : ℝ), (177056102957/390625000000 : ℝ), (5344331010081/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1054228643/2000000000 : ℝ)|^4647 ≤ (43984975609919/100000000000000 : ℝ)^3623
        have hw : |(1054228643/2000000000 : ℝ)|=(1054228643/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215842233/400000000 : ℝ)|^4647 ≤ (177056102957/390625000000 : ℝ)^3623
        have hw : |(215842233/400000000 : ℝ)|=(215842233/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-349894481/2000000000 : ℝ)|^4647 ≤ (5344331010081/50000000000000 : ℝ)^3623
        have hw : |(-349894481/2000000000 : ℝ)|=(349894481/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_3 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (555226283/1250000000 : ℝ)*x 0 + (1036916529/2500000000 : ℝ)*x 1 + (4147666127/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (555226283/1250000000 : ℝ)^4647 ≤ (35313992611521/100000000000000 : ℝ)^3623 := by
    have hnat : (555226283 : ℕ)^4647*100000000000000^3623 ≤ 35313992611521^3623*1250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      555226283 1250000000 35313992611521 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1036916529/2500000000 : ℝ)^4647 ≤ (6468600726213/20000000000000 : ℝ)^3623 := by
    have hnat : (1036916529 : ℕ)^4647*20000000000000^3623 ≤ 6468600726213^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1036916529 2500000000 6468600726213 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4147666127/10000000000 : ℝ)^4647 ≤ (16171501870543/50000000000000 : ℝ)^3623 := by
    have hnat : (4147666127 : ℕ)^4647*50000000000000^3623 ≤ 16171501870543^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4147666127 10000000000 16171501870543 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(555226283/1250000000 : ℝ), (1036916529/2500000000 : ℝ), (4147666127/10000000000 : ℝ)] ![(35313992611521/100000000000000 : ℝ), (6468600726213/20000000000000 : ℝ), (16171501870543/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(555226283/1250000000 : ℝ)|^4647 ≤ (35313992611521/100000000000000 : ℝ)^3623
        have hw : |(555226283/1250000000 : ℝ)|=(555226283/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1036916529/2500000000 : ℝ)|^4647 ≤ (6468600726213/20000000000000 : ℝ)^3623
        have hw : |(1036916529/2500000000 : ℝ)|=(1036916529/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4147666127/10000000000 : ℝ)|^4647 ≤ (16171501870543/50000000000000 : ℝ)^3623
        have hw : |(4147666127/10000000000 : ℝ)|=(4147666127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_4 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1987197079/10000000000 : ℝ)*x 0 + (262257051/500000000 : ℝ)*x 1 + (2622570599/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1987197079/10000000000 : ℝ)^4647 ≤ (12586259268623/100000000000000 : ℝ)^3623 := by
    have hnat : (1987197079 : ℕ)^4647*100000000000000^3623 ≤ 12586259268623^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987197079 10000000000 12586259268623 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (262257051/500000000 : ℝ)^4647 ≤ (349654955283/800000000000 : ℝ)^3623 := by
    have hnat : (262257051 : ℕ)^4647*800000000000^3623 ≤ 349654955283^3623*500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262257051 500000000 349654955283 800000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2622570599/5000000000 : ℝ)^4647 ≤ (43706871312841/100000000000000 : ℝ)^3623 := by
    have hnat : (2622570599 : ℕ)^4647*100000000000000^3623 ≤ 43706871312841^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622570599 5000000000 43706871312841 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1987197079/10000000000 : ℝ), (262257051/500000000 : ℝ), (2622570599/5000000000 : ℝ)] ![(12586259268623/100000000000000 : ℝ), (349654955283/800000000000 : ℝ), (43706871312841/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1987197079/10000000000 : ℝ)|^4647 ≤ (12586259268623/100000000000000 : ℝ)^3623
        have hw : |(-1987197079/10000000000 : ℝ)|=(1987197079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(262257051/500000000 : ℝ)|^4647 ≤ (349654955283/800000000000 : ℝ)^3623
        have hw : |(262257051/500000000 : ℝ)|=(262257051/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2622570599/5000000000 : ℝ)|^4647 ≤ (43706871312841/100000000000000 : ℝ)^3623
        have hw : |(2622570599/5000000000 : ℝ)|=(2622570599/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_5 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1343928747/2500000000 : ℝ)*x 0 + (-906296321/5000000000 : ℝ)*x 1 + (655642649/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1343928747/2500000000 : ℝ)^4647 ≤ (45107326122341/100000000000000 : ℝ)^3623 := by
    have hnat : (1343928747 : ℕ)^4647*100000000000000^3623 ≤ 45107326122341^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1343928747 2500000000 45107326122341 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (906296321/5000000000 : ℝ)^4647 ≤ (2237160520947/20000000000000 : ℝ)^3623 := by
    have hnat : (906296321 : ℕ)^4647*20000000000000^3623 ≤ 2237160520947^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906296321 5000000000 2237160520947 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (655642649/1250000000 : ℝ)^4647 ≤ (43706871248713/100000000000000 : ℝ)^3623 := by
    have hnat : (655642649 : ℕ)^4647*100000000000000^3623 ≤ 43706871248713^3623*1250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655642649 1250000000 43706871248713 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1343928747/2500000000 : ℝ), (-906296321/5000000000 : ℝ), (655642649/1250000000 : ℝ)] ![(45107326122341/100000000000000 : ℝ), (2237160520947/20000000000000 : ℝ), (43706871248713/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1343928747/2500000000 : ℝ)|^4647 ≤ (45107326122341/100000000000000 : ℝ)^3623
        have hw : |(1343928747/2500000000 : ℝ)|=(1343928747/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-906296321/5000000000 : ℝ)|^4647 ≤ (2237160520947/20000000000000 : ℝ)^3623
        have hw : |(-906296321/5000000000 : ℝ)|=(906296321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(655642649/1250000000 : ℝ)|^4647 ≤ (43706871248713/100000000000000 : ℝ)^3623
        have hw : |(655642649/1250000000 : ℝ)|=(655642649/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_6 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075143037/2000000000 : ℝ)*x 0 + (5245140933/10000000000 : ℝ)*x 1 + (-906296363/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075143037/2000000000 : ℝ)^4647 ≤ (11276832060641/25000000000000 : ℝ)^3623 := by
    have hnat : (1075143037 : ℕ)^4647*25000000000000^3623 ≤ 11276832060641^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075143037 2000000000 11276832060641 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5245140933/10000000000 : ℝ)^4647 ≤ (21853434240259/50000000000000 : ℝ)^3623 := by
    have hnat : (5245140933 : ℕ)^4647*50000000000000^3623 ≤ 21853434240259^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5245140933 10000000000 21853434240259 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (906296363/5000000000 : ℝ)^4647 ≤ (5592901634813/50000000000000 : ℝ)^3623 := by
    have hnat : (906296363 : ℕ)^4647*50000000000000^3623 ≤ 5592901634813^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      906296363 5000000000 5592901634813 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075143037/2000000000 : ℝ), (5245140933/10000000000 : ℝ), (-906296363/5000000000 : ℝ)] ![(11276832060641/25000000000000 : ℝ), (21853434240259/50000000000000 : ℝ), (5592901634813/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075143037/2000000000 : ℝ)|^4647 ≤ (11276832060641/25000000000000 : ℝ)^3623
        have hw : |(1075143037/2000000000 : ℝ)|=(1075143037/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5245140933/10000000000 : ℝ)|^4647 ≤ (21853434240259/50000000000000 : ℝ)^3623
        have hw : |(5245140933/10000000000 : ℝ)|=(5245140933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-906296363/5000000000 : ℝ)|^4647 ≤ (5592901634813/50000000000000 : ℝ)^3623
        have hw : |(-906296363/5000000000 : ℝ)|=(906296363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_7 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4038096631/10000000000 : ℝ)*x 0 + (4349396013/10000000000 : ℝ)*x 1 + (543674511/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4038096631/10000000000 : ℝ)^4647 ≤ (31251222068853/100000000000000 : ℝ)^3623 := by
    have hnat : (4038096631 : ℕ)^4647*100000000000000^3623 ≤ 31251222068853^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4038096631 10000000000 31251222068853 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4349396013/10000000000 : ℝ)^4647 ≤ (8593597145049/25000000000000 : ℝ)^3623 := by
    have hnat : (4349396013 : ℕ)^4647*25000000000000^3623 ≤ 8593597145049^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4349396013 10000000000 8593597145049 25000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (543674511/1250000000 : ℝ)^4647 ≤ (34374389340473/100000000000000 : ℝ)^3623 := by
    have hnat : (543674511 : ℕ)^4647*100000000000000^3623 ≤ 34374389340473^3623*1250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      543674511 1250000000 34374389340473 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4038096631/10000000000 : ℝ), (4349396013/10000000000 : ℝ), (543674511/1250000000 : ℝ)] ![(31251222068853/100000000000000 : ℝ), (8593597145049/25000000000000 : ℝ), (34374389340473/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4038096631/10000000000 : ℝ)|^4647 ≤ (31251222068853/100000000000000 : ℝ)^3623
        have hw : |(4038096631/10000000000 : ℝ)|=(4038096631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4349396013/10000000000 : ℝ)|^4647 ≤ (8593597145049/25000000000000 : ℝ)^3623
        have hw : |(4349396013/10000000000 : ℝ)|=(4349396013/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(543674511/1250000000 : ℝ)|^4647 ≤ (34374389340473/100000000000000 : ℝ)^3623
        have hw : |(543674511/1250000000 : ℝ)|=(543674511/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_8 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1899974931/10000000000 : ℝ)*x 0 + (5138763807/10000000000 : ℝ)*x 1 + (5416309497/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1899974931/10000000000 : ℝ)^4647 ≤ (11882124773543/100000000000000 : ℝ)^3623 := by
    have hnat : (1899974931 : ℕ)^4647*100000000000000^3623 ≤ 11882124773543^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1899974931 10000000000 11882124773543 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5138763807/10000000000 : ℝ)^4647 ≤ (42573183244667/100000000000000 : ℝ)^3623 := by
    have hnat : (5138763807 : ℕ)^4647*100000000000000^3623 ≤ 42573183244667^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5138763807 10000000000 42573183244667 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416309497/10000000000 : ℝ)^4647 ≤ (2846543247943/6250000000000 : ℝ)^3623 := by
    have hnat : (5416309497 : ℕ)^4647*6250000000000^3623 ≤ 2846543247943^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416309497 10000000000 2846543247943 6250000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1899974931/10000000000 : ℝ), (5138763807/10000000000 : ℝ), (5416309497/10000000000 : ℝ)] ![(11882124773543/100000000000000 : ℝ), (42573183244667/100000000000000 : ℝ), (2846543247943/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1899974931/10000000000 : ℝ)|^4647 ≤ (11882124773543/100000000000000 : ℝ)^3623
        have hw : |(-1899974931/10000000000 : ℝ)|=(1899974931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5138763807/10000000000 : ℝ)|^4647 ≤ (42573183244667/100000000000000 : ℝ)^3623
        have hw : |(5138763807/10000000000 : ℝ)|=(5138763807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416309497/10000000000 : ℝ)|^4647 ≤ (2846543247943/6250000000000 : ℝ)^3623
        have hw : |(5416309497/10000000000 : ℝ)|=(5416309497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_9 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2628552907/5000000000 : ℝ)*x 0 + (-1740770177/10000000000 : ℝ)*x 1 + (5416309711/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2628552907/5000000000 : ℝ)^4647 ≤ (21917395227693/50000000000000 : ℝ)^3623 := by
    have hnat : (2628552907 : ℕ)^4647*50000000000000^3623 ≤ 21917395227693^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2628552907 5000000000 21917395227693 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1740770177/10000000000 : ℝ)^4647 ≤ (2124103049751/20000000000000 : ℝ)^3623 := by
    have hnat : (1740770177 : ℕ)^4647*20000000000000^3623 ≤ 2124103049751^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1740770177 10000000000 2124103049751 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416309711/10000000000 : ℝ)^4647 ≤ (5693086784397/12500000000000 : ℝ)^3623 := by
    have hnat : (5416309711 : ℕ)^4647*12500000000000^3623 ≤ 5693086784397^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416309711 10000000000 5693086784397 12500000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2628552907/5000000000 : ℝ), (-1740770177/10000000000 : ℝ), (5416309711/10000000000 : ℝ)] ![(21917395227693/50000000000000 : ℝ), (2124103049751/20000000000000 : ℝ), (5693086784397/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2628552907/5000000000 : ℝ)|^4647 ≤ (21917395227693/50000000000000 : ℝ)^3623
        have hw : |(2628552907/5000000000 : ℝ)|=(2628552907/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1740770177/10000000000 : ℝ)|^4647 ≤ (2124103049751/20000000000000 : ℝ)^3623
        have hw : |(-1740770177/10000000000 : ℝ)|=(1740770177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416309711/10000000000 : ℝ)|^4647 ≤ (5693086784397/12500000000000 : ℝ)^3623
        have hw : |(5416309711/10000000000 : ℝ)|=(5416309711/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_10 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (105142107/200000000 : ℝ)*x 0 + (42314921/78125000 : ℝ)*x 1 + (-217596321/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (105142107/200000000 : ℝ)^4647 ≤ (8766957098591/20000000000000 : ℝ)^3623 := by
    have hnat : (105142107 : ℕ)^4647*20000000000000^3623 ≤ 8766957098591^3623*200000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      105142107 200000000 8766957098591 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (42314921/78125000 : ℝ)^4647 ≤ (22772348092101/50000000000000 : ℝ)^3623 := by
    have hnat : (42314921 : ℕ)^4647*50000000000000^3623 ≤ 22772348092101^3623*78125000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42314921 78125000 22772348092101 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (217596321/1250000000 : ℝ)^4647 ≤ (10620518308501/100000000000000 : ℝ)^3623 := by
    have hnat : (217596321 : ℕ)^4647*100000000000000^3623 ≤ 10620518308501^3623*1250000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      217596321 1250000000 10620518308501 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(105142107/200000000 : ℝ), (42314921/78125000 : ℝ), (-217596321/1250000000 : ℝ)] ![(8766957098591/20000000000000 : ℝ), (22772348092101/50000000000000 : ℝ), (10620518308501/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(105142107/200000000 : ℝ)|^4647 ≤ (8766957098591/20000000000000 : ℝ)^3623
        have hw : |(105142107/200000000 : ℝ)|=(105142107/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(42314921/78125000 : ℝ)|^4647 ≤ (22772348092101/50000000000000 : ℝ)^3623
        have hw : |(42314921/78125000 : ℝ)|=(42314921/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-217596321/1250000000 : ℝ)|^4647 ≤ (10620518308501/100000000000000 : ℝ)^3623
        have hw : |(-217596321/1250000000 : ℝ)|=(217596321/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_11 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4494846491/10000000000 : ℝ)*x 0 + (2060279267/5000000000 : ℝ)*x 1 + (164822371/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4494846491/10000000000 : ℝ)^4647 ≤ (717114727091/2000000000000 : ℝ)^3623 := by
    have hnat : (4494846491 : ℕ)^4647*2000000000000^3623 ≤ 717114727091^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4494846491 10000000000 717114727091 2000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2060279267/5000000000 : ℝ)^4647 ≤ (32072128118509/100000000000000 : ℝ)^3623 := by
    have hnat : (2060279267 : ℕ)^4647*100000000000000^3623 ≤ 32072128118509^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2060279267 5000000000 32072128118509 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164822371/400000000 : ℝ)^4647 ≤ (32072135516167/100000000000000 : ℝ)^3623 := by
    have hnat : (164822371 : ℕ)^4647*100000000000000^3623 ≤ 32072135516167^3623*400000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164822371 400000000 32072135516167 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4494846491/10000000000 : ℝ), (2060279267/5000000000 : ℝ), (164822371/400000000 : ℝ)] ![(717114727091/2000000000000 : ℝ), (32072128118509/100000000000000 : ℝ), (32072135516167/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4494846491/10000000000 : ℝ)|^4647 ≤ (717114727091/2000000000000 : ℝ)^3623
        have hw : |(4494846491/10000000000 : ℝ)|=(4494846491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2060279267/5000000000 : ℝ)|^4647 ≤ (32072128118509/100000000000000 : ℝ)^3623
        have hw : |(2060279267/5000000000 : ℝ)|=(2060279267/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164822371/400000000 : ℝ)|^4647 ≤ (32072135516167/100000000000000 : ℝ)^3623
        have hw : |(164822371/400000000 : ℝ)|=(164822371/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_12 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-103916549/625000000 : ℝ)*x 0 + (5499204881/10000000000 : ℝ)*x 1 + (1046018427/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (103916549/625000000 : ℝ)^4647 ≤ (5006612250919/50000000000000 : ℝ)^3623 := by
    have hnat : (103916549 : ℕ)^4647*50000000000000^3623 ≤ 5006612250919^3623*625000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103916549 625000000 5006612250919 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5499204881/10000000000 : ℝ)^4647 ≤ (46440683444591/100000000000000 : ℝ)^3623 := by
    have hnat : (5499204881 : ℕ)^4647*100000000000000^3623 ≤ 46440683444591^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499204881 10000000000 46440683444591 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1046018427/2000000000 : ℝ)^4647 ≤ (8709218406077/20000000000000 : ℝ)^3623 := by
    have hnat : (1046018427 : ℕ)^4647*20000000000000^3623 ≤ 8709218406077^3623*2000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1046018427 2000000000 8709218406077 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-103916549/625000000 : ℝ), (5499204881/10000000000 : ℝ), (1046018427/2000000000 : ℝ)] ![(5006612250919/50000000000000 : ℝ), (46440683444591/100000000000000 : ℝ), (8709218406077/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-103916549/625000000 : ℝ)|^4647 ≤ (5006612250919/50000000000000 : ℝ)^3623
        have hw : |(-103916549/625000000 : ℝ)|=(103916549/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5499204881/10000000000 : ℝ)|^4647 ≤ (46440683444591/100000000000000 : ℝ)^3623
        have hw : |(5499204881/10000000000 : ℝ)|=(5499204881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1046018427/2000000000 : ℝ)|^4647 ≤ (8709218406077/20000000000000 : ℝ)^3623
        have hw : |(1046018427/2000000000 : ℝ)|=(1046018427/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_13 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386145347/10000000000 : ℝ)*x 0 + (-1818717171/10000000000 : ℝ)*x 1 + (1307522803/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386145347/10000000000 : ℝ)^4647 ≤ (45219614150367/100000000000000 : ℝ)^3623 := by
    have hnat : (5386145347 : ℕ)^4647*100000000000000^3623 ≤ 45219614150367^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386145347 10000000000 45219614150367 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1818717171/10000000000 : ℝ)^4647 ≤ (11234303653699/100000000000000 : ℝ)^3623 := by
    have hnat : (1818717171 : ℕ)^4647*100000000000000^3623 ≤ 11234303653699^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1818717171 10000000000 11234303653699 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1307522803/2500000000 : ℝ)^4647 ≤ (544326027167/1250000000000 : ℝ)^3623 := by
    have hnat : (1307522803 : ℕ)^4647*1250000000000^3623 ≤ 544326027167^3623*2500000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1307522803 2500000000 544326027167 1250000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386145347/10000000000 : ℝ), (-1818717171/10000000000 : ℝ), (1307522803/2500000000 : ℝ)] ![(45219614150367/100000000000000 : ℝ), (11234303653699/100000000000000 : ℝ), (544326027167/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386145347/10000000000 : ℝ)|^4647 ≤ (45219614150367/100000000000000 : ℝ)^3623
        have hw : |(5386145347/10000000000 : ℝ)|=(5386145347/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1818717171/10000000000 : ℝ)|^4647 ≤ (11234303653699/100000000000000 : ℝ)^3623
        have hw : |(-1818717171/10000000000 : ℝ)|=(1818717171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1307522803/2500000000 : ℝ)|^4647 ≤ (544326027167/1250000000000 : ℝ)^3623
        have hw : |(1307522803/2500000000 : ℝ)|=(1307522803/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_14 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5386146247/10000000000 : ℝ)*x 0 + (5230090201/10000000000 : ℝ)*x 1 + (-181871731/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5386146247/10000000000 : ℝ)^4647 ≤ (4521962384197/10000000000000 : ℝ)^3623 := by
    have hnat : (5386146247 : ℕ)^4647*10000000000000^3623 ≤ 4521962384197^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5386146247 10000000000 4521962384197 10000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5230090201/10000000000 : ℝ)^4647 ≤ (21773035688277/50000000000000 : ℝ)^3623 := by
    have hnat : (5230090201 : ℕ)^4647*50000000000000^3623 ≤ 21773035688277^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5230090201 10000000000 21773035688277 50000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181871731/1000000000 : ℝ)^4647 ≤ (2246860950997/20000000000000 : ℝ)^3623 := by
    have hnat : (181871731 : ℕ)^4647*20000000000000^3623 ≤ 2246860950997^3623*1000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181871731 1000000000 2246860950997 20000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5386146247/10000000000 : ℝ), (5230090201/10000000000 : ℝ), (-181871731/1000000000 : ℝ)] ![(4521962384197/10000000000000 : ℝ), (21773035688277/50000000000000 : ℝ), (2246860950997/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5386146247/10000000000 : ℝ)|^4647 ≤ (4521962384197/10000000000000 : ℝ)^3623
        have hw : |(5386146247/10000000000 : ℝ)|=(5386146247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5230090201/10000000000 : ℝ)|^4647 ≤ (21773035688277/50000000000000 : ℝ)^3623
        have hw : |(5230090201/10000000000 : ℝ)|=(5230090201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-181871731/1000000000 : ℝ)|^4647 ≤ (2246860950997/20000000000000 : ℝ)^3623
        have hw : |(-181871731/1000000000 : ℝ)|=(181871731/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1575_box_15 (p : ℝ) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1998486937/5000000000 : ℝ)*x 0 + (4369487721/10000000000 : ℝ)*x 1 + (4369488677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1998486937/5000000000 : ℝ)^4647 ≤ (30843607346141/100000000000000 : ℝ)^3623 := by
    have hnat : (1998486937 : ℕ)^4647*100000000000000^3623 ≤ 30843607346141^3623*5000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1998486937 5000000000 30843607346141 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4369487721/10000000000 : ℝ)^4647 ≤ (1080568483397/3125000000000 : ℝ)^3623 := by
    have hnat : (4369487721 : ℕ)^4647*3125000000000^3623 ≤ 1080568483397^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369487721 10000000000 1080568483397 3125000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4369488677/10000000000 : ℝ)^4647 ≤ (34578201172329/100000000000000 : ℝ)^3623 := by
    have hnat : (4369488677 : ℕ)^4647*100000000000000^3623 ≤ 34578201172329^3623*10000000000^4647 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4369488677 10000000000 34578201172329 100000000000000 4647 3623 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4647/1024 : ℝ)) 4647 3623 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1998486937/5000000000 : ℝ), (4369487721/10000000000 : ℝ), (4369488677/10000000000 : ℝ)] ![(30843607346141/100000000000000 : ℝ), (1080568483397/3125000000000 : ℝ), (34578201172329/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1998486937/5000000000 : ℝ)|^4647 ≤ (30843607346141/100000000000000 : ℝ)^3623
        have hw : |(1998486937/5000000000 : ℝ)|=(1998486937/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4369487721/10000000000 : ℝ)|^4647 ≤ (1080568483397/3125000000000 : ℝ)^3623
        have hw : |(4369487721/10000000000 : ℝ)|=(4369487721/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4369488677/10000000000 : ℝ)|^4647 ≤ (34578201172329/100000000000000 : ℝ)^3623
        have hw : |(4369488677/10000000000 : ℝ)|=(4369488677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1575_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h) :
    -(63837/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(29463/50000 : ℝ) ∧ (8097/10000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (86397/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5569/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5569/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5569/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3871/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5569/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5569/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3871/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5569/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5569/50000 : ℝ) ^ (4645/1024 : ℝ) ≤ (593063146998947/12500000000000000000 : ℝ) := by
    have hpowers : (5569/50000 : ℝ)^4645 ≤ (593063146998947/12500000000000000000 : ℝ)^1024 := by
      have hnat : (5569 : ℕ)^4645*12500000000000000000^1024 ≤ 593063146998947^1024*50000^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5569 50000 593063146998947 12500000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5569/50000 : ℝ)) (X := (593063146998947/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3871/25000 : ℝ) ^ (4645/1024 : ℝ) ≤ (10572372015202783/50000000000000000000 : ℝ) := by
    have hpowers : (3871/25000 : ℝ)^4645 ≤ (10572372015202783/50000000000000000000 : ℝ)^1024 := by
      have hnat : (3871 : ℕ)^4645*50000000000000000000^1024 ≤ 10572372015202783^1024*25000^4645 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3871 25000 10572372015202783 50000000000000000000 4645 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3871/25000 : ℝ)) (X := (10572372015202783/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (6250593063146998947/6250000000000000000 : ℝ) ≤ (2500052294872121/2500000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (6250593063146998947/6250000000000000000 : ℝ)^1024 ≤ (2500052294872121/2500000000000000 : ℝ)^4645 := by
      have hnat : (6250593063146998947 : ℕ)^1024*2500000000000000^4645 ≤ 2500052294872121^4645*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6250593063146998947 6250000000000000000 2500052294872121 2500000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500052294872121/2500000000000000 : ℝ)) (X := (6250593063146998947/6250000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50012944624603198571/50000000000000000000 : ℝ) ≤ (10000570676349329/10000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (50012944624603198571/50000000000000000000 : ℝ)^1024 ≤ (10000570676349329/10000000000000000 : ℝ)^4645 := by
      have hnat : (50012944624603198571 : ℕ)^1024*10000000000000000^4645 ≤ 10000570676349329^4645*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50012944624603198571 50000000000000000000 10000570676349329 10000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000570676349329/10000000000000000 : ℝ)) (X := (50012944624603198571/50000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25010572372015202783/25000000000000000000 : ℝ) ≤ (5000466086605087/5000000000000000 : ℝ) ^ (4645/1024 : ℝ) := by
    have hpowers : (25010572372015202783/25000000000000000000 : ℝ)^1024 ≤ (5000466086605087/5000000000000000 : ℝ)^4645 := by
      have hnat : (25010572372015202783 : ℕ)^1024*5000000000000000^4645 ≤ 5000466086605087^4645*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25010572372015202783 25000000000000000000 5000466086605087 5000000000000000 1024 4645 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000466086605087/5000000000000000 : ℝ)) (X := (25010572372015202783/25000000000000000000 : ℝ)) (by norm_num) 4645 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(593063146998947/12500000000000000000 : ℝ) ≤ ((10863214097496192061/10865000000000000000 : ℝ)+2*(72299372169/86920000000000 : ℝ)*(5569/50000 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (10863214097496192061/10865000000000000000 : ℝ)+2*(72299372169/86920000000000 : ℝ)*(5569/50000 : ℝ)=(2500052294872121/2500000000000000 : ℝ) by norm_num, show 1+2*(593063146998947/12500000000000000000 : ℝ)=(6250593063146998947/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(10572372015202783/50000000000000000000 : ℝ)+(593063146998947/12500000000000000000 : ℝ) ≤ ((10863214097496192061/10865000000000000000 : ℝ)+(72299372169/86920000000000 : ℝ)*((3871/25000 : ℝ)+(5569/50000 : ℝ)))^(4645/1024 : ℝ) := by
    rw [show (10863214097496192061/10865000000000000000 : ℝ)+(72299372169/86920000000000 : ℝ)*((3871/25000 : ℝ)+(5569/50000 : ℝ))=(10000570676349329/10000000000000000 : ℝ) by norm_num, show 1+(10572372015202783/50000000000000000000 : ℝ)+(593063146998947/12500000000000000000 : ℝ)=(50012944624603198571/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(10572372015202783/50000000000000000000 : ℝ) ≤ ((10863214097496192061/10865000000000000000 : ℝ)+2*(72299372169/86920000000000 : ℝ)*(3871/25000 : ℝ))^(4645/1024 : ℝ) := by
    rw [show (10863214097496192061/10865000000000000000 : ℝ)+2*(72299372169/86920000000000 : ℝ)*(3871/25000 : ℝ)=(5000466086605087/5000000000000000 : ℝ) by norm_num, show 1+2*(10572372015202783/50000000000000000000 : ℝ)=(25010572372015202783/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (10863214097496192061/10865000000000000000 : ℝ)*(X 1 0+X 2 0)+(72299372169/86920000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (10863214097496192061/10865000000000000000 : ℝ)) (alpha := (72299372169/86920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (10863214097496192061/10865000000000000000 : ℝ)*(X 0 1+X 2 1)+(72299372169/86920000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (10863214097496192061/10865000000000000000 : ℝ)) (alpha := (72299372169/86920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (10863214097496192061/10865000000000000000 : ℝ)*(X 0 2+X 1 2)+(72299372169/86920000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4645/1024 : ℝ)) (lo := (5569/50000 : ℝ)) (hi := (3871/25000 : ℝ)) (c := (10863214097496192061/10865000000000000000 : ℝ)) (alpha := (72299372169/86920000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-787901447/5000000000 : ℝ)*X 0 0+(5396055867/10000000000 : ℝ)*X 0 1+(2698028049/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1054228639/2000000000 : ℝ)*X 1 0+(-87473613/500000000 : ℝ)*X 1 1+(107921119/200000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1054228643/2000000000 : ℝ)*X 2 0+(215842233/400000000 : ℝ)*X 2 1+(-349894481/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((555226283/1250000000 : ℝ)*X 0 0+(1036916529/2500000000 : ℝ)*X 0 1+(4147666127/10000000000 : ℝ)*X 0 2+(555226283/1250000000 : ℝ)*X 1 0+(1036916529/2500000000 : ℝ)*X 1 1+(4147666127/10000000000 : ℝ)*X 1 2+(555226283/1250000000 : ℝ)*X 2 0+(1036916529/2500000000 : ℝ)*X 2 1+(4147666127/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1987197079/10000000000 : ℝ)*X 0 0+(262257051/500000000 : ℝ)*X 0 1+(2622570599/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1343928747/2500000000 : ℝ)*X 1 0+(-906296321/5000000000 : ℝ)*X 1 1+(655642649/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1075143037/2000000000 : ℝ)*X 2 0+(5245140933/10000000000 : ℝ)*X 2 1+(-906296363/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4038096631/10000000000 : ℝ)*X 0 0+(4349396013/10000000000 : ℝ)*X 0 1+(543674511/1250000000 : ℝ)*X 0 2+(4038096631/10000000000 : ℝ)*X 1 0+(4349396013/10000000000 : ℝ)*X 1 1+(543674511/1250000000 : ℝ)*X 1 2+(4038096631/10000000000 : ℝ)*X 2 0+(4349396013/10000000000 : ℝ)*X 2 1+(543674511/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-1899974931/10000000000 : ℝ)*X 0 0+(5138763807/10000000000 : ℝ)*X 0 1+(5416309497/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2628552907/5000000000 : ℝ)*X 1 0+(-1740770177/10000000000 : ℝ)*X 1 1+(5416309711/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((105142107/200000000 : ℝ)*X 2 0+(42314921/78125000 : ℝ)*X 2 1+(-217596321/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4494846491/10000000000 : ℝ)*X 0 0+(2060279267/5000000000 : ℝ)*X 0 1+(164822371/400000000 : ℝ)*X 0 2+(4494846491/10000000000 : ℝ)*X 1 0+(2060279267/5000000000 : ℝ)*X 1 1+(164822371/400000000 : ℝ)*X 1 2+(4494846491/10000000000 : ℝ)*X 2 0+(2060279267/5000000000 : ℝ)*X 2 1+(164822371/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-103916549/625000000 : ℝ)*X 0 0+(5499204881/10000000000 : ℝ)*X 0 1+(1046018427/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((5386145347/10000000000 : ℝ)*X 1 0+(-1818717171/10000000000 : ℝ)*X 1 1+(1307522803/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5386146247/10000000000 : ℝ)*X 2 0+(5230090201/10000000000 : ℝ)*X 2 1+(-181871731/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((1998486937/5000000000 : ℝ)*X 0 0+(4369487721/10000000000 : ℝ)*X 0 1+(4369488677/10000000000 : ℝ)*X 0 2+(1998486937/5000000000 : ℝ)*X 1 0+(4369487721/10000000000 : ℝ)*X 1 1+(4369488677/10000000000 : ℝ)*X 1 2+(1998486937/5000000000 : ℝ)*X 2 0+(4369487721/10000000000 : ℝ)*X 2 1+(4369488677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1575_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-63837/100000 : ℝ) ≤ (-2709247317369160883875653985959/4244140625000000000000000000000 : ℝ) := by norm_num
    linear_combination (7498467/50000000000000 : ℝ)*(upper0) + (44630371/100000000000000 : ℝ)*(upper1) + (8573767/50000000000000 : ℝ)*(upper2) + (4266431/10000000000000 : ℝ)*(upper3) + (13049467/12500000000000 : ℝ)*(upper5) + (72342637273217/3125000000000 : ℝ)*(major0) + (72342637273217/3125000000000 : ℝ)*(major1) + (72342637273217/3125000000000 : ℝ)*(major2) + (3906397687/50000000000000 : ℝ)*(sp2) + (636026417/50000000000000 : ℝ)*(sp3) + (409596487184383/12500000000000 : ℝ)*(sp4) + (409596487184383/12500000000000 : ℝ)*(sp5) + (327676408467969/10000000000000 : ℝ)*(sp6) + (1374433950464701/100000000000000 : ℝ)*(sp7) + (274887044503507/20000000000000 : ℝ)*(f.failure) + (409596487184383/12500000000000 : ℝ)*(f.sum) + (33324894651/434600000000000000000000000 : ℝ)*base66 + (598449226949227/132629394531250000000000000000 : ℝ)*base67 + (164910204577236487/33953125000000000000000000000000 : ℝ)*base69 + (16921271529764569/16976562500000000000000000000000 : ℝ)*base72 + (3663378601731/2173000000000000000000000000 : ℝ)*base73 + (890992702771486487/33953125000000000000000000000000 : ℝ)*base75 + (22634238398858319/16976562500000000000000000000000 : ℝ)*base78 + (10087486660359441/1061035156250000000000000000000 : ℝ)*base79 + (2051544379743/108650000000000000000000000 : ℝ)*base81 + (4686897/2000000000000000000000 : ℝ)*base90 + (4686897/2000000000000000000000 : ℝ)*base92 + (4686897/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (29463/50000 : ℝ) ≤ (80032834877594330528256539870277/135812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2963219/20000000000000 : ℝ)*(lower1) + (18128529/100000000000000 : ℝ)*(lower4) + (23310987/50000000000000 : ℝ)*(lower5) + (1197770209661619/50000000000000 : ℝ)*(major0) + (1197770209661619/50000000000000 : ℝ)*(major1) + (1197770209661619/50000000000000 : ℝ)*(major2) + (3349158301262001/100000000000000 : ℝ)*(sp0) + (1674581037767301/50000000000000 : ℝ)*(sp1) + (1674577091817769/50000000000000 : ℝ)*(sp2) + (355568350338397/25000000000000 : ℝ)*(sp3) + (579561293/50000000000000 : ℝ)*(sp5) + (1230430733/100000000000000 : ℝ)*(sp7) + (9051021649/100000000000000 : ℝ)*(sp10) + (986679037/20000000000000 : ℝ)*(sp12) + (1422274631784321/100000000000000 : ℝ)*(f.failure) + (3349163234657187/100000000000000 : ℝ)*(f.sum) + (4782750777289/1086500000000000000000000000 : ℝ)*base65 + (357688522678668241/543250000000000000000000000000000 : ℝ)*base68 + (3884230935603331759/543250000000000000000000000000000 : ℝ)*base69 + (128459037341668241/543250000000000000000000000000000 : ℝ)*base72 + (2650698888127/1086500000000000000000000000 : ℝ)*base74 + (3423591065058418241/543250000000000000000000000000000 : ℝ)*base76 + (1365137491323168241/543250000000000000000000000000000 : ℝ)*base78 + (2111607170586168241/543250000000000000000000000000000 : ℝ)*base80 + (754594438223/2173000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base85 + (64639509/10000000000000000000000 : ℝ)*base89 + (64639509/10000000000000000000000 : ℝ)*base91 + (64639509/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (8097/10000 : ℝ) ≤ (21994123243774433706984874401909/27162500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (74552877/100000000000000 : ℝ)*(lower1) + (8818301/5000000000000 : ℝ)*(upper2) + (6431729/50000000000000 : ℝ)*(lower3) + (2725947/2500000000000 : ℝ)*(lower5) + (129063421863859/5000000000000 : ℝ)*(major0) + (129063421863859/5000000000000 : ℝ)*(major1) + (129063421863859/5000000000000 : ℝ)*(major2) + (7610838779/100000000000000 : ℝ)*(sp1) + (1066309911/100000000000000 : ℝ)*(sp2) + (11998426437/100000000000000 : ℝ)*(sp3) + (1801500723078671/50000000000000 : ℝ)*(sp8) + (3602993835318563/100000000000000 : ℝ)*(sp9) + (3603000379847431/100000000000000 : ℝ)*(sp10) + (766266317995701/50000000000000 : ℝ)*(sp11) + (1532544634417839/100000000000000 : ℝ)*(f.failure) + (1801500723078671/50000000000000 : ℝ)*(f.sum) + (4378116373753/1086500000000000000000000000 : ℝ)*base65 + (238613440898948399/54325000000000000000000000000000 : ℝ)*base67 + (826525345180523399/54325000000000000000000000000000 : ℝ)*base69 + (543547837302473399/54325000000000000000000000000000 : ℝ)*base71 + (1995208056527/2173000000000000000000000000 : ℝ)*base74 + (292061144409598399/54325000000000000000000000000000 : ℝ)*base75 + (549448861743873399/54325000000000000000000000000000 : ℝ)*base77 + (528352660762523399/54325000000000000000000000000000 : ℝ)*base79 + (966862644029/271625000000000000000000000 : ℝ)*base81 + (95544869/10000000000000000000000 : ℝ)*base90 + (95544869/10000000000000000000000 : ℝ)*base92 + (95544869/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-86397/100000 : ℝ) ≤ (-469337692426799911108911445207029/543250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (89859559/50000000000000 : ℝ)*(lower0) + (36697277/10000000000000 : ℝ)*(lower1) + (22496951/20000000000000 : ℝ)*(lower2) + (40208517/100000000000000 : ℝ)*(lower3) + (2621891638217521/100000000000000 : ℝ)*(major0) + (2621891638217521/100000000000000 : ℝ)*(major1) + (2621891638217521/100000000000000 : ℝ)*(major2) + (111253219383/25000000000000 : ℝ)*(sp5) + (657758796081/100000000000000 : ℝ)*(sp6) + (11515840923/25000000000000 : ℝ)*(sp7) + (3715918070913783/100000000000000 : ℝ)*(sp12) + (3715473058036251/100000000000000 : ℝ)*(sp13) + (1857630156058851/50000000000000 : ℝ)*(sp14) + (778308641256009/50000000000000 : ℝ)*(sp15) + (155666334587571/10000000000000 : ℝ)*(f.failure) + (3715918070913783/100000000000000 : ℝ)*(f.sum) + (5821255518103/4346000000000000000000000000 : ℝ)*base66 + (14989286813301925781/1086500000000000000000000000000000 : ℝ)*base67 + (4550425162166925781/1086500000000000000000000000000000 : ℝ)*base69 + (7221792596851925781/1086500000000000000000000000000000 : ℝ)*base71 + (1615873513813/869200000000000000000000000 : ℝ)*base74 + (7651700719355425781/1086500000000000000000000000000000 : ℝ)*base75 + (3812430928242925781/1086500000000000000000000000000000 : ℝ)*base77 + (14513240258603925781/1086500000000000000000000000000000 : ℝ)*base79 + (5886911165927/4346000000000000000000000000 : ℝ)*base82 + (5916241/1000000000000000000000 : ℝ)*base90 + (5916241/1000000000000000000000 : ℝ)*base92 + (5916241/1000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1575_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5569/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63837/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29463/50000 : ℝ) else (8097/10000 : ℝ) ≤ X j i ∧ X j i ≤ (86397/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1575_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1575_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63837/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29463/50000 : ℝ) else (8097/10000 : ℝ) ≤ X j i ∧ X j i ≤ (86397/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1575_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1575_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  exact h1
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4645/1024 : ℝ) ≤ p) (hpb : p ≤ (4647/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (168430229/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3871/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11137/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(63837/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(29463/50000 : ℝ) else (8097/10000 : ℝ) ≤ X j i ∧ X j i ≤ (86397/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1575_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
