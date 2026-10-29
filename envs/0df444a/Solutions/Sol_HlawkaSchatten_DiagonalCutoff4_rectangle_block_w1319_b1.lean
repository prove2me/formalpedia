-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1319_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:42:56.779823+00:00
-- url     : https://prove2.me/submissions/813ccccb-e175-4158-933d-15fd98fae55c

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
theorem support_rectangle_w1319_s3_0 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-257749743/1250000000 : ℝ)*x 0 + (5430214619/10000000000 : ℝ)*x 1 + (5228872393/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (257749743/1250000000 : ℝ)^4279 ≤ (12547816233321/100000000000000 : ℝ)^3255 := by
    have hnat : (257749743 : ℕ)^4279*100000000000000^3255 ≤ 12547816233321^3255*1250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      257749743 1250000000 12547816233321 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5430214619/10000000000 : ℝ)^4279 ≤ (8962358058023/20000000000000 : ℝ)^3255 := by
    have hnat : (5430214619 : ℕ)^4279*20000000000000^3255 ≤ 8962358058023^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5430214619 10000000000 8962358058023 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5228872393/10000000000 : ℝ)^4279 ≤ (2665024591399/6250000000000 : ℝ)^3255 := by
    have hnat : (5228872393 : ℕ)^4279*6250000000000^3255 ≤ 2665024591399^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228872393 10000000000 2665024591399 6250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-257749743/1250000000 : ℝ), (5430214619/10000000000 : ℝ), (5228872393/10000000000 : ℝ)] ![(12547816233321/100000000000000 : ℝ), (8962358058023/20000000000000 : ℝ), (2665024591399/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-257749743/1250000000 : ℝ)|^4279 ≤ (12547816233321/100000000000000 : ℝ)^3255
        have hw : |(-257749743/1250000000 : ℝ)|=(257749743/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5430214619/10000000000 : ℝ)|^4279 ≤ (8962358058023/20000000000000 : ℝ)^3255
        have hw : |(5430214619/10000000000 : ℝ)|=(5430214619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5228872393/10000000000 : ℝ)|^4279 ≤ (2665024591399/6250000000000 : ℝ)^3255
        have hw : |(5228872393/10000000000 : ℝ)|=(5228872393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s3_1 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2676764229/5000000000 : ℝ)*x 0 + (-2164961523/10000000000 : ℝ)*x 1 + (2614436181/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676764229/5000000000 : ℝ)^4279 ≤ (43981720410549/100000000000000 : ℝ)^3255 := by
    have hnat : (2676764229 : ℕ)^4279*100000000000000^3255 ≤ 43981720410549^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676764229 5000000000 43981720410549 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2164961523/10000000000 : ℝ)^4279 ≤ (836117902921/6250000000000 : ℝ)^3255 := by
    have hnat : (2164961523 : ℕ)^4279*6250000000000^3255 ≤ 836117902921^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164961523 10000000000 836117902921 6250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2614436181/5000000000 : ℝ)^4279 ≤ (42640393130057/100000000000000 : ℝ)^3255 := by
    have hnat : (2614436181 : ℕ)^4279*100000000000000^3255 ≤ 42640393130057^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2614436181 5000000000 42640393130057 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676764229/5000000000 : ℝ), (-2164961523/10000000000 : ℝ), (2614436181/5000000000 : ℝ)] ![(43981720410549/100000000000000 : ℝ), (836117902921/6250000000000 : ℝ), (42640393130057/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676764229/5000000000 : ℝ)|^4279 ≤ (43981720410549/100000000000000 : ℝ)^3255
        have hw : |(2676764229/5000000000 : ℝ)|=(2676764229/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2164961523/10000000000 : ℝ)|^4279 ≤ (836117902921/6250000000000 : ℝ)^3255
        have hw : |(-2164961523/10000000000 : ℝ)|=(2164961523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2614436181/5000000000 : ℝ)|^4279 ≤ (42640393130057/100000000000000 : ℝ)^3255
        have hw : |(2614436181/5000000000 : ℝ)|=(2614436181/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s3_2 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (133838213/250000000 : ℝ)*x 0 + (5228872121/10000000000 : ℝ)*x 1 + (-1082480879/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133838213/250000000 : ℝ)^4279 ≤ (10995430270037/25000000000000 : ℝ)^3255 := by
    have hnat : (133838213 : ℕ)^4279*25000000000000^3255 ≤ 10995430270037^3255*250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133838213 250000000 10995430270037 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5228872121/10000000000 : ℝ)^4279 ≤ (533004881831/1250000000000 : ℝ)^3255 := by
    have hnat : (5228872121 : ℕ)^4279*1250000000000^3255 ≤ 533004881831^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5228872121 10000000000 533004881831 1250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1082480879/5000000000 : ℝ)^4279 ≤ (6688944177847/50000000000000 : ℝ)^3255 := by
    have hnat : (1082480879 : ℕ)^4279*50000000000000^3255 ≤ 6688944177847^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1082480879 5000000000 6688944177847 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133838213/250000000 : ℝ), (5228872121/10000000000 : ℝ), (-1082480879/5000000000 : ℝ)] ![(10995430270037/25000000000000 : ℝ), (533004881831/1250000000000 : ℝ), (6688944177847/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133838213/250000000 : ℝ)|^4279 ≤ (10995430270037/25000000000000 : ℝ)^3255
        have hw : |(133838213/250000000 : ℝ)|=(133838213/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5228872121/10000000000 : ℝ)|^4279 ≤ (533004881831/1250000000000 : ℝ)^3255
        have hw : |(5228872121/10000000000 : ℝ)|=(5228872121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1082480879/5000000000 : ℝ)|^4279 ≤ (6688944177847/50000000000000 : ℝ)^3255
        have hw : |(-1082480879/5000000000 : ℝ)|=(1082480879/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s3_3 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4331455163/10000000000 : ℝ)*x 0 + (4127175381/10000000000 : ℝ)*x 1 + (4545254951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4331455163/10000000000 : ℝ)^4279 ≤ (33290582287793/100000000000000 : ℝ)^3255 := by
    have hnat : (4331455163 : ℕ)^4279*100000000000000^3255 ≤ 33290582287793^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4331455163 10000000000 33290582287793 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4127175381/10000000000 : ℝ)^4279 ≤ (7810521976809/25000000000000 : ℝ)^3255 := by
    have hnat : (4127175381 : ℕ)^4279*25000000000000^3255 ≤ 7810521976809^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4127175381 10000000000 7810521976809 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4545254951/10000000000 : ℝ)^4279 ≤ (35467329794061/100000000000000 : ℝ)^3255 := by
    have hnat : (4545254951 : ℕ)^4279*100000000000000^3255 ≤ 35467329794061^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4545254951 10000000000 35467329794061 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4331455163/10000000000 : ℝ), (4127175381/10000000000 : ℝ), (4545254951/10000000000 : ℝ)] ![(33290582287793/100000000000000 : ℝ), (7810521976809/25000000000000 : ℝ), (35467329794061/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4331455163/10000000000 : ℝ)|^4279 ≤ (33290582287793/100000000000000 : ℝ)^3255
        have hw : |(4331455163/10000000000 : ℝ)|=(4331455163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4127175381/10000000000 : ℝ)|^4279 ≤ (7810521976809/25000000000000 : ℝ)^3255
        have hw : |(4127175381/10000000000 : ℝ)|=(4127175381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4545254951/10000000000 : ℝ)|^4279 ≤ (35467329794061/100000000000000 : ℝ)^3255
        have hw : |(4545254951/10000000000 : ℝ)|=(4545254951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s3_4 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1031009311/5000000000 : ℝ)*x 0 + (5229723383/10000000000 : ℝ)*x 1 + (2714679197/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031009311/5000000000 : ℝ)^4279 ≤ (24507776661/195312500000 : ℝ)^3255 := by
    have hnat : (1031009311 : ℕ)^4279*195312500000^3255 ≤ 24507776661^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031009311 5000000000 24507776661 195312500000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5229723383/10000000000 : ℝ)^4279 ≤ (4264951651181/10000000000000 : ℝ)^3255 := by
    have hnat : (5229723383 : ℕ)^4279*10000000000000^3255 ≤ 4264951651181^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5229723383 10000000000 4264951651181 10000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714679197/5000000000 : ℝ)^4279 ≤ (22401250914941/50000000000000 : ℝ)^3255 := by
    have hnat : (2714679197 : ℕ)^4279*50000000000000^3255 ≤ 22401250914941^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714679197 5000000000 22401250914941 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1031009311/5000000000 : ℝ), (5229723383/10000000000 : ℝ), (2714679197/5000000000 : ℝ)] ![(24507776661/195312500000 : ℝ), (4264951651181/10000000000000 : ℝ), (22401250914941/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1031009311/5000000000 : ℝ)|^4279 ≤ (24507776661/195312500000 : ℝ)^3255
        have hw : |(-1031009311/5000000000 : ℝ)|=(1031009311/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5229723383/10000000000 : ℝ)|^4279 ≤ (4264951651181/10000000000000 : ℝ)^3255
        have hw : |(5229723383/10000000000 : ℝ)|=(5229723383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714679197/5000000000 : ℝ)|^4279 ≤ (22401250914941/50000000000000 : ℝ)^3255
        have hw : |(2714679197/5000000000 : ℝ)|=(2714679197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s3_5 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1325451299/2500000000 : ℝ)*x 0 + (-982237747/5000000000 : ℝ)*x 1 + (2714679177/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1325451299/2500000000 : ℝ)^4279 ≤ (8684792093017/20000000000000 : ℝ)^3255 := by
    have hnat : (1325451299 : ℕ)^4279*20000000000000^3255 ≤ 8684792093017^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1325451299 2500000000 8684792093017 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (982237747/5000000000 : ℝ)^4279 ≤ (11773538132499/100000000000000 : ℝ)^3255 := by
    have hnat : (982237747 : ℕ)^4279*100000000000000^3255 ≤ 11773538132499^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      982237747 5000000000 11773538132499 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2714679177/5000000000 : ℝ)^4279 ≤ (22401250697983/50000000000000 : ℝ)^3255 := by
    have hnat : (2714679177 : ℕ)^4279*50000000000000^3255 ≤ 22401250697983^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2714679177 5000000000 22401250697983 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1325451299/2500000000 : ℝ), (-982237747/5000000000 : ℝ), (2714679177/5000000000 : ℝ)] ![(8684792093017/20000000000000 : ℝ), (11773538132499/100000000000000 : ℝ), (22401250697983/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1325451299/2500000000 : ℝ)|^4279 ≤ (8684792093017/20000000000000 : ℝ)^3255
        have hw : |(1325451299/2500000000 : ℝ)|=(1325451299/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-982237747/5000000000 : ℝ)|^4279 ≤ (11773538132499/100000000000000 : ℝ)^3255
        have hw : |(-982237747/5000000000 : ℝ)|=(982237747/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2714679177/5000000000 : ℝ)|^4279 ≤ (22401250697983/50000000000000 : ℝ)^3255
        have hw : |(2714679177/5000000000 : ℝ)|=(2714679177/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s3_6 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (265090267/500000000 : ℝ)*x 0 + (5429358227/10000000000 : ℝ)*x 1 + (-196447547/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265090267/500000000 : ℝ)^4279 ≤ (43423962015541/100000000000000 : ℝ)^3255 := by
    have hnat : (265090267 : ℕ)^4279*100000000000000^3255 ≤ 43423962015541^3255*500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265090267 500000000 43423962015541 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5429358227/10000000000 : ℝ)^4279 ≤ (8960500003657/20000000000000 : ℝ)^3255 := by
    have hnat : (5429358227 : ℕ)^4279*20000000000000^3255 ≤ 8960500003657^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5429358227 10000000000 8960500003657 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (196447547/1000000000 : ℝ)^4279 ≤ (2943384485853/25000000000000 : ℝ)^3255 := by
    have hnat : (196447547 : ℕ)^4279*25000000000000^3255 ≤ 2943384485853^3255*1000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196447547 1000000000 2943384485853 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265090267/500000000 : ℝ), (5429358227/10000000000 : ℝ), (-196447547/1000000000 : ℝ)] ![(43423962015541/100000000000000 : ℝ), (8960500003657/20000000000000 : ℝ), (2943384485853/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265090267/500000000 : ℝ)|^4279 ≤ (43423962015541/100000000000000 : ℝ)^3255
        have hw : |(265090267/500000000 : ℝ)|=(265090267/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5429358227/10000000000 : ℝ)|^4279 ≤ (8960500003657/20000000000000 : ℝ)^3255
        have hw : |(5429358227/10000000000 : ℝ)|=(5429358227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-196447547/1000000000 : ℝ)|^4279 ≤ (2943384485853/25000000000000 : ℝ)^3255
        have hw : |(-196447547/1000000000 : ℝ)|=(196447547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s3_7 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (866299581/2000000000 : ℝ)*x 0 + (4543487737/10000000000 : ℝ)*x 1 + (4128953433/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (866299581/2000000000 : ℝ)^4279 ≤ (33291014139237/100000000000000 : ℝ)^3255 := by
    have hnat : (866299581 : ℕ)^4279*100000000000000^3255 ≤ 33291014139237^3255*2000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      866299581 2000000000 33291014139237 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4543487737/10000000000 : ℝ)^4279 ≤ (8862300717471/25000000000000 : ℝ)^3255 := by
    have hnat : (4543487737 : ℕ)^4279*25000000000000^3255 ≤ 8862300717471^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4543487737 10000000000 8862300717471 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4128953433/10000000000 : ℝ)^4279 ≤ (15629891489/50000000000 : ℝ)^3255 := by
    have hnat : (4128953433 : ℕ)^4279*50000000000^3255 ≤ 15629891489^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4128953433 10000000000 15629891489 50000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(866299581/2000000000 : ℝ), (4543487737/10000000000 : ℝ), (4128953433/10000000000 : ℝ)] ![(33291014139237/100000000000000 : ℝ), (8862300717471/25000000000000 : ℝ), (15629891489/50000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(866299581/2000000000 : ℝ)|^4279 ≤ (33291014139237/100000000000000 : ℝ)^3255
        have hw : |(866299581/2000000000 : ℝ)|=(866299581/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4543487737/10000000000 : ℝ)|^4279 ≤ (8862300717471/25000000000000 : ℝ)^3255
        have hw : |(4543487737/10000000000 : ℝ)|=(4543487737/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4128953433/10000000000 : ℝ)|^4279 ≤ (15629891489/50000000000 : ℝ)^3255
        have hw : |(4128953433/10000000000 : ℝ)|=(4128953433/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1319_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8099/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10773/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (15033/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8099/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9697/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8099/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9697/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8099/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9697/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8099/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9697/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8099/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9697/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8099/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9697/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9697/100000 : ℝ) ^ (2139/512 : ℝ) ≤ (5840368007385761/100000000000000000000 : ℝ) := by
    have hpowers : (9697/100000 : ℝ)^2139 ≤ (5840368007385761/100000000000000000000 : ℝ)^512 := by
      have hnat : (9697 : ℕ)^2139*100000000000000000000^512 ≤ 5840368007385761^512*100000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9697 100000 5840368007385761 100000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9697/100000 : ℝ)) (X := (5840368007385761/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hpowhi : (8099/50000 : ℝ) ^ (2139/512 : ℝ) ≤ (99625310794279/200000000000000000 : ℝ) := by
    have hpowers : (8099/50000 : ℝ)^2139 ≤ (99625310794279/200000000000000000 : ℝ)^512 := by
      have hnat : (8099 : ℕ)^2139*200000000000000000^512 ≤ 99625310794279^512*50000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8099 50000 99625310794279 200000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8099/50000 : ℝ)) (X := (99625310794279/200000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005840368007385761/50000000000000000000 : ℝ) ≤ (2000055916514061/2000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (50005840368007385761/50000000000000000000 : ℝ)^512 ≤ (2000055916514061/2000000000000000 : ℝ)^2139 := by
      have hnat : (50005840368007385761 : ℕ)^512*2000000000000000^2139 ≤ 2000055916514061^2139*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005840368007385761 50000000000000000000 2000055916514061 2000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000055916514061/2000000000000000 : ℝ)) (X := (50005840368007385761/50000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100055653023404525261/100000000000000000000 : ℝ) ≤ (10001331852215229/10000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (100055653023404525261/100000000000000000000 : ℝ)^512 ≤ (10001331852215229/10000000000000000 : ℝ)^2139 := by
      have hnat : (100055653023404525261 : ℕ)^512*10000000000000000^2139 ≤ 10001331852215229^2139*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100055653023404525261 100000000000000000000 10001331852215229 10000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001331852215229/10000000000000000 : ℝ)) (X := (100055653023404525261/100000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (100099625310794279/100000000000000000 : ℝ) ≤ (10002384121860153/10000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (100099625310794279/100000000000000000 : ℝ)^512 ≤ (10002384121860153/10000000000000000 : ℝ)^2139 := by
      have hnat : (100099625310794279 : ℕ)^512*10000000000000000^2139 ≤ 10002384121860153^2139*100000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100099625310794279 100000000000000000 10002384121860153 10000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10002384121860153/10000000000000000 : ℝ)) (X := (100099625310794279/100000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5840368007385761/100000000000000000000 : ℝ) ≤ ((21663803282931965583/21670000000000000000 : ℝ)+2*(87689137077/54175000000000 : ℝ)*(9697/100000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (21663803282931965583/21670000000000000000 : ℝ)+2*(87689137077/54175000000000 : ℝ)*(9697/100000 : ℝ)=(2000055916514061/2000000000000000 : ℝ) by norm_num, show 1+2*(5840368007385761/100000000000000000000 : ℝ)=(50005840368007385761/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(99625310794279/200000000000000000 : ℝ)+(5840368007385761/100000000000000000000 : ℝ) ≤ ((21663803282931965583/21670000000000000000 : ℝ)+(87689137077/54175000000000 : ℝ)*((8099/50000 : ℝ)+(9697/100000 : ℝ)))^(2139/512 : ℝ) := by
    rw [show (21663803282931965583/21670000000000000000 : ℝ)+(87689137077/54175000000000 : ℝ)*((8099/50000 : ℝ)+(9697/100000 : ℝ))=(10001331852215229/10000000000000000 : ℝ) by norm_num, show 1+(99625310794279/200000000000000000 : ℝ)+(5840368007385761/100000000000000000000 : ℝ)=(100055653023404525261/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(99625310794279/200000000000000000 : ℝ) ≤ ((21663803282931965583/21670000000000000000 : ℝ)+2*(87689137077/54175000000000 : ℝ)*(8099/50000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (21663803282931965583/21670000000000000000 : ℝ)+2*(87689137077/54175000000000 : ℝ)*(8099/50000 : ℝ)=(10002384121860153/10000000000000000 : ℝ) by norm_num, show 1+2*(99625310794279/200000000000000000 : ℝ)=(100099625310794279/100000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (21663803282931965583/21670000000000000000 : ℝ)*(X 1 0+X 2 0)+(87689137077/54175000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (9697/100000 : ℝ)) (hi := (8099/50000 : ℝ)) (c := (21663803282931965583/21670000000000000000 : ℝ)) (alpha := (87689137077/54175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (21663803282931965583/21670000000000000000 : ℝ)*(X 0 1+X 2 1)+(87689137077/54175000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (9697/100000 : ℝ)) (hi := (8099/50000 : ℝ)) (c := (21663803282931965583/21670000000000000000 : ℝ)) (alpha := (87689137077/54175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (21663803282931965583/21670000000000000000 : ℝ)*(X 0 2+X 1 2)+(87689137077/54175000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (9697/100000 : ℝ)) (hi := (8099/50000 : ℝ)) (c := (21663803282931965583/21670000000000000000 : ℝ)) (alpha := (87689137077/54175000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-257749743/1250000000 : ℝ)*X 0 0+(5430214619/10000000000 : ℝ)*X 0 1+(5228872393/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2676764229/5000000000 : ℝ)*X 1 0+(-2164961523/10000000000 : ℝ)*X 1 1+(2614436181/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133838213/250000000 : ℝ)*X 2 0+(5228872121/10000000000 : ℝ)*X 2 1+(-1082480879/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4331455163/10000000000 : ℝ)*X 0 0+(4127175381/10000000000 : ℝ)*X 0 1+(4545254951/10000000000 : ℝ)*X 0 2+(4331455163/10000000000 : ℝ)*X 1 0+(4127175381/10000000000 : ℝ)*X 1 1+(4545254951/10000000000 : ℝ)*X 1 2+(4331455163/10000000000 : ℝ)*X 2 0+(4127175381/10000000000 : ℝ)*X 2 1+(4545254951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1031009311/5000000000 : ℝ)*X 0 0+(5229723383/10000000000 : ℝ)*X 0 1+(2714679197/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1325451299/2500000000 : ℝ)*X 1 0+(-982237747/5000000000 : ℝ)*X 1 1+(2714679177/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((265090267/500000000 : ℝ)*X 2 0+(5429358227/10000000000 : ℝ)*X 2 1+(-196447547/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((866299581/2000000000 : ℝ)*X 0 0+(4543487737/10000000000 : ℝ)*X 0 1+(4128953433/10000000000 : ℝ)*X 0 2+(866299581/2000000000 : ℝ)*X 1 0+(4543487737/10000000000 : ℝ)*X 1 1+(4128953433/10000000000 : ℝ)*X 1 2+(866299581/2000000000 : ℝ)*X 2 0+(4543487737/10000000000 : ℝ)*X 2 1+(4128953433/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2292943771668023728811488359/270875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (875658469/50000000000000 : ℝ)*(base19) + (411637719/25000000000000 : ℝ)*(base23) + (86880473/100000000000000 : ℝ)*(lower2) + (374406903/100000000000000 : ℝ)*(upper3) + (15635337/100000000000000 : ℝ)*(upper5) + (919829832684109/25000000000000 : ℝ)*(major0) + (919829832684109/25000000000000 : ℝ)*(major1) + (3679319330736437/100000000000000 : ℝ)*(major2) + (993339896502111/20000000000000 : ℝ)*(sp0) + (155209998929989/3125000000000 : ℝ)*(sp1) + (4966720070525709/100000000000000 : ℝ)*(sp2) + (239190022803063/10000000000000 : ℝ)*(sp3) + (22234566031/100000000000000 : ℝ)*(sp4) + (4108550149/25000000000000 : ℝ)*(sp7) + (1195958331115613/50000000000000 : ℝ)*(f.failure) + (993344343415317/20000000000000 : ℝ)*(f.sum) + (11530959827669/5417500000000000000000000000 : ℝ)*base66 + (3921154930411079453/541750000000000000000000000000000 : ℝ)*base68 + (4246480481347847771/2167000000000000000000000000000000 : ℝ)*base69 + (2475970382909420547/541750000000000000000000000000000 : ℝ)*base71 + (2340396195953/2708750000000000000000000000 : ℝ)*base73 + (28332904495901152229/2167000000000000000000000000000000 : ℝ)*base76 + (642231054043720547/541750000000000000000000000000000 : ℝ)*base77 + (1572710883891970547/541750000000000000000000000000000 : ℝ)*base79 + (8836830551541/1354375000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (12088941/5000000000000000000000 : ℝ)*base89 + (12088941/5000000000000000000000 : ℝ)*base91 + (37911059/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (195953416069947416955875673/54175000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (970129807/100000000000000 : ℝ)*(base19) + (565147557/50000000000000 : ℝ)*(base23) + (2461729/2500000000000 : ℝ)*(upper3) + (3362031/50000000000000 : ℝ)*(lower4) + (52478451/50000000000000 : ℝ)*(upper5) + (185537211624077/5000000000000 : ℝ)*(major0) + (185537211624077/5000000000000 : ℝ)*(major1) + (185537211624077/5000000000000 : ℝ)*(major2) + (810295609/5000000000000 : ℝ)*(sp1) + (17377719933/100000000000000 : ℝ)*(sp2) + (2504571214497897/50000000000000 : ℝ)*(sp4) + (5009125252953807/100000000000000 : ℝ)*(sp5) + (5009123920980747/100000000000000 : ℝ)*(sp6) + (1206172957699553/50000000000000 : ℝ)*(sp7) + (1206172957699553/50000000000000 : ℝ)*(f.failure) + (2504571214497897/50000000000000 : ℝ)*(f.sum) + (1104648861351/216700000000000000000000000 : ℝ)*base65 + (284669328700658109/108350000000000000000000000000000 : ℝ)*base68 + (885942824190841891/108350000000000000000000000000000 : ℝ)*base69 + (434443302544041891/108350000000000000000000000000000 : ℝ)*base71 + (1191083343939/541750000000000000000000000 : ℝ)*base73 + (1396788844825858109/108350000000000000000000000000000 : ℝ)*base76 + (62924210964758109/108350000000000000000000000000000 : ℝ)*base78 + (257830205906658109/108350000000000000000000000000000 : ℝ)*base80 + (6183599057833/1083500000000000000000000000 : ℝ)*base81 + (70006479/5000000000000000000000 : ℝ)*base90 + (70006479/5000000000000000000000 : ℝ)*base92 + (70006479/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1319_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8099/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10773/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (15033/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1319_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1319_s4_0 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-515913887/2500000000 : ℝ)*x 0 + (2708452163/5000000000 : ℝ)*x 1 + (2620547529/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (515913887/2500000000 : ℝ)^4279 ≤ (628053908429/5000000000000 : ℝ)^3255 := by
    have hnat : (515913887 : ℕ)^4279*5000000000000^3255 ≤ 628053908429^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      515913887 2500000000 628053908429 5000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708452163/5000000000 : ℝ)^4279 ≤ (22333725155563/50000000000000 : ℝ)^3255 := by
    have hnat : (2708452163 : ℕ)^4279*50000000000000^3255 ≤ 22333725155563^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708452163 5000000000 22333725155563 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2620547529/5000000000 : ℝ)^4279 ≤ (42771471500299/100000000000000 : ℝ)^3255 := by
    have hnat : (2620547529 : ℕ)^4279*100000000000000^3255 ≤ 42771471500299^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2620547529 5000000000 42771471500299 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-515913887/2500000000 : ℝ), (2708452163/5000000000 : ℝ), (2620547529/5000000000 : ℝ)] ![(628053908429/5000000000000 : ℝ), (22333725155563/50000000000000 : ℝ), (42771471500299/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-515913887/2500000000 : ℝ)|^4279 ≤ (628053908429/5000000000000 : ℝ)^3255
        have hw : |(-515913887/2500000000 : ℝ)|=(515913887/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708452163/5000000000 : ℝ)|^4279 ≤ (22333725155563/50000000000000 : ℝ)^3255
        have hw : |(2708452163/5000000000 : ℝ)|=(2708452163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2620547529/5000000000 : ℝ)|^4279 ≤ (42771471500299/100000000000000 : ℝ)^3255
        have hw : |(2620547529/5000000000 : ℝ)|=(2620547529/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s4_1 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350148937/10000000000 : ℝ)*x 0 + (-215330843/1000000000 : ℝ)*x 1 + (1310273701/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350148937/10000000000 : ℝ)^4279 ≤ (21972612619537/50000000000000 : ℝ)^3255 := by
    have hnat : (5350148937 : ℕ)^4279*50000000000000^3255 ≤ 21972612619537^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350148937 10000000000 21972612619537 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215330843/1000000000 : ℝ)^4279 ≤ (13283305965553/100000000000000 : ℝ)^3255 := by
    have hnat : (215330843 : ℕ)^4279*100000000000000^3255 ≤ 13283305965553^3255*1000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215330843 1000000000 13283305965553 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1310273701/2500000000 : ℝ)^4279 ≤ (42771468775357/100000000000000 : ℝ)^3255 := by
    have hnat : (1310273701 : ℕ)^4279*100000000000000^3255 ≤ 42771468775357^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1310273701 2500000000 42771468775357 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350148937/10000000000 : ℝ), (-215330843/1000000000 : ℝ), (1310273701/2500000000 : ℝ)] ![(21972612619537/50000000000000 : ℝ), (13283305965553/100000000000000 : ℝ), (42771468775357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350148937/10000000000 : ℝ)|^4279 ≤ (21972612619537/50000000000000 : ℝ)^3255
        have hw : |(5350148937/10000000000 : ℝ)|=(5350148937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-215330843/1000000000 : ℝ)|^4279 ≤ (13283305965553/100000000000000 : ℝ)^3255
        have hw : |(-215330843/1000000000 : ℝ)|=(215330843/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1310273701/2500000000 : ℝ)|^4279 ≤ (42771468775357/100000000000000 : ℝ)^3255
        have hw : |(1310273701/2500000000 : ℝ)|=(1310273701/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s4_2 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350148867/10000000000 : ℝ)*x 0 + (655136813/1250000000 : ℝ)*x 1 + (-2153308921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350148867/10000000000 : ℝ)^4279 ≤ (5493153060403/12500000000000 : ℝ)^3255 := by
    have hnat : (5350148867 : ℕ)^4279*12500000000000^3255 ≤ 5493153060403^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350148867 10000000000 5493153060403 12500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (655136813/1250000000 : ℝ)^4279 ≤ (42771465556923/100000000000000 : ℝ)^3255 := by
    have hnat : (655136813 : ℕ)^4279*100000000000000^3255 ≤ 42771465556923^3255*1250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      655136813 1250000000 42771465556923 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2153308921/10000000000 : ℝ)^4279 ≤ (3320827486823/25000000000000 : ℝ)^3255 := by
    have hnat : (2153308921 : ℕ)^4279*25000000000000^3255 ≤ 3320827486823^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2153308921 10000000000 3320827486823 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350148867/10000000000 : ℝ), (655136813/1250000000 : ℝ), (-2153308921/10000000000 : ℝ)] ![(5493153060403/12500000000000 : ℝ), (42771465556923/100000000000000 : ℝ), (3320827486823/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350148867/10000000000 : ℝ)|^4279 ≤ (5493153060403/12500000000000 : ℝ)^3255
        have hw : |(5350148867/10000000000 : ℝ)|=(5350148867/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(655136813/1250000000 : ℝ)|^4279 ≤ (42771465556923/100000000000000 : ℝ)^3255
        have hw : |(655136813/1250000000 : ℝ)|=(655136813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2153308921/10000000000 : ℝ)|^4279 ≤ (3320827486823/25000000000000 : ℝ)^3255
        have hw : |(-2153308921/10000000000 : ℝ)|=(2153308921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s4_3 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4332459299/10000000000 : ℝ)*x 0 + (4153558833/10000000000 : ℝ)*x 1 + (4518620993/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4332459299/10000000000 : ℝ)^4279 ≤ (6660145621941/20000000000000 : ℝ)^3255 := by
    have hnat : (4332459299 : ℕ)^4279*20000000000000^3255 ≤ 6660145621941^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332459299 10000000000 6660145621941 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4153558833/10000000000 : ℝ)^4279 ≤ (15752450162359/50000000000000 : ℝ)^3255 := by
    have hnat : (4153558833 : ℕ)^4279*50000000000000^3255 ≤ 15752450162359^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4153558833 10000000000 15752450162359 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4518620993/10000000000 : ℝ)^4279 ≤ (17597185770189/50000000000000 : ℝ)^3255 := by
    have hnat : (4518620993 : ℕ)^4279*50000000000000^3255 ≤ 17597185770189^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4518620993 10000000000 17597185770189 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4332459299/10000000000 : ℝ), (4153558833/10000000000 : ℝ), (4518620993/10000000000 : ℝ)] ![(6660145621941/20000000000000 : ℝ), (15752450162359/50000000000000 : ℝ), (17597185770189/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4332459299/10000000000 : ℝ)|^4279 ≤ (6660145621941/20000000000000 : ℝ)^3255
        have hw : |(4332459299/10000000000 : ℝ)|=(4332459299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4153558833/10000000000 : ℝ)|^4279 ≤ (15752450162359/50000000000000 : ℝ)^3255
        have hw : |(4153558833/10000000000 : ℝ)|=(4153558833/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4518620993/10000000000 : ℝ)|^4279 ≤ (17597185770189/50000000000000 : ℝ)^3255
        have hw : |(4518620993/10000000000 : ℝ)|=(4518620993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s4_4 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2063669287/10000000000 : ℝ)*x 0 + (5241744381/10000000000 : ℝ)*x 1 + (5416251541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063669287/10000000000 : ℝ)^4279 ≤ (3140297025933/25000000000000 : ℝ)^3255 := by
    have hnat : (2063669287 : ℕ)^4279*25000000000000^3255 ≤ 3140297025933^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063669287 10000000000 3140297025933 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5241744381/10000000000 : ℝ)^4279 ≤ (133682617651/312500000000 : ℝ)^3255 := by
    have hnat : (5241744381 : ℕ)^4279*312500000000^3255 ≤ 133682617651^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5241744381 10000000000 133682617651 312500000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5416251541/10000000000 : ℝ)^4279 ≤ (22330187111563/50000000000000 : ℝ)^3255 := by
    have hnat : (5416251541 : ℕ)^4279*50000000000000^3255 ≤ 22330187111563^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5416251541 10000000000 22330187111563 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2063669287/10000000000 : ℝ), (5241744381/10000000000 : ℝ), (5416251541/10000000000 : ℝ)] ![(3140297025933/25000000000000 : ℝ), (133682617651/312500000000 : ℝ), (22330187111563/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2063669287/10000000000 : ℝ)|^4279 ≤ (3140297025933/25000000000000 : ℝ)^3255
        have hw : |(-2063669287/10000000000 : ℝ)|=(2063669287/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5241744381/10000000000 : ℝ)|^4279 ≤ (133682617651/312500000000 : ℝ)^3255
        have hw : |(5241744381/10000000000 : ℝ)|=(5241744381/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5416251541/10000000000 : ℝ)|^4279 ≤ (22330187111563/50000000000000 : ℝ)^3255
        have hw : |(5416251541/10000000000 : ℝ)|=(5416251541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s4_5 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5304986479/10000000000 : ℝ)*x 0 + (-61817253/312500000 : ℝ)*x 1 + (1083250307/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304986479/10000000000 : ℝ)^4279 ≤ (1738328669947/4000000000000 : ℝ)^3255 := by
    have hnat : (5304986479 : ℕ)^4279*4000000000000^3255 ≤ 1738328669947^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304986479 10000000000 1738328669947 4000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (61817253/312500000 : ℝ)^4279 ≤ (2970352267941/25000000000000 : ℝ)^3255 := by
    have hnat : (61817253 : ℕ)^4279*25000000000000^3255 ≤ 2970352267941^3255*312500000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      61817253 312500000 2970352267941 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1083250307/2000000000 : ℝ)^4279 ≤ (5582546769761/12500000000000 : ℝ)^3255 := by
    have hnat : (1083250307 : ℕ)^4279*12500000000000^3255 ≤ 5582546769761^3255*2000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1083250307 2000000000 5582546769761 12500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304986479/10000000000 : ℝ), (-61817253/312500000 : ℝ), (1083250307/2000000000 : ℝ)] ![(1738328669947/4000000000000 : ℝ), (2970352267941/25000000000000 : ℝ), (5582546769761/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304986479/10000000000 : ℝ)|^4279 ≤ (1738328669947/4000000000000 : ℝ)^3255
        have hw : |(5304986479/10000000000 : ℝ)|=(5304986479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-61817253/312500000 : ℝ)|^4279 ≤ (2970352267941/25000000000000 : ℝ)^3255
        have hw : |(-61817253/312500000 : ℝ)|=(61817253/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1083250307/2000000000 : ℝ)|^4279 ≤ (5582546769761/12500000000000 : ℝ)^3255
        have hw : |(1083250307/2000000000 : ℝ)|=(1083250307/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s4_6 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (530498649/1000000000 : ℝ)*x 0 + (2708125761/5000000000 : ℝ)*x 1 + (-19781521/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (530498649/1000000000 : ℝ)^4279 ≤ (8691643373427/20000000000000 : ℝ)^3255 := by
    have hnat : (530498649 : ℕ)^4279*20000000000000^3255 ≤ 8691643373427^3255*1000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530498649 1000000000 8691643373427 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2708125761/5000000000 : ℝ)^4279 ≤ (44660374017173/100000000000000 : ℝ)^3255 := by
    have hnat : (2708125761 : ℕ)^4279*100000000000000^3255 ≤ 44660374017173^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2708125761 5000000000 44660374017173 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (19781521/100000000 : ℝ)^4279 ≤ (11881409103347/100000000000000 : ℝ)^3255 := by
    have hnat : (19781521 : ℕ)^4279*100000000000000^3255 ≤ 11881409103347^3255*100000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      19781521 100000000 11881409103347 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(530498649/1000000000 : ℝ), (2708125761/5000000000 : ℝ), (-19781521/100000000 : ℝ)] ![(8691643373427/20000000000000 : ℝ), (44660374017173/100000000000000 : ℝ), (11881409103347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(530498649/1000000000 : ℝ)|^4279 ≤ (8691643373427/20000000000000 : ℝ)^3255
        have hw : |(530498649/1000000000 : ℝ)|=(530498649/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2708125761/5000000000 : ℝ)|^4279 ≤ (44660374017173/100000000000000 : ℝ)^3255
        have hw : |(2708125761/5000000000 : ℝ)|=(2708125761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-19781521/100000000 : ℝ)|^4279 ≤ (11881409103347/100000000000000 : ℝ)^3255
        have hw : |(-19781521/100000000 : ℝ)|=(19781521/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s4_7 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4332487933/10000000000 : ℝ)*x 0 + (903454421/2000000000 : ℝ)*x 1 + (4154914797/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4332487933/10000000000 : ℝ)^4279 ≤ (8325254359849/25000000000000 : ℝ)^3255 := by
    have hnat : (4332487933 : ℕ)^4279*25000000000000^3255 ≤ 8325254359849^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4332487933 10000000000 8325254359849 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (903454421/2000000000 : ℝ)^4279 ≤ (35180560891337/100000000000000 : ℝ)^3255 := by
    have hnat : (903454421 : ℕ)^4279*100000000000000^3255 ≤ 35180560891337^3255*2000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      903454421 2000000000 35180560891337 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4154914797/10000000000 : ℝ)^4279 ≤ (15759210828657/50000000000000 : ℝ)^3255 := by
    have hnat : (4154914797 : ℕ)^4279*50000000000000^3255 ≤ 15759210828657^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154914797 10000000000 15759210828657 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4332487933/10000000000 : ℝ), (903454421/2000000000 : ℝ), (4154914797/10000000000 : ℝ)] ![(8325254359849/25000000000000 : ℝ), (35180560891337/100000000000000 : ℝ), (15759210828657/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4332487933/10000000000 : ℝ)|^4279 ≤ (8325254359849/25000000000000 : ℝ)^3255
        have hw : |(4332487933/10000000000 : ℝ)|=(4332487933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(903454421/2000000000 : ℝ)|^4279 ≤ (35180560891337/100000000000000 : ℝ)^3255
        have hw : |(903454421/2000000000 : ℝ)|=(903454421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4154914797/10000000000 : ℝ)|^4279 ≤ (15759210828657/50000000000000 : ℝ)^3255
        have hw : |(4154914797/10000000000 : ℝ)|=(4154914797/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1319_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10773/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5517/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2951/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (15033/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10773/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (15033/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10773/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (15033/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10773/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (15033/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10773/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (15033/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10773/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (15033/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10773/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10773/100000 : ℝ) ^ (2139/512 : ℝ) ≤ (4532414338066437/50000000000000000000 : ℝ) := by
    have hpowers : (10773/100000 : ℝ)^2139 ≤ (4532414338066437/50000000000000000000 : ℝ)^512 := by
      have hnat : (10773 : ℕ)^2139*50000000000000000000^512 ≤ 4532414338066437^512*100000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10773 100000 4532414338066437 50000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10773/100000 : ℝ)) (X := (4532414338066437/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hpowhi : (15033/100000 : ℝ) ^ (2139/512 : ℝ) ≤ (18234143086440971/50000000000000000000 : ℝ) := by
    have hpowers : (15033/100000 : ℝ)^2139 ≤ (18234143086440971/50000000000000000000 : ℝ)^512 := by
      have hnat : (15033 : ℕ)^2139*50000000000000000000^512 ≤ 18234143086440971^512*100000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        15033 100000 18234143086440971 50000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (15033/100000 : ℝ)) (X := (18234143086440971/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25004532414338066437/25000000000000000000 : ℝ) ≤ (10000433929154229/10000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (25004532414338066437/25000000000000000000 : ℝ)^512 ≤ (10000433929154229/10000000000000000 : ℝ)^2139 := by
      have hnat : (25004532414338066437 : ℕ)^512*10000000000000000^2139 ≤ 10000433929154229^2139*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25004532414338066437 25000000000000000000 10000433929154229 10000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000433929154229/10000000000000000 : ℝ)) (X := (25004532414338066437/25000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (3126422909839031713/3125000000000000000 : ℝ) ≤ (10001089711022117/10000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (3126422909839031713/3125000000000000000 : ℝ)^512 ≤ (10001089711022117/10000000000000000 : ℝ)^2139 := by
      have hnat : (3126422909839031713 : ℕ)^512*10000000000000000^2139 ≤ 10001089711022117^2139*3125000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3126422909839031713 3125000000000000000 10001089711022117 10000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001089711022117/10000000000000000 : ℝ)) (X := (3126422909839031713/3125000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25018234143086440971/25000000000000000000 : ℝ) ≤ (2000349098578001/2000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (25018234143086440971/25000000000000000000 : ℝ)^512 ≤ (2000349098578001/2000000000000000 : ℝ)^2139 := by
      have hnat : (25018234143086440971 : ℕ)^512*2000000000000000^2139 ≤ 2000349098578001^2139*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25018234143086440971 25000000000000000000 2000349098578001 2000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000349098578001/2000000000000000 : ℝ)) (X := (25018234143086440971/25000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4532414338066437/50000000000000000000 : ℝ) ≤ ((3548976588505958391/3550000000000000000 : ℝ)+2*(40986366743/26625000000000 : ℝ)*(10773/100000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (3548976588505958391/3550000000000000000 : ℝ)+2*(40986366743/26625000000000 : ℝ)*(10773/100000 : ℝ)=(10000433929154229/10000000000000000 : ℝ) by norm_num, show 1+2*(4532414338066437/50000000000000000000 : ℝ)=(25004532414338066437/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18234143086440971/50000000000000000000 : ℝ)+(4532414338066437/50000000000000000000 : ℝ) ≤ ((3548976588505958391/3550000000000000000 : ℝ)+(40986366743/26625000000000 : ℝ)*((15033/100000 : ℝ)+(10773/100000 : ℝ)))^(2139/512 : ℝ) := by
    rw [show (3548976588505958391/3550000000000000000 : ℝ)+(40986366743/26625000000000 : ℝ)*((15033/100000 : ℝ)+(10773/100000 : ℝ))=(10001089711022117/10000000000000000 : ℝ) by norm_num, show 1+(18234143086440971/50000000000000000000 : ℝ)+(4532414338066437/50000000000000000000 : ℝ)=(3126422909839031713/3125000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18234143086440971/50000000000000000000 : ℝ) ≤ ((3548976588505958391/3550000000000000000 : ℝ)+2*(40986366743/26625000000000 : ℝ)*(15033/100000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (3548976588505958391/3550000000000000000 : ℝ)+2*(40986366743/26625000000000 : ℝ)*(15033/100000 : ℝ)=(2000349098578001/2000000000000000 : ℝ) by norm_num, show 1+2*(18234143086440971/50000000000000000000 : ℝ)=(25018234143086440971/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3548976588505958391/3550000000000000000 : ℝ)*(X 1 0+X 2 0)+(40986366743/26625000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (10773/100000 : ℝ)) (hi := (15033/100000 : ℝ)) (c := (3548976588505958391/3550000000000000000 : ℝ)) (alpha := (40986366743/26625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3548976588505958391/3550000000000000000 : ℝ)*(X 0 1+X 2 1)+(40986366743/26625000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (10773/100000 : ℝ)) (hi := (15033/100000 : ℝ)) (c := (3548976588505958391/3550000000000000000 : ℝ)) (alpha := (40986366743/26625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3548976588505958391/3550000000000000000 : ℝ)*(X 0 2+X 1 2)+(40986366743/26625000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (10773/100000 : ℝ)) (hi := (15033/100000 : ℝ)) (c := (3548976588505958391/3550000000000000000 : ℝ)) (alpha := (40986366743/26625000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-515913887/2500000000 : ℝ)*X 0 0+(2708452163/5000000000 : ℝ)*X 0 1+(2620547529/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350148937/10000000000 : ℝ)*X 1 0+(-215330843/1000000000 : ℝ)*X 1 1+(1310273701/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350148867/10000000000 : ℝ)*X 2 0+(655136813/1250000000 : ℝ)*X 2 1+(-2153308921/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4332459299/10000000000 : ℝ)*X 0 0+(4153558833/10000000000 : ℝ)*X 0 1+(4518620993/10000000000 : ℝ)*X 0 2+(4332459299/10000000000 : ℝ)*X 1 0+(4153558833/10000000000 : ℝ)*X 1 1+(4518620993/10000000000 : ℝ)*X 1 2+(4332459299/10000000000 : ℝ)*X 2 0+(4153558833/10000000000 : ℝ)*X 2 1+(4518620993/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2063669287/10000000000 : ℝ)*X 0 0+(5241744381/10000000000 : ℝ)*X 0 1+(5416251541/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304986479/10000000000 : ℝ)*X 1 0+(-61817253/312500000 : ℝ)*X 1 1+(1083250307/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((530498649/1000000000 : ℝ)*X 2 0+(2708125761/5000000000 : ℝ)*X 2 1+(-19781521/100000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4332487933/10000000000 : ℝ)*X 0 0+(903454421/2000000000 : ℝ)*X 0 1+(4154914797/10000000000 : ℝ)*X 0 2+(4332487933/10000000000 : ℝ)*X 1 0+(903454421/2000000000 : ℝ)*X 1 1+(4154914797/10000000000 : ℝ)*X 1 2+(4332487933/10000000000 : ℝ)*X 2 0+(903454421/2000000000 : ℝ)*X 2 1+(4154914797/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (176276574570065146139086509/22187500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (131416697/6250000000000 : ℝ)*(base19) + (2009603847/100000000000000 : ℝ)*(base23) + (299870407/100000000000000 : ℝ)*(upper3) + (2380651/10000000000000 : ℝ)*(lower4) + (1053420251274633/25000000000000 : ℝ)*(major0) + (1053420251274633/25000000000000 : ℝ)*(major1) + (1053420251274633/25000000000000 : ℝ)*(major2) + (5688026081997463/100000000000000 : ℝ)*(sp0) + (5688055739061799/100000000000000 : ℝ)*(sp1) + (1422012088091243/25000000000000 : ℝ)*(sp2) + (684819956149089/25000000000000 : ℝ)*(sp3) + (992491609/3125000000000 : ℝ)*(sp4) + (1869940033/25000000000000 : ℝ)*(sp6) + (24079043091/100000000000000 : ℝ)*(sp7) + (342412987954931/12500000000000 : ℝ)*(f.failure) + (5688057841728951/100000000000000 : ℝ)*(f.sum) + (12968023196943/1775000000000000000000000000 : ℝ)*base65 + (59452499777754497/88750000000000000000000000000000 : ℝ)*base68 + (204150227137754497/88750000000000000000000000000000 : ℝ)*base70 + (505803765916504497/88750000000000000000000000000000 : ℝ)*base72 + (5354920457293/1775000000000000000000000000 : ℝ)*base73 + (634563900780254497/88750000000000000000000000000000 : ℝ)*base76 + (637318799569745503/88750000000000000000000000000000 : ℝ)*base77 + (2007758256960254497/88750000000000000000000000000000 : ℝ)*base80 + (10699794972543/1775000000000000000000000000 : ℝ)*base81 + (14644067/1250000000000000000000 : ℝ)*base89 + (14644067/1250000000000000000000 : ℝ)*base91 + (14644067/1250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (328005971657268690409762671/88750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (663482343/100000000000000 : ℝ)*(base19) + (362440767/50000000000000 : ℝ)*(base23) + (15151469/20000000000000 : ℝ)*(upper3) + (2343809/10000000000000 : ℝ)*(lower4) + (41447407/50000000000000 : ℝ)*(upper5) + (2122532661728973/50000000000000 : ℝ)*(major0) + (2122532661728973/50000000000000 : ℝ)*(major1) + (2122532661728973/50000000000000 : ℝ)*(major2) + (2568305731/20000000000000 : ℝ)*(sp1) + (6734159703/50000000000000 : ℝ)*(sp2) + (358151484379713/6250000000000 : ℝ)*(sp4) + (5730410245064411/100000000000000 : ℝ)*(sp5) + (5730409556874469/100000000000000 : ℝ)*(sp6) + (1379853386822869/50000000000000 : ℝ)*(sp7) + (1379853386822869/50000000000000 : ℝ)*(f.failure) + (358151484379713/6250000000000 : ℝ)*(f.sum) + (3307349350723/887500000000000000000000000 : ℝ)*base66 + (604839104712637557/177500000000000000000000000000000 : ℝ)*base68 + (2682839329547362443/177500000000000000000000000000000 : ℝ)*base69 + (472237236262637557/177500000000000000000000000000000 : ℝ)*base72 + (121490623131/110937500000000000000000000 : ℝ)*base74 + (1982774754129862443/177500000000000000000000000000000 : ℝ)*base75 + (373807956817362443/177500000000000000000000000000000 : ℝ)*base77 + (1706733811352362443/177500000000000000000000000000000 : ℝ)*base79 + (1509962609063/221875000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (72909467/5000000000000000000000 : ℝ)*base90 + (72909467/5000000000000000000000 : ℝ)*base92 + (72909467/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1319_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (15033/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10773/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5517/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1319_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1319_s5_0 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2063952207/10000000000 : ℝ)*x 0 + (5414367/10000000 : ℝ)*x 1 + (2621718617/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2063952207/10000000000 : ℝ)^4279 ≤ (502538079667/4000000000000 : ℝ)^3255 := by
    have hnat : (2063952207 : ℕ)^4279*4000000000000^3255 ≤ 502538079667^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2063952207 10000000000 502538079667 4000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5414367/10000000 : ℝ)^4279 ≤ (44639947596777/100000000000000 : ℝ)^3255 := by
    have hnat : (5414367 : ℕ)^4279*100000000000000^3255 ≤ 44639947596777^3255*10000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5414367 10000000 44639947596777 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2621718617/5000000000 : ℝ)^4279 ≤ (4279660040153/10000000000000 : ℝ)^3255 := by
    have hnat : (2621718617 : ℕ)^4279*10000000000000^3255 ≤ 4279660040153^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2621718617 5000000000 4279660040153 10000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2063952207/10000000000 : ℝ), (5414367/10000000 : ℝ), (2621718617/5000000000 : ℝ)] ![(502538079667/4000000000000 : ℝ), (44639947596777/100000000000000 : ℝ), (4279660040153/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2063952207/10000000000 : ℝ)|^4279 ≤ (502538079667/4000000000000 : ℝ)^3255
        have hw : |(-2063952207/10000000000 : ℝ)|=(2063952207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5414367/10000000 : ℝ)|^4279 ≤ (44639947596777/100000000000000 : ℝ)^3255
        have hw : |(5414367/10000000 : ℝ)|=(5414367/10000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2621718617/5000000000 : ℝ)|^4279 ≤ (4279660040153/10000000000000 : ℝ)^3255
        have hw : |(2621718617/5000000000 : ℝ)|=(2621718617/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s5_1 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668687809/1250000000 : ℝ)*x 0 + (-537767427/2500000000 : ℝ)*x 1 + (5243437281/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668687809/1250000000 : ℝ)^4279 ≤ (43938244942443/100000000000000 : ℝ)^3255 := by
    have hnat : (668687809 : ℕ)^4279*100000000000000^3255 ≤ 43938244942443^3255*1250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668687809 1250000000 43938244942443 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (537767427/2500000000 : ℝ)^4279 ≤ (6632577069127/50000000000000 : ℝ)^3255 := by
    have hnat : (537767427 : ℕ)^4279*50000000000000^3255 ≤ 6632577069127^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      537767427 2500000000 6632577069127 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5243437281/10000000000 : ℝ)^4279 ≤ (21398300452911/50000000000000 : ℝ)^3255 := by
    have hnat : (5243437281 : ℕ)^4279*50000000000000^3255 ≤ 21398300452911^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243437281 10000000000 21398300452911 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668687809/1250000000 : ℝ), (-537767427/2500000000 : ℝ), (5243437281/10000000000 : ℝ)] ![(43938244942443/100000000000000 : ℝ), (6632577069127/50000000000000 : ℝ), (21398300452911/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668687809/1250000000 : ℝ)|^4279 ≤ (43938244942443/100000000000000 : ℝ)^3255
        have hw : |(668687809/1250000000 : ℝ)|=(668687809/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-537767427/2500000000 : ℝ)|^4279 ≤ (6632577069127/50000000000000 : ℝ)^3255
        have hw : |(-537767427/2500000000 : ℝ)|=(537767427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5243437281/10000000000 : ℝ)|^4279 ≤ (21398300452911/50000000000000 : ℝ)^3255
        have hw : |(5243437281/10000000000 : ℝ)|=(5243437281/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s5_2 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1069900457/2000000000 : ℝ)*x 0 + (5243437373/10000000000 : ℝ)*x 1 + (-430213967/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1069900457/2000000000 : ℝ)^4279 ≤ (21969121461661/50000000000000 : ℝ)^3255 := by
    have hnat : (1069900457 : ℕ)^4279*50000000000000^3255 ≤ 21969121461661^3255*2000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1069900457 2000000000 21969121461661 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5243437373/10000000000 : ℝ)^4279 ≤ (10699150473237/25000000000000 : ℝ)^3255 := by
    have hnat : (5243437373 : ℕ)^4279*25000000000000^3255 ≤ 10699150473237^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5243437373 10000000000 10699150473237 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (430213967/2000000000 : ℝ)^4279 ≤ (13265155167817/100000000000000 : ℝ)^3255 := by
    have hnat : (430213967 : ℕ)^4279*100000000000000^3255 ≤ 13265155167817^3255*2000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430213967 2000000000 13265155167817 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1069900457/2000000000 : ℝ), (5243437373/10000000000 : ℝ), (-430213967/2000000000 : ℝ)] ![(21969121461661/50000000000000 : ℝ), (10699150473237/25000000000000 : ℝ), (13265155167817/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1069900457/2000000000 : ℝ)|^4279 ≤ (21969121461661/50000000000000 : ℝ)^3255
        have hw : |(1069900457/2000000000 : ℝ)|=(1069900457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5243437373/10000000000 : ℝ)|^4279 ≤ (10699150473237/25000000000000 : ℝ)^3255
        have hw : |(5243437373/10000000000 : ℝ)|=(5243437373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-430213967/2000000000 : ℝ)|^4279 ≤ (13265155167817/100000000000000 : ℝ)^3255
        have hw : |(-430213967/2000000000 : ℝ)|=(430213967/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s5_3 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (86652717/200000000 : ℝ)*x 0 + (4158603459/10000000000 : ℝ)*x 1 + (564191529/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (86652717/200000000 : ℝ)^4279 ≤ (33302512063069/100000000000000 : ℝ)^3255 := by
    have hnat : (86652717 : ℕ)^4279*100000000000000^3255 ≤ 33302512063069^3255*200000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      86652717 200000000 33302512063069 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4158603459/10000000000 : ℝ)^4279 ≤ (394440138661/1250000000000 : ℝ)^3255 := by
    have hnat : (4158603459 : ℕ)^4279*1250000000000^3255 ≤ 394440138661^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4158603459 10000000000 394440138661 1250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (564191529/1250000000 : ℝ)^4279 ≤ (549098075357/1562500000000 : ℝ)^3255 := by
    have hnat : (564191529 : ℕ)^4279*1562500000000^3255 ≤ 549098075357^3255*1250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      564191529 1250000000 549098075357 1562500000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(86652717/200000000 : ℝ), (4158603459/10000000000 : ℝ), (564191529/1250000000 : ℝ)] ![(33302512063069/100000000000000 : ℝ), (394440138661/1250000000000 : ℝ), (549098075357/1562500000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(86652717/200000000 : ℝ)|^4279 ≤ (33302512063069/100000000000000 : ℝ)^3255
        have hw : |(86652717/200000000 : ℝ)|=(86652717/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4158603459/10000000000 : ℝ)|^4279 ≤ (394440138661/1250000000000 : ℝ)^3255
        have hw : |(4158603459/10000000000 : ℝ)|=(4158603459/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(564191529/1250000000 : ℝ)|^4279 ≤ (549098075357/1562500000000 : ℝ)^3255
        have hw : |(564191529/1250000000 : ℝ)|=(564191529/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s5_4 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1031982401/5000000000 : ℝ)*x 0 + (2622025549/5000000000 : ℝ)*x 1 + (5413749979/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1031982401/5000000000 : ℝ)^4279 ≤ (1570444097181/12500000000000 : ℝ)^3255 := by
    have hnat : (1031982401 : ℕ)^4279*12500000000000^3255 ≤ 1570444097181^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1031982401 5000000000 1570444097181 12500000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2622025549/5000000000 : ℝ)^4279 ≤ (856063741051/2000000000000 : ℝ)^3255 := by
    have hnat : (2622025549 : ℕ)^4279*2000000000000^3255 ≤ 856063741051^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2622025549 5000000000 856063741051 2000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5413749979/10000000000 : ℝ)^4279 ≤ (22316630081921/50000000000000 : ℝ)^3255 := by
    have hnat : (5413749979 : ℕ)^4279*50000000000000^3255 ≤ 22316630081921^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5413749979 10000000000 22316630081921 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1031982401/5000000000 : ℝ), (2622025549/5000000000 : ℝ), (5413749979/10000000000 : ℝ)] ![(1570444097181/12500000000000 : ℝ), (856063741051/2000000000000 : ℝ), (22316630081921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1031982401/5000000000 : ℝ)|^4279 ≤ (1570444097181/12500000000000 : ℝ)^3255
        have hw : |(-1031982401/5000000000 : ℝ)|=(1031982401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2622025549/5000000000 : ℝ)|^4279 ≤ (856063741051/2000000000000 : ℝ)^3255
        have hw : |(2622025549/5000000000 : ℝ)|=(2622025549/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5413749979/10000000000 : ℝ)|^4279 ≤ (22316630081921/50000000000000 : ℝ)^3255
        have hw : |(5413749979/10000000000 : ℝ)|=(5413749979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s5_5 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305593931/10000000000 : ℝ)*x 0 + (-1980757057/10000000000 : ℝ)*x 1 + (2706874967/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305593931/10000000000 : ℝ)^4279 ≤ (43464758570361/100000000000000 : ℝ)^3255 := by
    have hnat : (5305593931 : ℕ)^4279*100000000000000^3255 ≤ 43464758570361^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305593931 10000000000 43464758570361 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1980757057/10000000000 : ℝ)^4279 ≤ (11901981744149/100000000000000 : ℝ)^3255 := by
    have hnat : (1980757057 : ℕ)^4279*100000000000000^3255 ≤ 11901981744149^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980757057 10000000000 11901981744149 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2706874967/5000000000 : ℝ)^4279 ≤ (44633259676129/100000000000000 : ℝ)^3255 := by
    have hnat : (2706874967 : ℕ)^4279*100000000000000^3255 ≤ 44633259676129^3255*5000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2706874967 5000000000 44633259676129 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305593931/10000000000 : ℝ), (-1980757057/10000000000 : ℝ), (2706874967/5000000000 : ℝ)] ![(43464758570361/100000000000000 : ℝ), (11901981744149/100000000000000 : ℝ), (44633259676129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305593931/10000000000 : ℝ)|^4279 ≤ (43464758570361/100000000000000 : ℝ)^3255
        have hw : |(5305593931/10000000000 : ℝ)|=(5305593931/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1980757057/10000000000 : ℝ)|^4279 ≤ (11901981744149/100000000000000 : ℝ)^3255
        have hw : |(-1980757057/10000000000 : ℝ)|=(1980757057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2706874967/5000000000 : ℝ)|^4279 ≤ (44633259676129/100000000000000 : ℝ)^3255
        have hw : |(2706874967/5000000000 : ℝ)|=(2706874967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s5_6 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5305595049/10000000000 : ℝ)*x 0 + (1353437227/2500000000 : ℝ)*x 1 + (-1980756941/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305595049/10000000000 : ℝ)^4279 ≤ (8692954122127/20000000000000 : ℝ)^3255 := by
    have hnat : (5305595049 : ℕ)^4279*20000000000000^3255 ≤ 8692954122127^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305595049 10000000000 8692954122127 20000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1353437227/2500000000 : ℝ)^4279 ≤ (11158312139069/25000000000000 : ℝ)^3255 := by
    have hnat : (1353437227 : ℕ)^4279*25000000000000^3255 ≤ 11158312139069^3255*2500000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1353437227 2500000000 11158312139069 25000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1980756941/10000000000 : ℝ)^4279 ≤ (238039616557/2000000000000 : ℝ)^3255 := by
    have hnat : (1980756941 : ℕ)^4279*2000000000000^3255 ≤ 238039616557^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1980756941 10000000000 238039616557 2000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305595049/10000000000 : ℝ), (1353437227/2500000000 : ℝ), (-1980756941/10000000000 : ℝ)] ![(8692954122127/20000000000000 : ℝ), (11158312139069/25000000000000 : ℝ), (238039616557/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305595049/10000000000 : ℝ)|^4279 ≤ (8692954122127/20000000000000 : ℝ)^3255
        have hw : |(5305595049/10000000000 : ℝ)|=(5305595049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1353437227/2500000000 : ℝ)|^4279 ≤ (11158312139069/25000000000000 : ℝ)^3255
        have hw : |(1353437227/2500000000 : ℝ)|=(1353437227/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1980756941/10000000000 : ℝ)|^4279 ≤ (238039616557/2000000000000 : ℝ)^3255
        have hw : |(-1980756941/10000000000 : ℝ)|=(1980756941/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1319_s5_7 (p : ℝ) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (108316567/250000000 : ℝ)*x 0 + (902451343/2000000000 : ℝ)*x 1 + (4159884969/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (108316567/250000000 : ℝ)^4279 ≤ (16651391583931/50000000000000 : ℝ)^3255 := by
    have hnat : (108316567 : ℕ)^4279*50000000000000^3255 ≤ 16651391583931^3255*250000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108316567 250000000 16651391583931 50000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (902451343/2000000000 : ℝ)^4279 ≤ (35129221981893/100000000000000 : ℝ)^3255 := by
    have hnat : (902451343 : ℕ)^4279*100000000000000^3255 ≤ 35129221981893^3255*2000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      902451343 2000000000 35129221981893 100000000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4159884969/10000000000 : ℝ)^4279 ≤ (1972999677041/6250000000000 : ℝ)^3255 := by
    have hnat : (4159884969 : ℕ)^4279*6250000000000^3255 ≤ 1972999677041^3255*10000000000^4279 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4159884969 10000000000 1972999677041 6250000000000 4279 3255 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4279/1024 : ℝ)) 4279 3255 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(108316567/250000000 : ℝ), (902451343/2000000000 : ℝ), (4159884969/10000000000 : ℝ)] ![(16651391583931/50000000000000 : ℝ), (35129221981893/100000000000000 : ℝ), (1972999677041/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(108316567/250000000 : ℝ)|^4279 ≤ (16651391583931/50000000000000 : ℝ)^3255
        have hw : |(108316567/250000000 : ℝ)|=(108316567/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(902451343/2000000000 : ℝ)|^4279 ≤ (35129221981893/100000000000000 : ℝ)^3255
        have hw : |(902451343/2000000000 : ℝ)|=(902451343/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4159884969/10000000000 : ℝ)|^4279 ≤ (1972999677041/6250000000000 : ℝ)^3255
        have hw : |(4159884969/10000000000 : ℝ)|=(4159884969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1319_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5517/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (2771/25000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7351/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5517/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5517/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5517/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2951/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5517/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5517/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2951/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5517/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5517/50000 : ℝ) ^ (2139/512 : ℝ) ≤ (2504567101120237/25000000000000000000 : ℝ) := by
    have hpowers : (5517/50000 : ℝ)^2139 ≤ (2504567101120237/25000000000000000000 : ℝ)^512 := by
      have hnat : (5517 : ℕ)^2139*25000000000000000000^512 ≤ 2504567101120237^512*50000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5517 50000 2504567101120237 25000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5517/50000 : ℝ)) (X := (2504567101120237/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2951/20000 : ℝ) ^ (2139/512 : ℝ) ≤ (33732519953547207/100000000000000000000 : ℝ) := by
    have hpowers : (2951/20000 : ℝ)^2139 ≤ (33732519953547207/100000000000000000000 : ℝ)^512 := by
      have hnat : (2951 : ℕ)^2139*100000000000000000000^512 ≤ 33732519953547207^512*20000^2139 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2951 20000 33732519953547207 100000000000000000000 2139 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2951/20000 : ℝ)) (X := (33732519953547207/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (12502504567101120237/12500000000000000000 : ℝ) ≤ (10000479566395447/10000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (12502504567101120237/12500000000000000000 : ℝ)^512 ≤ (10000479566395447/10000000000000000 : ℝ)^2139 := by
      have hnat : (12502504567101120237 : ℕ)^512*10000000000000000^2139 ≤ 10000479566395447^2139*12500000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502504567101120237 12500000000000000000 10000479566395447 10000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000479566395447/10000000000000000 : ℝ)) (X := (12502504567101120237/12500000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008750157671605631/20000000000000000000 : ℝ) ≤ (500052353149477/500000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (20008750157671605631/20000000000000000000 : ℝ)^512 ≤ (500052353149477/500000000000000 : ℝ)^2139 := by
      have hnat : (20008750157671605631 : ℕ)^512*500000000000000^2139 ≤ 500052353149477^2139*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008750157671605631 20000000000000000000 500052353149477 500000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500052353149477/500000000000000 : ℝ)) (X := (20008750157671605631/20000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033732519953547207/50000000000000000000 : ℝ) ≤ (10001614559583633/10000000000000000 : ℝ) ^ (2139/512 : ℝ) := by
    have hpowers : (50033732519953547207/50000000000000000000 : ℝ)^512 ≤ (10001614559583633/10000000000000000 : ℝ)^2139 := by
      have hnat : (50033732519953547207 : ℕ)^512*10000000000000000^2139 ≤ 10001614559583633^2139*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033732519953547207 50000000000000000000 10001614559583633 10000000000000000 512 2139 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001614559583633/10000000000000000 : ℝ)) (X := (50033732519953547207/50000000000000000000 : ℝ)) (by norm_num) 2139 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2504567101120237/25000000000000000000 : ℝ) ≤ ((37199260951719013963/37210000000000000000 : ℝ)+2*(567496594093/372100000000000 : ℝ)*(5517/50000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (37199260951719013963/37210000000000000000 : ℝ)+2*(567496594093/372100000000000 : ℝ)*(5517/50000 : ℝ)=(10000479566395447/10000000000000000 : ℝ) by norm_num, show 1+2*(2504567101120237/25000000000000000000 : ℝ)=(12502504567101120237/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33732519953547207/100000000000000000000 : ℝ)+(2504567101120237/25000000000000000000 : ℝ) ≤ ((37199260951719013963/37210000000000000000 : ℝ)+(567496594093/372100000000000 : ℝ)*((2951/20000 : ℝ)+(5517/50000 : ℝ)))^(2139/512 : ℝ) := by
    rw [show (37199260951719013963/37210000000000000000 : ℝ)+(567496594093/372100000000000 : ℝ)*((2951/20000 : ℝ)+(5517/50000 : ℝ))=(500052353149477/500000000000000 : ℝ) by norm_num, show 1+(33732519953547207/100000000000000000000 : ℝ)+(2504567101120237/25000000000000000000 : ℝ)=(20008750157671605631/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33732519953547207/100000000000000000000 : ℝ) ≤ ((37199260951719013963/37210000000000000000 : ℝ)+2*(567496594093/372100000000000 : ℝ)*(2951/20000 : ℝ))^(2139/512 : ℝ) := by
    rw [show (37199260951719013963/37210000000000000000 : ℝ)+2*(567496594093/372100000000000 : ℝ)*(2951/20000 : ℝ)=(10001614559583633/10000000000000000 : ℝ) by norm_num, show 1+2*(33732519953547207/100000000000000000000 : ℝ)=(50033732519953547207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37199260951719013963/37210000000000000000 : ℝ)*(X 1 0+X 2 0)+(567496594093/372100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (5517/50000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (37199260951719013963/37210000000000000000 : ℝ)) (alpha := (567496594093/372100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37199260951719013963/37210000000000000000 : ℝ)*(X 0 1+X 2 1)+(567496594093/372100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (5517/50000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (37199260951719013963/37210000000000000000 : ℝ)) (alpha := (567496594093/372100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37199260951719013963/37210000000000000000 : ℝ)*(X 0 2+X 1 2)+(567496594093/372100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2139/512 : ℝ)) (lo := (5517/50000 : ℝ)) (hi := (2951/20000 : ℝ)) (c := (37199260951719013963/37210000000000000000 : ℝ)) (alpha := (567496594093/372100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2063952207/10000000000 : ℝ)*X 0 0+(5414367/10000000 : ℝ)*X 0 1+(2621718617/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668687809/1250000000 : ℝ)*X 1 0+(-537767427/2500000000 : ℝ)*X 1 1+(5243437281/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1069900457/2000000000 : ℝ)*X 2 0+(5243437373/10000000000 : ℝ)*X 2 1+(-430213967/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((86652717/200000000 : ℝ)*X 0 0+(4158603459/10000000000 : ℝ)*X 0 1+(564191529/1250000000 : ℝ)*X 0 2+(86652717/200000000 : ℝ)*X 1 0+(4158603459/10000000000 : ℝ)*X 1 1+(564191529/1250000000 : ℝ)*X 1 2+(86652717/200000000 : ℝ)*X 2 0+(4158603459/10000000000 : ℝ)*X 2 1+(564191529/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1031982401/5000000000 : ℝ)*X 0 0+(2622025549/5000000000 : ℝ)*X 0 1+(5413749979/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5305593931/10000000000 : ℝ)*X 1 0+(-1980757057/10000000000 : ℝ)*X 1 1+(2706874967/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305595049/10000000000 : ℝ)*X 2 0+(1353437227/2500000000 : ℝ)*X 2 1+(-1980756941/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((108316567/250000000 : ℝ)*X 0 0+(902451343/2000000000 : ℝ)*X 0 1+(4159884969/10000000000 : ℝ)*X 0 2+(108316567/250000000 : ℝ)*X 1 0+(902451343/2000000000 : ℝ)*X 1 1+(4159884969/10000000000 : ℝ)*X 1 2+(108316567/250000000 : ℝ)*X 2 0+(902451343/2000000000 : ℝ)*X 2 1+(4159884969/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1319_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (17429862044448926518735458111/1860500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (912923737/50000000000000 : ℝ)*(base19) + (385336993/25000000000000 : ℝ)*(base23) + (44241057/12500000000000 : ℝ)*(upper3) + (42790081/100000000000000 : ℝ)*(upper4) + (106776579/100000000000000 : ℝ)*(upper5) + (4333964830938613/100000000000000 : ℝ)*(major0) + (4333964830938613/100000000000000 : ℝ)*(major1) + (2166982415469307/50000000000000 : ℝ)*(major2) + (36564983707437/625000000000 : ℝ)*(sp0) + (1170085478750941/20000000000000 : ℝ)*(sp1) + (5850427678254207/100000000000000 : ℝ)*(sp2) + (140874088883969/5000000000000 : ℝ)*(sp3) + (1591320613/5000000000000 : ℝ)*(sp4) + (3670463297/20000000000000 : ℝ)*(sp7) + (563500025999173/20000000000000 : ℝ)*(f.failure) + (5850429219602179/100000000000000 : ℝ)*(f.sum) + (148600965296289/37210000000000000000000000000 : ℝ)*base66 + (57257833233821946681/3721000000000000000000000000000000 : ℝ)*base68 + (23594522981908883641/1860500000000000000000000000000000 : ℝ)*base69 + (10177731465906946681/3721000000000000000000000000000000 : ℝ)*base72 + (246568168286439/37210000000000000000000000000 : ℝ)*base74 + (27344670905166383641/1860500000000000000000000000000000 : ℝ)*base75 + (22879303271751246681/3721000000000000000000000000000000 : ℝ)*base78 + (41872479690717753319/3721000000000000000000000000000000 : ℝ)*base79 + (19035804583609/18605000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (10331861/2000000000000000000000 : ℝ)*base89 + (10331861/2000000000000000000000 : ℝ)*base91 + (9668139/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (631481404708504622978997/5814062500000000000000000000000 : ℝ) := by norm_num
    linear_combination (1108476157/100000000000000 : ℝ)*(base19) + (1279163671/50000000000000 : ℝ)*(base23) + (21210323/25000000000000 : ℝ)*(lower4) + (24409563/10000000000000 : ℝ)*(upper5) + (54567043735679/1250000000000 : ℝ)*(major0) + (54567043735679/1250000000000 : ℝ)*(major1) + (54567043735679/1250000000000 : ℝ)*(major2) + (1798053531/50000000000000 : ℝ)*(sp0) + (31888617553/100000000000000 : ℝ)*(sp1) + (37714226929/100000000000000 : ℝ)*(sp2) + (1178562213873379/20000000000000 : ℝ)*(sp4) + (2946390834190123/50000000000000 : ℝ)*(sp5) + (1178554878583937/20000000000000 : ℝ)*(sp6) + (1418956164307123/50000000000000 : ℝ)*(sp7) + (1418956164307123/50000000000000 : ℝ)*(f.failure) + (1473203666368489/25000000000000 : ℝ)*(f.sum) + (1975089822797/465125000000000000000000000 : ℝ)*base65 + (165966327560514123/46512500000000000000000000000000 : ℝ)*base68 + (357501929750398377/46512500000000000000000000000000 : ℝ)*base69 + (161156051357460877/46512500000000000000000000000000 : ℝ)*base71 + (279262401583/232562500000000000000000000 : ℝ)*base73 + (732862202786348377/46512500000000000000000000000000 : ℝ)*base75 + (213682883286860877/46512500000000000000000000000000 : ℝ)*base77 + (946951432884148377/46512500000000000000000000000000 : ℝ)*base79 + (1523955863501/1860500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (53264989/5000000000000000000000 : ℝ)*base90 + (53264989/5000000000000000000000 : ℝ)*base92 + (53264989/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1319_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2951/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5517/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2771/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1319_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1319_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8099/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2771/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1319_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1319_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1319_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2139/512 : ℝ) ≤ p) (hpb : p ≤ (4279/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (153823057/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8099/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9697/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2771/25000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7351/50000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1319_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
