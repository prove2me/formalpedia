-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1284_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:24:19.704747+00:00
-- url     : https://prove2.me/submissions/9e9f4671-c5a6-41ae-b355-d26fb6ca3a83

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
theorem support_rectangle_w1284_box_0 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1923148497/10000000000 : ℝ)*x 0 + (5392338469/10000000000 : ℝ)*x 1 + (5392338019/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1923148497/10000000000 : ℝ)^1061 ≤ (56923291773/500000000000 : ℝ)^805 := by
    have hnat : (1923148497 : ℕ)^1061*500000000000^805 ≤ 56923291773^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1923148497 10000000000 56923291773 500000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392338469/10000000000 : ℝ)^1061 ≤ (44307673253713/100000000000000 : ℝ)^805 := by
    have hnat : (5392338469 : ℕ)^1061*100000000000000^805 ≤ 44307673253713^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392338469 10000000000 44307673253713 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392338019/10000000000 : ℝ)^1061 ≤ (44307668380293/100000000000000 : ℝ)^805 := by
    have hnat : (5392338019 : ℕ)^1061*100000000000000^805 ≤ 44307668380293^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392338019 10000000000 44307668380293 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1923148497/10000000000 : ℝ), (5392338469/10000000000 : ℝ), (5392338019/10000000000 : ℝ)] ![(56923291773/500000000000 : ℝ), (44307673253713/100000000000000 : ℝ), (44307668380293/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1923148497/10000000000 : ℝ)|^1061 ≤ (56923291773/500000000000 : ℝ)^805
        have hw : |(-1923148497/10000000000 : ℝ)|=(1923148497/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392338469/10000000000 : ℝ)|^1061 ≤ (44307673253713/100000000000000 : ℝ)^805
        have hw : |(5392338469/10000000000 : ℝ)|=(5392338469/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392338019/10000000000 : ℝ)|^1061 ≤ (44307668380293/100000000000000 : ℝ)^805
        have hw : |(5392338019/10000000000 : ℝ)|=(5392338019/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_1 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5284222581/10000000000 : ℝ)*x 0 + (-2070958379/10000000000 : ℝ)*x 1 + (5392338261/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284222581/10000000000 : ℝ)^1061 ≤ (43140547452979/100000000000000 : ℝ)^805 := by
    have hnat : (5284222581 : ℕ)^1061*100000000000000^805 ≤ 43140547452979^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284222581 10000000000 43140547452979 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2070958379/10000000000 : ℝ)^1061 ≤ (12551781540711/100000000000000 : ℝ)^805 := by
    have hnat : (2070958379 : ℕ)^1061*100000000000000^805 ≤ 12551781540711^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070958379 10000000000 12551781540711 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392338261/10000000000 : ℝ)^1061 ≤ (4430767100111/10000000000000 : ℝ)^805 := by
    have hnat : (5392338261 : ℕ)^1061*10000000000000^805 ≤ 4430767100111^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392338261 10000000000 4430767100111 10000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284222581/10000000000 : ℝ), (-2070958379/10000000000 : ℝ), (5392338261/10000000000 : ℝ)] ![(43140547452979/100000000000000 : ℝ), (12551781540711/100000000000000 : ℝ), (4430767100111/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284222581/10000000000 : ℝ)|^1061 ≤ (43140547452979/100000000000000 : ℝ)^805
        have hw : |(5284222581/10000000000 : ℝ)|=(5284222581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2070958379/10000000000 : ℝ)|^1061 ≤ (12551781540711/100000000000000 : ℝ)^805
        have hw : |(-2070958379/10000000000 : ℝ)|=(2070958379/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392338261/10000000000 : ℝ)|^1061 ≤ (4430767100111/10000000000000 : ℝ)^805
        have hw : |(5392338261/10000000000 : ℝ)|=(5392338261/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_2 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2642111401/5000000000 : ℝ)*x 0 + (215693531/400000000 : ℝ)*x 1 + (-2070958061/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2642111401/5000000000 : ℝ)^1061 ≤ (10785137457751/25000000000000 : ℝ)^805 := by
    have hnat : (2642111401 : ℕ)^1061*25000000000000^805 ≤ 10785137457751^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2642111401 5000000000 10785137457751 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (215693531/400000000 : ℝ)^1061 ≤ (44307671152727/100000000000000 : ℝ)^805 := by
    have hnat : (215693531 : ℕ)^1061*100000000000000^805 ≤ 44307671152727^805*400000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215693531 400000000 44307671152727 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2070958061/10000000000 : ℝ)^1061 ≤ (12551779000437/100000000000000 : ℝ)^805 := by
    have hnat : (2070958061 : ℕ)^1061*100000000000000^805 ≤ 12551779000437^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2070958061 10000000000 12551779000437 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2642111401/5000000000 : ℝ), (215693531/400000000 : ℝ), (-2070958061/10000000000 : ℝ)] ![(10785137457751/25000000000000 : ℝ), (44307671152727/100000000000000 : ℝ), (12551779000437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2642111401/5000000000 : ℝ)|^1061 ≤ (10785137457751/25000000000000 : ℝ)^805
        have hw : |(2642111401/5000000000 : ℝ)|=(2642111401/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(215693531/400000000 : ℝ)|^1061 ≤ (44307671152727/100000000000000 : ℝ)^805
        have hw : |(215693531/400000000 : ℝ)|=(215693531/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2070958061/10000000000 : ℝ)|^1061 ≤ (12551779000437/100000000000000 : ℝ)^805
        have hw : |(-2070958061/10000000000 : ℝ)|=(2070958061/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_3 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4491647431/10000000000 : ℝ)*x 0 + (533903817/1250000000 : ℝ)*x 1 + (4271230611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4491647431/10000000000 : ℝ)^1061 ≤ (17411506339127/50000000000000 : ℝ)^805 := by
    have hnat : (4491647431 : ℕ)^1061*50000000000000^805 ≤ 17411506339127^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4491647431 10000000000 17411506339127 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (533903817/1250000000 : ℝ)^1061 ≤ (8147123318731/25000000000000 : ℝ)^805 := by
    have hnat : (533903817 : ℕ)^1061*25000000000000^805 ≤ 8147123318731^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      533903817 1250000000 8147123318731 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4271230611/10000000000 : ℝ)^1061 ≤ (16294247014567/50000000000000 : ℝ)^805 := by
    have hnat : (4271230611 : ℕ)^1061*50000000000000^805 ≤ 16294247014567^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4271230611 10000000000 16294247014567 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4491647431/10000000000 : ℝ), (533903817/1250000000 : ℝ), (4271230611/10000000000 : ℝ)] ![(17411506339127/50000000000000 : ℝ), (8147123318731/25000000000000 : ℝ), (16294247014567/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4491647431/10000000000 : ℝ)|^1061 ≤ (17411506339127/50000000000000 : ℝ)^805
        have hw : |(4491647431/10000000000 : ℝ)|=(4491647431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(533903817/1250000000 : ℝ)|^1061 ≤ (8147123318731/25000000000000 : ℝ)^805
        have hw : |(533903817/1250000000 : ℝ)|=(533903817/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4271230611/10000000000 : ℝ)|^1061 ≤ (16294247014567/50000000000000 : ℝ)^805
        have hw : |(4271230611/10000000000 : ℝ)|=(4271230611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_4 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-1134970873/5000000000 : ℝ)*x 0 + (657934671/1250000000 : ℝ)*x 1 + (1052695167/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1134970873/5000000000 : ℝ)^1061 ≤ (14165091706011/100000000000000 : ℝ)^805 := by
    have hnat : (1134970873 : ℕ)^1061*100000000000000^805 ≤ 14165091706011^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1134970873 5000000000 14165091706011 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (657934671/1250000000 : ℝ)^1061 ≤ (21458731187773/50000000000000 : ℝ)^805 := by
    have hnat : (657934671 : ℕ)^1061*50000000000000^805 ≤ 21458731187773^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      657934671 1250000000 21458731187773 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1052695167/2000000000 : ℝ)^1061 ≤ (42917445900641/100000000000000 : ℝ)^805 := by
    have hnat : (1052695167 : ℕ)^1061*100000000000000^805 ≤ 42917445900641^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052695167 2000000000 42917445900641 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1134970873/5000000000 : ℝ), (657934671/1250000000 : ℝ), (1052695167/2000000000 : ℝ)] ![(14165091706011/100000000000000 : ℝ), (21458731187773/50000000000000 : ℝ), (42917445900641/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1134970873/5000000000 : ℝ)|^1061 ≤ (14165091706011/100000000000000 : ℝ)^805
        have hw : |(-1134970873/5000000000 : ℝ)|=(1134970873/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(657934671/1250000000 : ℝ)|^1061 ≤ (21458731187773/50000000000000 : ℝ)^805
        have hw : |(657934671/1250000000 : ℝ)|=(657934671/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1052695167/2000000000 : ℝ)|^1061 ≤ (42917445900641/100000000000000 : ℝ)^805
        have hw : |(1052695167/2000000000 : ℝ)|=(1052695167/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_5 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5374956753/10000000000 : ℝ)*x 0 + (-530558987/2500000000 : ℝ)*x 1 + (1315869427/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374956753/10000000000 : ℝ)^1061 ≤ (22059764461051/50000000000000 : ℝ)^805 := by
    have hnat : (5374956753 : ℕ)^1061*50000000000000^805 ≤ 22059764461051^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374956753 10000000000 22059764461051 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (530558987/2500000000 : ℝ)^1061 ≤ (810187814933/6250000000000 : ℝ)^805 := by
    have hnat : (530558987 : ℕ)^1061*6250000000000^805 ≤ 810187814933^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      530558987 2500000000 810187814933 6250000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1315869427/2500000000 : ℝ)^1061 ≤ (1341170813421/3125000000000 : ℝ)^805 := by
    have hnat : (1315869427 : ℕ)^1061*3125000000000^805 ≤ 1341170813421^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315869427 2500000000 1341170813421 3125000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374956753/10000000000 : ℝ), (-530558987/2500000000 : ℝ), (1315869427/2500000000 : ℝ)] ![(22059764461051/50000000000000 : ℝ), (810187814933/6250000000000 : ℝ), (1341170813421/3125000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374956753/10000000000 : ℝ)|^1061 ≤ (22059764461051/50000000000000 : ℝ)^805
        have hw : |(5374956753/10000000000 : ℝ)|=(5374956753/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-530558987/2500000000 : ℝ)|^1061 ≤ (810187814933/6250000000000 : ℝ)^805
        have hw : |(-530558987/2500000000 : ℝ)|=(530558987/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1315869427/2500000000 : ℝ)|^1061 ≤ (1341170813421/3125000000000 : ℝ)^805
        have hw : |(1315869427/2500000000 : ℝ)|=(1315869427/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_6 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (5374957217/10000000000 : ℝ)*x 0 + (1315869337/2500000000 : ℝ)*x 1 + (-424447161/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5374957217/10000000000 : ℝ)^1061 ≤ (22059766970991/50000000000000 : ℝ)^805 := by
    have hnat : (5374957217 : ℕ)^1061*50000000000000^805 ≤ 22059766970991^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5374957217 10000000000 22059766970991 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1315869337/2500000000 : ℝ)^1061 ≤ (42917462160609/100000000000000 : ℝ)^805 := by
    have hnat : (1315869337 : ℕ)^1061*100000000000000^805 ≤ 42917462160609^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1315869337 2500000000 42917462160609 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (424447161/2000000000 : ℝ)^1061 ≤ (3240750971921/25000000000000 : ℝ)^805 := by
    have hnat : (424447161 : ℕ)^1061*25000000000000^805 ≤ 3240750971921^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      424447161 2000000000 3240750971921 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5374957217/10000000000 : ℝ), (1315869337/2500000000 : ℝ), (-424447161/2000000000 : ℝ)] ![(22059766970991/50000000000000 : ℝ), (42917462160609/100000000000000 : ℝ), (3240750971921/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5374957217/10000000000 : ℝ)|^1061 ≤ (22059766970991/50000000000000 : ℝ)^805
        have hw : |(5374957217/10000000000 : ℝ)|=(5374957217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1315869337/2500000000 : ℝ)|^1061 ≤ (42917462160609/100000000000000 : ℝ)^805
        have hw : |(1315869337/2500000000 : ℝ)|=(1315869337/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-424447161/2000000000 : ℝ)|^1061 ≤ (3240750971921/25000000000000 : ℝ)^805
        have hw : |(-424447161/2000000000 : ℝ)|=(424447161/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_7 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4191553743/10000000000 : ℝ)*x 0 + (552652687/1250000000 : ℝ)*x 1 + (552652751/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4191553743/10000000000 : ℝ)^1061 ≤ (15894820019423/50000000000000 : ℝ)^805 := by
    have hnat : (4191553743 : ℕ)^1061*50000000000000^805 ≤ 15894820019423^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4191553743 10000000000 15894820019423 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552652687/1250000000 : ℝ)^1061 ≤ (34105177368359/100000000000000 : ℝ)^805 := by
    have hnat : (552652687 : ℕ)^1061*100000000000000^805 ≤ 34105177368359^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552652687 1250000000 34105177368359 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (552652751/1250000000 : ℝ)^1061 ≤ (34105182573919/100000000000000 : ℝ)^805 := by
    have hnat : (552652751 : ℕ)^1061*100000000000000^805 ≤ 34105182573919^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552652751 1250000000 34105182573919 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4191553743/10000000000 : ℝ), (552652687/1250000000 : ℝ), (552652751/1250000000 : ℝ)] ![(15894820019423/50000000000000 : ℝ), (34105177368359/100000000000000 : ℝ), (34105182573919/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4191553743/10000000000 : ℝ)|^1061 ≤ (15894820019423/50000000000000 : ℝ)^805
        have hw : |(4191553743/10000000000 : ℝ)|=(4191553743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552652687/1250000000 : ℝ)|^1061 ≤ (34105177368359/100000000000000 : ℝ)^805
        have hw : |(552652687/1250000000 : ℝ)|=(552652687/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(552652751/1250000000 : ℝ)|^1061 ≤ (34105182573919/100000000000000 : ℝ)^805
        have hw : |(552652751/1250000000 : ℝ)|=(552652751/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_8 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-549320157/2500000000 : ℝ)*x 0 + (5175048563/10000000000 : ℝ)*x 1 + (5406378297/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (549320157/2500000000 : ℝ)^1061 ≤ (13570534361533/100000000000000 : ℝ)^805 := by
    have hnat : (549320157 : ℕ)^1061*100000000000000^805 ≤ 13570534361533^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      549320157 2500000000 13570534361533 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5175048563/10000000000 : ℝ)^1061 ≤ (10492420155267/25000000000000 : ℝ)^805 := by
    have hnat : (5175048563 : ℕ)^1061*25000000000000^805 ≤ 10492420155267^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5175048563 10000000000 10492420155267 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5406378297/10000000000 : ℝ)^1061 ≤ (44459784997347/100000000000000 : ℝ)^805 := by
    have hnat : (5406378297 : ℕ)^1061*100000000000000^805 ≤ 44459784997347^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406378297 10000000000 44459784997347 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-549320157/2500000000 : ℝ), (5175048563/10000000000 : ℝ), (5406378297/10000000000 : ℝ)] ![(13570534361533/100000000000000 : ℝ), (10492420155267/25000000000000 : ℝ), (44459784997347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-549320157/2500000000 : ℝ)|^1061 ≤ (13570534361533/100000000000000 : ℝ)^805
        have hw : |(-549320157/2500000000 : ℝ)|=(549320157/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5175048563/10000000000 : ℝ)|^1061 ≤ (10492420155267/25000000000000 : ℝ)^805
        have hw : |(5175048563/10000000000 : ℝ)|=(5175048563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5406378297/10000000000 : ℝ)|^1061 ≤ (44459784997347/100000000000000 : ℝ)^805
        have hw : |(5406378297/10000000000 : ℝ)|=(5406378297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_9 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2637165339/5000000000 : ℝ)*x 0 + (-2065234921/10000000000 : ℝ)*x 1 + (1351594449/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637165339/5000000000 : ℝ)^1061 ≤ (21517069692511/50000000000000 : ℝ)^805 := by
    have hnat : (2637165339 : ℕ)^1061*50000000000000^805 ≤ 21517069692511^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637165339 5000000000 21517069692511 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2065234921/10000000000 : ℝ)^1061 ≤ (6253040518033/50000000000000 : ℝ)^805 := by
    have hnat : (2065234921 : ℕ)^1061*50000000000000^805 ≤ 6253040518033^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2065234921 10000000000 6253040518033 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351594449/2500000000 : ℝ)^1061 ≤ (22229889783559/50000000000000 : ℝ)^805 := by
    have hnat : (1351594449 : ℕ)^1061*50000000000000^805 ≤ 22229889783559^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351594449 2500000000 22229889783559 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637165339/5000000000 : ℝ), (-2065234921/10000000000 : ℝ), (1351594449/2500000000 : ℝ)] ![(21517069692511/50000000000000 : ℝ), (6253040518033/50000000000000 : ℝ), (22229889783559/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637165339/5000000000 : ℝ)|^1061 ≤ (21517069692511/50000000000000 : ℝ)^805
        have hw : |(2637165339/5000000000 : ℝ)|=(2637165339/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2065234921/10000000000 : ℝ)|^1061 ≤ (6253040518033/50000000000000 : ℝ)^805
        have hw : |(-2065234921/10000000000 : ℝ)|=(2065234921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351594449/2500000000 : ℝ)|^1061 ≤ (22229889783559/50000000000000 : ℝ)^805
        have hw : |(1351594449/2500000000 : ℝ)|=(1351594449/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_10 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (527433021/1000000000 : ℝ)*x 0 + (5406378417/10000000000 : ℝ)*x 1 + (-516308677/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (527433021/1000000000 : ℝ)^1061 ≤ (8606826870441/20000000000000 : ℝ)^805 := by
    have hnat : (527433021 : ℕ)^1061*20000000000000^805 ≤ 8606826870441^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      527433021 1000000000 8606826870441 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5406378417/10000000000 : ℝ)^1061 ≤ (44459786298001/100000000000000 : ℝ)^805 := by
    have hnat : (5406378417 : ℕ)^1061*100000000000000^805 ≤ 44459786298001^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5406378417 10000000000 44459786298001 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (516308677/2500000000 : ℝ)^1061 ≤ (12506079336059/100000000000000 : ℝ)^805 := by
    have hnat : (516308677 : ℕ)^1061*100000000000000^805 ≤ 12506079336059^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      516308677 2500000000 12506079336059 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(527433021/1000000000 : ℝ), (5406378417/10000000000 : ℝ), (-516308677/2500000000 : ℝ)] ![(8606826870441/20000000000000 : ℝ), (44459786298001/100000000000000 : ℝ), (12506079336059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(527433021/1000000000 : ℝ)|^1061 ≤ (8606826870441/20000000000000 : ℝ)^805
        have hw : |(527433021/1000000000 : ℝ)|=(527433021/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5406378417/10000000000 : ℝ)|^1061 ≤ (44459786298001/100000000000000 : ℝ)^805
        have hw : |(5406378417/10000000000 : ℝ)|=(5406378417/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-516308677/2500000000 : ℝ)|^1061 ≤ (12506079336059/100000000000000 : ℝ)^805
        have hw : |(-516308677/2500000000 : ℝ)|=(516308677/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_11 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4523783339/10000000000 : ℝ)*x 0 + (425487547/1000000000 : ℝ)*x 1 + (265929649/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4523783339/10000000000 : ℝ)^1061 ≤ (35151761150833/100000000000000 : ℝ)^805 := by
    have hnat : (4523783339 : ℕ)^1061*100000000000000^805 ≤ 35151761150833^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4523783339 10000000000 35151761150833 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (425487547/1000000000 : ℝ)^1061 ≤ (16212062435137/50000000000000 : ℝ)^805 := by
    have hnat : (425487547 : ℕ)^1061*50000000000000^805 ≤ 16212062435137^805*1000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      425487547 1000000000 16212062435137 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (265929649/625000000 : ℝ)^1061 ≤ (8106028490659/25000000000000 : ℝ)^805 := by
    have hnat : (265929649 : ℕ)^1061*25000000000000^805 ≤ 8106028490659^805*625000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265929649 625000000 8106028490659 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4523783339/10000000000 : ℝ), (425487547/1000000000 : ℝ), (265929649/625000000 : ℝ)] ![(35151761150833/100000000000000 : ℝ), (16212062435137/50000000000000 : ℝ), (8106028490659/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4523783339/10000000000 : ℝ)|^1061 ≤ (35151761150833/100000000000000 : ℝ)^805
        have hw : |(4523783339/10000000000 : ℝ)|=(4523783339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(425487547/1000000000 : ℝ)|^1061 ≤ (16212062435137/50000000000000 : ℝ)^805
        have hw : |(425487547/1000000000 : ℝ)|=(425487547/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(265929649/625000000 : ℝ)|^1061 ≤ (8106028490659/25000000000000 : ℝ)^805
        have hw : |(265929649/625000000 : ℝ)|=(265929649/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_12 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (-499066239/2500000000 : ℝ)*x 0 + (1369605787/2500000000 : ℝ)*x 1 + (5252462563/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (499066239/2500000000 : ℝ)^1061 ≤ (186852493649/1562500000000 : ℝ)^805 := by
    have hnat : (499066239 : ℕ)^1061*1562500000000^805 ≤ 186852493649^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      499066239 2500000000 186852493649 1562500000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1369605787/2500000000 : ℝ)^1061 ≤ (22621156479727/50000000000000 : ℝ)^805 := by
    have hnat : (1369605787 : ℕ)^1061*50000000000000^805 ≤ 22621156479727^805*2500000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1369605787 2500000000 22621156479727 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252462563/10000000000 : ℝ)^1061 ≤ (42799127437599/100000000000000 : ℝ)^805 := by
    have hnat : (5252462563 : ℕ)^1061*100000000000000^805 ≤ 42799127437599^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252462563 10000000000 42799127437599 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-499066239/2500000000 : ℝ), (1369605787/2500000000 : ℝ), (5252462563/10000000000 : ℝ)] ![(186852493649/1562500000000 : ℝ), (22621156479727/50000000000000 : ℝ), (42799127437599/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-499066239/2500000000 : ℝ)|^1061 ≤ (186852493649/1562500000000 : ℝ)^805
        have hw : |(-499066239/2500000000 : ℝ)|=(499066239/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1369605787/2500000000 : ℝ)|^1061 ≤ (22621156479727/50000000000000 : ℝ)^805
        have hw : |(1369605787/2500000000 : ℝ)|=(1369605787/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252462563/10000000000 : ℝ)|^1061 ≤ (42799127437599/100000000000000 : ℝ)^805
        have hw : |(5252462563/10000000000 : ℝ)|=(5252462563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_13 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (672838781/1250000000 : ℝ)*x 0 + (-2126512353/10000000000 : ℝ)*x 1 + (5252462343/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (672838781/1250000000 : ℝ)^1061 ≤ (44203430953751/100000000000000 : ℝ)^805 := by
    have hnat : (672838781 : ℕ)^1061*100000000000000^805 ≤ 44203430953751^805*1250000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      672838781 1250000000 44203430953751 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2126512353/10000000000 : ℝ)^1061 ≤ (6498721975339/50000000000000 : ℝ)^805 := by
    have hnat : (2126512353 : ℕ)^1061*50000000000000^805 ≤ 6498721975339^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2126512353 10000000000 6498721975339 50000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5252462343/10000000000 : ℝ)^1061 ≤ (42799125074869/100000000000000 : ℝ)^805 := by
    have hnat : (5252462343 : ℕ)^1061*100000000000000^805 ≤ 42799125074869^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5252462343 10000000000 42799125074869 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(672838781/1250000000 : ℝ), (-2126512353/10000000000 : ℝ), (5252462343/10000000000 : ℝ)] ![(44203430953751/100000000000000 : ℝ), (6498721975339/50000000000000 : ℝ), (42799125074869/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(672838781/1250000000 : ℝ)|^1061 ≤ (44203430953751/100000000000000 : ℝ)^805
        have hw : |(672838781/1250000000 : ℝ)|=(672838781/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2126512353/10000000000 : ℝ)|^1061 ≤ (6498721975339/50000000000000 : ℝ)^805
        have hw : |(-2126512353/10000000000 : ℝ)|=(2126512353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5252462343/10000000000 : ℝ)|^1061 ≤ (42799125074869/100000000000000 : ℝ)^805
        have hw : |(5252462343/10000000000 : ℝ)|=(5252462343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_14 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (2691355099/5000000000 : ℝ)*x 0 + (1050492509/2000000000 : ℝ)*x 1 + (-42530243/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2691355099/5000000000 : ℝ)^1061 ≤ (44203430412567/100000000000000 : ℝ)^805 := by
    have hnat : (2691355099 : ℕ)^1061*100000000000000^805 ≤ 44203430412567^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2691355099 5000000000 44203430412567 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1050492509/2000000000 : ℝ)^1061 ≤ (8559825448857/20000000000000 : ℝ)^805 := by
    have hnat : (1050492509 : ℕ)^1061*20000000000000^805 ≤ 8559825448857^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1050492509 2000000000 8559825448857 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42530243/200000000 : ℝ)^1061 ≤ (12997442315347/100000000000000 : ℝ)^805 := by
    have hnat : (42530243 : ℕ)^1061*100000000000000^805 ≤ 12997442315347^805*200000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42530243 200000000 12997442315347 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2691355099/5000000000 : ℝ), (1050492509/2000000000 : ℝ), (-42530243/200000000 : ℝ)] ![(44203430412567/100000000000000 : ℝ), (8559825448857/20000000000000 : ℝ), (12997442315347/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2691355099/5000000000 : ℝ)|^1061 ≤ (44203430412567/100000000000000 : ℝ)^805
        have hw : |(2691355099/5000000000 : ℝ)|=(2691355099/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1050492509/2000000000 : ℝ)|^1061 ≤ (8559825448857/20000000000000 : ℝ)^805
        have hw : |(1050492509/2000000000 : ℝ)|=(1050492509/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-42530243/200000000 : ℝ)|^1061 ≤ (12997442315347/100000000000000 : ℝ)^805
        have hw : |(-42530243/200000000 : ℝ)|=(42530243/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1284_box_15 (p : ℝ) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ)) (x : Fin 3 → ℝ) :
    (4165458209/10000000000 : ℝ)*x 0 + (886806347/2000000000 : ℝ)*x 1 + (2217015559/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4165458209/10000000000 : ℝ)^1061 ≤ (7882261343853/25000000000000 : ℝ)^805 := by
    have hnat : (4165458209 : ℕ)^1061*25000000000000^805 ≤ 7882261343853^805*10000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4165458209 10000000000 7882261343853 25000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (886806347/2000000000 : ℝ)^1061 ≤ (6847096089733/20000000000000 : ℝ)^805 := by
    have hnat : (886806347 : ℕ)^1061*20000000000000^805 ≤ 6847096089733^805*2000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      886806347 2000000000 6847096089733 20000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2217015559/5000000000 : ℝ)^1061 ≤ (34235474169783/100000000000000 : ℝ)^805 := by
    have hnat : (2217015559 : ℕ)^1061*100000000000000^805 ≤ 34235474169783^805*5000000000^1061 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2217015559 5000000000 34235474169783 100000000000000 1061 805 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (1061/256 : ℝ)) 1061 805 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4165458209/10000000000 : ℝ), (886806347/2000000000 : ℝ), (2217015559/5000000000 : ℝ)] ![(7882261343853/25000000000000 : ℝ), (6847096089733/20000000000000 : ℝ), (34235474169783/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4165458209/10000000000 : ℝ)|^1061 ≤ (7882261343853/25000000000000 : ℝ)^805
        have hw : |(4165458209/10000000000 : ℝ)|=(4165458209/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(886806347/2000000000 : ℝ)|^1061 ≤ (6847096089733/20000000000000 : ℝ)^805
        have hw : |(886806347/2000000000 : ℝ)|=(886806347/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2217015559/5000000000 : ℝ)|^1061 ≤ (34235474169783/100000000000000 : ℝ)^805
        have hw : |(2217015559/5000000000 : ℝ)|=(2217015559/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1284_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h) :
    -(62837/100000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(5883/10000 : ℝ) ∧ (9951/12500 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (84123/100000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7333/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (344/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7333/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (344/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7333/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (344/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7333/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (344/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7333/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (344/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7333/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (344/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (344/3125 : ℝ) ^ (4243/1024 : ℝ) ≤ (267427733774297/2500000000000000000 : ℝ) := by
    have hpowers : (344/3125 : ℝ)^4243 ≤ (267427733774297/2500000000000000000 : ℝ)^1024 := by
      have hnat : (344 : ℕ)^4243*2500000000000000000^1024 ≤ 267427733774297^1024*3125^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        344 3125 267427733774297 2500000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (344/3125 : ℝ)) (X := (267427733774297/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7333/50000 : ℝ) ^ (4243/1024 : ℝ) ≤ (8780249664576051/25000000000000000000 : ℝ) := by
    have hpowers : (7333/50000 : ℝ)^4243 ≤ (8780249664576051/25000000000000000000 : ℝ)^1024 := by
      have hnat : (7333 : ℕ)^4243*25000000000000000000^1024 ≤ 8780249664576051^1024*50000^4243 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7333 50000 8780249664576051 25000000000000000000 4243 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7333/50000 : ℝ)) (X := (8780249664576051/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1250267427733774297/1250000000000000000 : ℝ) ≤ (5000258141671691/5000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (1250267427733774297/1250000000000000000 : ℝ)^1024 ≤ (5000258141671691/5000000000000000 : ℝ)^4243 := by
      have hnat : (1250267427733774297 : ℕ)^1024*5000000000000000^4243 ≤ 5000258141671691^4243*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1250267427733774297 1250000000000000000 5000258141671691 5000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000258141671691/5000000000000000 : ℝ)) (X := (1250267427733774297/1250000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (25011454527002319021/25000000000000000000 : ℝ) ≤ (10001105576016671/10000000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (25011454527002319021/25000000000000000000 : ℝ)^1024 ≤ (10001105576016671/10000000000000000 : ℝ)^4243 := by
      have hnat : (25011454527002319021 : ℕ)^1024*10000000000000000^4243 ≤ 10001105576016671^4243*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25011454527002319021 25000000000000000000 10001105576016671 10000000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001105576016671/10000000000000000 : ℝ)) (X := (25011454527002319021/25000000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12508780249664576051/12500000000000000000 : ℝ) ≤ (250042371717249/250000000000000 : ℝ) ^ (4243/1024 : ℝ) := by
    have hpowers : (12508780249664576051/12500000000000000000 : ℝ)^1024 ≤ (250042371717249/250000000000000 : ℝ)^4243 := by
      have hnat : (12508780249664576051 : ℕ)^1024*250000000000000^4243 ≤ 250042371717249^4243*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12508780249664576051 12500000000000000000 250042371717249 250000000000000 1024 4243 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (250042371717249/250000000000000 : ℝ)) (X := (12508780249664576051/12500000000000000000 : ℝ)) (by norm_num) 4243 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(267427733774297/2500000000000000000 : ℝ) ≤ ((9142228674243740183/9145000000000000000 : ℝ)+2*(589292673289/365800000000000 : ℝ)*(344/3125 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (9142228674243740183/9145000000000000000 : ℝ)+2*(589292673289/365800000000000 : ℝ)*(344/3125 : ℝ)=(5000258141671691/5000000000000000 : ℝ) by norm_num, show 1+2*(267427733774297/2500000000000000000 : ℝ)=(1250267427733774297/1250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(8780249664576051/25000000000000000000 : ℝ)+(267427733774297/2500000000000000000 : ℝ) ≤ ((9142228674243740183/9145000000000000000 : ℝ)+(589292673289/365800000000000 : ℝ)*((7333/50000 : ℝ)+(344/3125 : ℝ)))^(4243/1024 : ℝ) := by
    rw [show (9142228674243740183/9145000000000000000 : ℝ)+(589292673289/365800000000000 : ℝ)*((7333/50000 : ℝ)+(344/3125 : ℝ))=(10001105576016671/10000000000000000 : ℝ) by norm_num, show 1+(8780249664576051/25000000000000000000 : ℝ)+(267427733774297/2500000000000000000 : ℝ)=(25011454527002319021/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(8780249664576051/25000000000000000000 : ℝ) ≤ ((9142228674243740183/9145000000000000000 : ℝ)+2*(589292673289/365800000000000 : ℝ)*(7333/50000 : ℝ))^(4243/1024 : ℝ) := by
    rw [show (9142228674243740183/9145000000000000000 : ℝ)+2*(589292673289/365800000000000 : ℝ)*(7333/50000 : ℝ)=(250042371717249/250000000000000 : ℝ) by norm_num, show 1+2*(8780249664576051/25000000000000000000 : ℝ)=(12508780249664576051/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (9142228674243740183/9145000000000000000 : ℝ)*(X 1 0+X 2 0)+(589292673289/365800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (344/3125 : ℝ)) (hi := (7333/50000 : ℝ)) (c := (9142228674243740183/9145000000000000000 : ℝ)) (alpha := (589292673289/365800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (9142228674243740183/9145000000000000000 : ℝ)*(X 0 1+X 2 1)+(589292673289/365800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (344/3125 : ℝ)) (hi := (7333/50000 : ℝ)) (c := (9142228674243740183/9145000000000000000 : ℝ)) (alpha := (589292673289/365800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (9142228674243740183/9145000000000000000 : ℝ)*(X 0 2+X 1 2)+(589292673289/365800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4243/1024 : ℝ)) (lo := (344/3125 : ℝ)) (hi := (7333/50000 : ℝ)) (c := (9142228674243740183/9145000000000000000 : ℝ)) (alpha := (589292673289/365800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1923148497/10000000000 : ℝ)*X 0 0+(5392338469/10000000000 : ℝ)*X 0 1+(5392338019/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5284222581/10000000000 : ℝ)*X 1 0+(-2070958379/10000000000 : ℝ)*X 1 1+(5392338261/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2642111401/5000000000 : ℝ)*X 2 0+(215693531/400000000 : ℝ)*X 2 1+(-2070958061/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4491647431/10000000000 : ℝ)*X 0 0+(533903817/1250000000 : ℝ)*X 0 1+(4271230611/10000000000 : ℝ)*X 0 2+(4491647431/10000000000 : ℝ)*X 1 0+(533903817/1250000000 : ℝ)*X 1 1+(4271230611/10000000000 : ℝ)*X 1 2+(4491647431/10000000000 : ℝ)*X 2 0+(533903817/1250000000 : ℝ)*X 2 1+(4271230611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1134970873/5000000000 : ℝ)*X 0 0+(657934671/1250000000 : ℝ)*X 0 1+(1052695167/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5374956753/10000000000 : ℝ)*X 1 0+(-530558987/2500000000 : ℝ)*X 1 1+(1315869427/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5374957217/10000000000 : ℝ)*X 2 0+(1315869337/2500000000 : ℝ)*X 2 1+(-424447161/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4191553743/10000000000 : ℝ)*X 0 0+(552652687/1250000000 : ℝ)*X 0 1+(552652751/1250000000 : ℝ)*X 0 2+(4191553743/10000000000 : ℝ)*X 1 0+(552652687/1250000000 : ℝ)*X 1 1+(552652751/1250000000 : ℝ)*X 1 2+(4191553743/10000000000 : ℝ)*X 2 0+(552652687/1250000000 : ℝ)*X 2 1+(552652751/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-549320157/2500000000 : ℝ)*X 0 0+(5175048563/10000000000 : ℝ)*X 0 1+(5406378297/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((2637165339/5000000000 : ℝ)*X 1 0+(-2065234921/10000000000 : ℝ)*X 1 1+(1351594449/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((527433021/1000000000 : ℝ)*X 2 0+(5406378417/10000000000 : ℝ)*X 2 1+(-516308677/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4523783339/10000000000 : ℝ)*X 0 0+(425487547/1000000000 : ℝ)*X 0 1+(265929649/625000000 : ℝ)*X 0 2+(4523783339/10000000000 : ℝ)*X 1 0+(425487547/1000000000 : ℝ)*X 1 1+(265929649/625000000 : ℝ)*X 1 2+(4523783339/10000000000 : ℝ)*X 2 0+(425487547/1000000000 : ℝ)*X 2 1+(265929649/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-499066239/2500000000 : ℝ)*X 0 0+(1369605787/2500000000 : ℝ)*X 0 1+(5252462563/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((672838781/1250000000 : ℝ)*X 1 0+(-2126512353/10000000000 : ℝ)*X 1 1+(5252462343/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((2691355099/5000000000 : ℝ)*X 2 0+(1050492509/2000000000 : ℝ)*X 2 1+(-42530243/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4165458209/10000000000 : ℝ)*X 0 0+(886806347/2000000000 : ℝ)*X 0 1+(2217015559/5000000000 : ℝ)*X 0 2+(4165458209/10000000000 : ℝ)*X 1 0+(886806347/2000000000 : ℝ)*X 1 1+(2217015559/5000000000 : ℝ)*X 1 2+(4165458209/10000000000 : ℝ)*X 2 0+(886806347/2000000000 : ℝ)*X 2 1+(2217015559/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1284_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-62837/100000 : ℝ) ≤ (-14365601499190493498000780933361/22862500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2016587/12500000000000 : ℝ)*(upper1) + (978393/3125000000000 : ℝ)*(upper4) + (124331259/50000000000000 : ℝ)*(upper5) + (285504998808089/10000000000000 : ℝ)*(major0) + (285504998808089/10000000000000 : ℝ)*(major1) + (285504998808089/10000000000000 : ℝ)*(major2) + (13373187721/100000000000000 : ℝ)*(sp3) + (3858206234978759/100000000000000 : ℝ)*(sp4) + (1929004948452939/50000000000000 : ℝ)*(sp5) + (120568762711407/3125000000000 : ℝ)*(sp6) + (1872791347373611/100000000000000 : ℝ)*(sp7) + (33947174173/100000000000000 : ℝ)*(sp8) + (46057049411/20000000000000 : ℝ)*(sp13) + (9943846977/25000000000000 : ℝ)*(sp14) + (468201180140333/25000000000000 : ℝ)*(f.failure) + (964560045538233/25000000000000 : ℝ)*(f.sum) + (4570306553193/1829000000000000000000000000 : ℝ)*base66 + (762495948869415287/91450000000000000000000000000000 : ℝ)*base67 + (794202547093515287/91450000000000000000000000000000 : ℝ)*base69 + (658087092920665287/91450000000000000000000000000000 : ℝ)*base71 + (113142683879/457250000000000000000000000 : ℝ)*base74 + (5564771523834713/91450000000000000000000000000000 : ℝ)*base76 + (1184139480484565287/91450000000000000000000000000000 : ℝ)*base77 + (803923484652965287/91450000000000000000000000000000 : ℝ)*base79 + (72820382971/36580000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (9935607/2500000000000000000000 : ℝ)*base90 + (9935607/2500000000000000000000 : ℝ)*base92 + (9935607/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (5883/10000 : ℝ) ≤ (134505673301705237530205916418047/228625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (7379609/10000000000000 : ℝ)*(upper0) + (4213669/20000000000000 : ℝ)*(lower1) + (40948793/25000000000000 : ℝ)*(upper4) + (1460901003066201/50000000000000 : ℝ)*(major0) + (1460901003066201/50000000000000 : ℝ)*(major1) + (1460901003066201/50000000000000 : ℝ)*(major2) + (1953696831098421/50000000000000 : ℝ)*(sp0) + (1953698425350991/50000000000000 : ℝ)*(sp1) + (488423539467509/12500000000000 : ℝ)*(sp2) + (958295000941957/50000000000000 : ℝ)*(sp3) + (4829504887/100000000000000 : ℝ)*(sp5) + (13364466797/100000000000000 : ℝ)*(sp6) + (757884403/50000000000000 : ℝ)*(sp7) + (8018010027/100000000000000 : ℝ)*(sp8) + (23957393970659/1250000000000 : ℝ)*(f.failure) + (3907401680206869/100000000000000 : ℝ)*(f.sum) + (27244740604599/9145000000000000000000000000 : ℝ)*base65 + (521415233427670217/457250000000000000000000000000000 : ℝ)*base68 + (3139805295942670217/457250000000000000000000000000000 : ℝ)*base70 + (2265808192756170217/457250000000000000000000000000000 : ℝ)*base72 + (203452555389681/9145000000000000000000000000 : ℝ)*base74 + (1479609321429920217/457250000000000000000000000000000 : ℝ)*base76 + (2652887802996170217/457250000000000000000000000000000 : ℝ)*base78 + (18258880760990920217/457250000000000000000000000000000 : ℝ)*base80 + (9753075493991/2286250000000000000000000000 : ℝ)*base81 + (15961/125000000000000000000 : ℝ)*base90 + (15961/125000000000000000000 : ℝ)*base92 + (15961/125000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (9951/12500 : ℝ) ≤ (11742534748092500423334396038781/14750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1385673/781250000000 : ℝ)*(upper0) + (419203827/100000000000000 : ℝ)*(upper1) + (5891051/25000000000000 : ℝ)*(upper2) + (3236068566109239/100000000000000 : ℝ)*(major0) + (3236068566109239/100000000000000 : ℝ)*(major1) + (3236068566109239/100000000000000 : ℝ)*(major2) + (164787777319/50000000000000 : ℝ)*(sp1) + (510239047591/100000000000000 : ℝ)*(sp2) + (98156677151/100000000000000 : ℝ)*(sp3) + (18199847747/100000000000000 : ℝ)*(sp4) + (216142182277501/5000000000000 : ℝ)*(sp8) + (432253226984313/10000000000000 : ℝ)*(sp9) + (135073487698443/3125000000000 : ℝ)*(sp10) + (424528065690589/20000000000000 : ℝ)*(sp11) + (424547697026019/20000000000000 : ℝ)*(f.failure) + (540357730674721/12500000000000 : ℝ)*(f.sum) + (3922212870419/590000000000000000000000000 : ℝ)*base66 + (83919698229987927/29500000000000000000000000000000 : ℝ)*base67 + (4830594001987927/29500000000000000000000000000000 : ℝ)*base69 + (316244911124012073/29500000000000000000000000000000 : ℝ)*base72 + (14924502904981/590000000000000000000000000 : ℝ)*base73 + (214913027231512073/29500000000000000000000000000000 : ℝ)*base76 + (130854052782012073/29500000000000000000000000000000 : ℝ)*base78 + (106074631719512073/29500000000000000000000000000000 : ℝ)*base80 + (3504768322539/590000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base88 + (3145401/2000000000000000000000 : ℝ)*base90 + (3145401/2000000000000000000000 : ℝ)*base92 + (3145401/2000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (-84123/100000 : ℝ) ≤ (-192320132513453940621767258600013/228625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (83066757/100000000000000 : ℝ)*(lower0) + (40049929/50000000000000 : ℝ)*(lower2) + (15893219/100000000000000 : ℝ)*(upper3) + (1635933601008221/50000000000000 : ℝ)*(major0) + (1635933601008221/50000000000000 : ℝ)*(major1) + (1635933601008221/50000000000000 : ℝ)*(major2) + (8337991341/100000000000000 : ℝ)*(sp0) + (208693428783/100000000000000 : ℝ)*(sp5) + (76851369051/100000000000000 : ℝ)*(sp6) + (5085077721/12500000000000 : ℝ)*(sp7) + (1106386286231129/25000000000000 : ℝ)*(sp12) + (2212672394743537/50000000000000 : ℝ)*(sp13) + (2212738315773403/50000000000000 : ℝ)*(sp14) + (1073090177292527/50000000000000 : ℝ)*(sp15) + (1073110517603411/50000000000000 : ℝ)*(f.failure) + (2212776741457929/50000000000000 : ℝ)*(f.sum) + (1235350789001/2286250000000000000000000000 : ℝ)*base65 + (1640785187390980557/457250000000000000000000000000000 : ℝ)*base68 + (4149286848503980557/457250000000000000000000000000000 : ℝ)*base70 + (2303310691449480557/457250000000000000000000000000000 : ℝ)*base72 + (130565929105129/9145000000000000000000000000 : ℝ)*base73 + (1386735874306730557/457250000000000000000000000000000 : ℝ)*base76 + (1562411462853480557/457250000000000000000000000000000 : ℝ)*base78 + (6773802686068230557/457250000000000000000000000000000 : ℝ)*base80 + (4747130414631/2286250000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (49117431/5000000000000000000000 : ℝ)*base89 + (49117431/5000000000000000000000 : ℝ)*base91 + (49117431/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1284_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62837/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5883/10000 : ℝ) else (9951/12500 : ℝ) ≤ X j i ∧ X j i ≤ (84123/100000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1284_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1284_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62837/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5883/10000 : ℝ) else (9951/12500 : ℝ) ≤ X j i ∧ X j i ≤ (84123/100000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1284_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4243/1024 : ℝ) ≤ p) (hpb : p ≤ (1061/256 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (152447821/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7333/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (344/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(62837/100000 : ℝ) ≤ X j i ∧ X j i ≤ -(5883/10000 : ℝ) else (9951/12500 : ℝ) ≤ X j i ∧ X j i ≤ (84123/100000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1284_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
