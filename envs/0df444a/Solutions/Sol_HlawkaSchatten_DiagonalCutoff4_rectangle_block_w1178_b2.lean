-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1178_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:48:28.994996+00:00
-- url     : https://prove2.me/submissions/3138b121-fc80-45c0-bc3e-0020385d7b5c

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
theorem support_rectangle_w1178_s6_0 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-429952361/2000000000 : ℝ)*x 0 + (5392663921/10000000000 : ℝ)*x 1 + (5266035887/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (429952361/2000000000 : ℝ)^8371 ≤ (3266582740561/25000000000000 : ℝ)^6323 := by
    have hnat : (429952361 : ℕ)^8371*25000000000000^6323 ≤ 3266582740561^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      429952361 2000000000 3266582740561 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392663921/10000000000 : ℝ)^8371 ≤ (44150466585867/100000000000000 : ℝ)^6323 := by
    have hnat : (5392663921 : ℕ)^8371*100000000000000^6323 ≤ 44150466585867^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392663921 10000000000 44150466585867 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266035887/10000000000 : ℝ)^8371 ≤ (10695800611539/25000000000000 : ℝ)^6323 := by
    have hnat : (5266035887 : ℕ)^8371*25000000000000^6323 ≤ 10695800611539^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266035887 10000000000 10695800611539 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-429952361/2000000000 : ℝ), (5392663921/10000000000 : ℝ), (5266035887/10000000000 : ℝ)] ![(3266582740561/25000000000000 : ℝ), (44150466585867/100000000000000 : ℝ), (10695800611539/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-429952361/2000000000 : ℝ)|^8371 ≤ (3266582740561/25000000000000 : ℝ)^6323
        have hw : |(-429952361/2000000000 : ℝ)|=(429952361/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392663921/10000000000 : ℝ)|^8371 ≤ (44150466585867/100000000000000 : ℝ)^6323
        have hw : |(5392663921/10000000000 : ℝ)|=(5392663921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266035887/10000000000 : ℝ)|^8371 ≤ (10695800611539/25000000000000 : ℝ)^6323
        have hw : |(5266035887/10000000000 : ℝ)|=(5266035887/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s6_1 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5344686989/10000000000 : ℝ)*x 0 + (-2213984869/10000000000 : ℝ)*x 1 + (1053207187/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344686989/10000000000 : ℝ)^8371 ≤ (10907799775579/25000000000000 : ℝ)^6323 := by
    have hnat : (5344686989 : ℕ)^8371*25000000000000^6323 ≤ 10907799775579^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344686989 10000000000 10907799775579 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2213984869/10000000000 : ℝ)^8371 ≤ (13585597927297/100000000000000 : ℝ)^6323 := by
    have hnat : (2213984869 : ℕ)^8371*100000000000000^6323 ≤ 13585597927297^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2213984869 10000000000 13585597927297 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053207187/2000000000 : ℝ)^8371 ≤ (10695800740609/25000000000000 : ℝ)^6323 := by
    have hnat : (1053207187 : ℕ)^8371*25000000000000^6323 ≤ 10695800740609^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053207187 2000000000 10695800740609 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344686989/10000000000 : ℝ), (-2213984869/10000000000 : ℝ), (1053207187/2000000000 : ℝ)] ![(10907799775579/25000000000000 : ℝ), (13585597927297/100000000000000 : ℝ), (10695800740609/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344686989/10000000000 : ℝ)|^8371 ≤ (10907799775579/25000000000000 : ℝ)^6323
        have hw : |(5344686989/10000000000 : ℝ)|=(5344686989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2213984869/10000000000 : ℝ)|^8371 ≤ (13585597927297/100000000000000 : ℝ)^6323
        have hw : |(-2213984869/10000000000 : ℝ)|=(2213984869/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053207187/2000000000 : ℝ)|^8371 ≤ (10695800740609/25000000000000 : ℝ)^6323
        have hw : |(1053207187/2000000000 : ℝ)|=(1053207187/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s6_2 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1068937421/2000000000 : ℝ)*x 0 + (5266035757/10000000000 : ℝ)*x 1 + (-44279699/200000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1068937421/2000000000 : ℝ)^8371 ≤ (43631200355997/100000000000000 : ℝ)^6323 := by
    have hnat : (1068937421 : ℕ)^8371*100000000000000^6323 ≤ 43631200355997^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1068937421 2000000000 43631200355997 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266035757/10000000000 : ℝ)^8371 ≤ (42783201047899/100000000000000 : ℝ)^6323 := by
    have hnat : (5266035757 : ℕ)^8371*100000000000000^6323 ≤ 42783201047899^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266035757 10000000000 42783201047899 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (44279699/200000000 : ℝ)^8371 ≤ (3396399646331/25000000000000 : ℝ)^6323 := by
    have hnat : (44279699 : ℕ)^8371*25000000000000^6323 ≤ 3396399646331^6323*200000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      44279699 200000000 3396399646331 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1068937421/2000000000 : ℝ), (5266035757/10000000000 : ℝ), (-44279699/200000000 : ℝ)] ![(43631200355997/100000000000000 : ℝ), (42783201047899/100000000000000 : ℝ), (3396399646331/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1068937421/2000000000 : ℝ)|^8371 ≤ (43631200355997/100000000000000 : ℝ)^6323
        have hw : |(1068937421/2000000000 : ℝ)|=(1068937421/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266035757/10000000000 : ℝ)|^8371 ≤ (42783201047899/100000000000000 : ℝ)^6323
        have hw : |(5266035757/10000000000 : ℝ)|=(5266035757/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-44279699/200000000 : ℝ)|^8371 ≤ (3396399646331/25000000000000 : ℝ)^6323
        have hw : |(-44279699/200000000 : ℝ)|=(44279699/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s6_3 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179806137/5000000000 : ℝ)*x 0 + (4234581129/10000000000 : ℝ)*x 1 + (179531399/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179806137/5000000000 : ℝ)^8371 ≤ (333170203393/1000000000000 : ℝ)^6323 := by
    have hnat : (2179806137 : ℕ)^8371*1000000000000^6323 ≤ 333170203393^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179806137 5000000000 333170203393 1000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4234581129/10000000000 : ℝ)^8371 ≤ (2003620862687/6250000000000 : ℝ)^6323 := by
    have hnat : (4234581129 : ℕ)^8371*6250000000000^6323 ≤ 2003620862687^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4234581129 10000000000 2003620862687 6250000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (179531399/400000000 : ℝ)^8371 ≤ (8656261460701/25000000000000 : ℝ)^6323 := by
    have hnat : (179531399 : ℕ)^8371*25000000000000^6323 ≤ 8656261460701^6323*400000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179531399 400000000 8656261460701 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179806137/5000000000 : ℝ), (4234581129/10000000000 : ℝ), (179531399/400000000 : ℝ)] ![(333170203393/1000000000000 : ℝ), (2003620862687/6250000000000 : ℝ), (8656261460701/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179806137/5000000000 : ℝ)|^8371 ≤ (333170203393/1000000000000 : ℝ)^6323
        have hw : |(2179806137/5000000000 : ℝ)|=(2179806137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4234581129/10000000000 : ℝ)|^8371 ≤ (2003620862687/6250000000000 : ℝ)^6323
        have hw : |(4234581129/10000000000 : ℝ)|=(4234581129/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(179531399/400000000 : ℝ)|^8371 ≤ (8656261460701/25000000000000 : ℝ)^6323
        have hw : |(179531399/400000000 : ℝ)|=(179531399/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s6_4 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-214976673/1000000000 : ℝ)*x 0 + (1316588943/2500000000 : ℝ)*x 1 + (215693713/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214976673/1000000000 : ℝ)^8371 ≤ (522654823689/4000000000000 : ℝ)^6323 := by
    have hnat : (214976673 : ℕ)^8371*4000000000000^6323 ≤ 522654823689^6323*1000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214976673 1000000000 522654823689 4000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1316588943/2500000000 : ℝ)^8371 ≤ (42786643106353/100000000000000 : ℝ)^6323 := by
    have hnat : (1316588943 : ℕ)^8371*100000000000000^6323 ≤ 42786643106353^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316588943 2500000000 42786643106353 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (215693713/400000000 : ℝ)^8371 ≤ (44146986284837/100000000000000 : ℝ)^6323 := by
    have hnat : (215693713 : ℕ)^8371*100000000000000^6323 ≤ 44146986284837^6323*400000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215693713 400000000 44146986284837 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214976673/1000000000 : ℝ), (1316588943/2500000000 : ℝ), (215693713/400000000 : ℝ)] ![(522654823689/4000000000000 : ℝ), (42786643106353/100000000000000 : ℝ), (44146986284837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214976673/1000000000 : ℝ)|^8371 ≤ (522654823689/4000000000000 : ℝ)^6323
        have hw : |(-214976673/1000000000 : ℝ)|=(214976673/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1316588943/2500000000 : ℝ)|^8371 ≤ (42786643106353/100000000000000 : ℝ)^6323
        have hw : |(1316588943/2500000000 : ℝ)|=(1316588943/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(215693713/400000000 : ℝ)|^8371 ≤ (44146986284837/100000000000000 : ℝ)^6323
        have hw : |(215693713/400000000 : ℝ)|=(215693713/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s6_5 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312520939/10000000000 : ℝ)*x 0 + (-41753557/200000000 : ℝ)*x 1 + (2696171443/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312520939/10000000000 : ℝ)^8371 ≤ (10820975193171/25000000000000 : ℝ)^6323 := by
    have hnat : (5312520939 : ℕ)^8371*25000000000000^6323 ≤ 10820975193171^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312520939 10000000000 10820975193171 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (41753557/200000000 : ℝ)^8371 ≤ (314227806687/2500000000000 : ℝ)^6323 := by
    have hnat : (41753557 : ℕ)^8371*2500000000000^6323 ≤ 314227806687^6323*200000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      41753557 200000000 314227806687 2500000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696171443/5000000000 : ℝ)^8371 ≤ (44146986945999/100000000000000 : ℝ)^6323 := by
    have hnat : (2696171443 : ℕ)^8371*100000000000000^6323 ≤ 44146986945999^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696171443 5000000000 44146986945999 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312520939/10000000000 : ℝ), (-41753557/200000000 : ℝ), (2696171443/5000000000 : ℝ)] ![(10820975193171/25000000000000 : ℝ), (314227806687/2500000000000 : ℝ), (44146986945999/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312520939/10000000000 : ℝ)|^8371 ≤ (10820975193171/25000000000000 : ℝ)^6323
        have hw : |(5312520939/10000000000 : ℝ)|=(5312520939/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-41753557/200000000 : ℝ)|^8371 ≤ (314227806687/2500000000000 : ℝ)^6323
        have hw : |(-41753557/200000000 : ℝ)|=(41753557/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696171443/5000000000 : ℝ)|^8371 ≤ (44146986945999/100000000000000 : ℝ)^6323
        have hw : |(2696171443/5000000000 : ℝ)|=(2696171443/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s6_6 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1062504189/2000000000 : ℝ)*x 0 + (539234291/1000000000 : ℝ)*x 1 + (-208767781/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1062504189/2000000000 : ℝ)^8371 ≤ (43283900837403/100000000000000 : ℝ)^6323 := by
    have hnat : (1062504189 : ℕ)^8371*100000000000000^6323 ≤ 43283900837403^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1062504189 2000000000 43283900837403 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539234291/1000000000 : ℝ)^8371 ≤ (2759186700383/6250000000000 : ℝ)^6323 := by
    have hnat : (539234291 : ℕ)^8371*6250000000000^6323 ≤ 2759186700383^6323*1000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539234291 1000000000 2759186700383 6250000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (208767781/1000000000 : ℝ)^8371 ≤ (3142277987163/25000000000000 : ℝ)^6323 := by
    have hnat : (208767781 : ℕ)^8371*25000000000000^6323 ≤ 3142277987163^6323*1000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      208767781 1000000000 3142277987163 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1062504189/2000000000 : ℝ), (539234291/1000000000 : ℝ), (-208767781/1000000000 : ℝ)] ![(43283900837403/100000000000000 : ℝ), (2759186700383/6250000000000 : ℝ), (3142277987163/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1062504189/2000000000 : ℝ)|^8371 ≤ (43283900837403/100000000000000 : ℝ)^6323
        have hw : |(1062504189/2000000000 : ℝ)|=(1062504189/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539234291/1000000000 : ℝ)|^8371 ≤ (2759186700383/6250000000000 : ℝ)^6323
        have hw : |(539234291/1000000000 : ℝ)|=(539234291/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-208767781/1000000000 : ℝ)|^8371 ≤ (3142277987163/25000000000000 : ℝ)^6323
        have hw : |(-208767781/1000000000 : ℝ)|=(208767781/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s6_7 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359621839/10000000000 : ℝ)*x 0 + (4487643923/10000000000 : ℝ)*x 1 + (423522469/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359621839/10000000000 : ℝ)^8371 ≤ (33317117113051/100000000000000 : ℝ)^6323 := by
    have hnat : (4359621839 : ℕ)^8371*100000000000000^6323 ≤ 33317117113051^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359621839 10000000000 33317117113051 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4487643923/10000000000 : ℝ)^8371 ≤ (17309249383971/50000000000000 : ℝ)^6323 := by
    have hnat : (4487643923 : ℕ)^8371*50000000000000^6323 ≤ 17309249383971^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487643923 10000000000 17309249383971 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (423522469/1000000000 : ℝ)^8371 ≤ (32064384098873/100000000000000 : ℝ)^6323 := by
    have hnat : (423522469 : ℕ)^8371*100000000000000^6323 ≤ 32064384098873^6323*1000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423522469 1000000000 32064384098873 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359621839/10000000000 : ℝ), (4487643923/10000000000 : ℝ), (423522469/1000000000 : ℝ)] ![(33317117113051/100000000000000 : ℝ), (17309249383971/50000000000000 : ℝ), (32064384098873/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359621839/10000000000 : ℝ)|^8371 ≤ (33317117113051/100000000000000 : ℝ)^6323
        have hw : |(4359621839/10000000000 : ℝ)|=(4359621839/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4487643923/10000000000 : ℝ)|^8371 ≤ (17309249383971/50000000000000 : ℝ)^6323
        have hw : |(4487643923/10000000000 : ℝ)|=(4487643923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(423522469/1000000000 : ℝ)|^8371 ≤ (32064384098873/100000000000000 : ℝ)^6323
        have hw : |(423522469/1000000000 : ℝ)|=(423522469/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1178_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5697/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (3519/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11367/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1763/12500 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11367/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1763/12500 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11367/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11367/100000 : ℝ) ^ (4185/1024 : ℝ) ≤ (3454982038224807/25000000000000000000 : ℝ) := by
    have hpowers : (11367/100000 : ℝ)^4185 ≤ (3454982038224807/25000000000000000000 : ℝ)^1024 := by
      have hnat : (11367 : ℕ)^4185*25000000000000000000^1024 ≤ 3454982038224807^1024*100000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11367 100000 3454982038224807 25000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11367/100000 : ℝ)) (X := (3454982038224807/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1763/12500 : ℝ) ^ (4185/1024 : ℝ) ≤ (3337606100852547/10000000000000000000 : ℝ) := by
    have hpowers : (1763/12500 : ℝ)^4185 ≤ (3337606100852547/10000000000000000000 : ℝ)^1024 := by
      have hnat : (1763 : ℕ)^4185*10000000000000000000^1024 ≤ 3337606100852547^1024*12500^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1763 12500 3337606100852547 10000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1763/12500 : ℝ)) (X := (3337606100852547/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (12503454982038224807/12500000000000000000 : ℝ) ≤ (2500169057699679/2500000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (12503454982038224807/12500000000000000000 : ℝ)^1024 ≤ (2500169057699679/2500000000000000 : ℝ)^4185 := by
      have hnat : (12503454982038224807 : ℕ)^1024*2500000000000000^4185 ≤ 2500169057699679^4185*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12503454982038224807 12500000000000000000 2500169057699679 2500000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500169057699679/2500000000000000 : ℝ)) (X := (12503454982038224807/12500000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023597994580712349/50000000000000000000 : ℝ) ≤ (2000230920340233/2000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (50023597994580712349/50000000000000000000 : ℝ)^1024 ≤ (2000230920340233/2000000000000000 : ℝ)^4185 := by
      have hnat : (50023597994580712349 : ℕ)^1024*2000000000000000^4185 ≤ 2000230920340233^4185*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023597994580712349 50000000000000000000 2000230920340233 2000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000230920340233/2000000000000000 : ℝ)) (X := (50023597994580712349/50000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (5003337606100852547/5000000000000000000 : ℝ) ≤ (5000816486301807/5000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (5003337606100852547/5000000000000000000 : ℝ)^1024 ≤ (5000816486301807/5000000000000000 : ℝ)^4185 := by
      have hnat : (5003337606100852547 : ℕ)^1024*5000000000000000^4185 ≤ 5000816486301807^4185*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5003337606100852547 5000000000000000000 5000816486301807 5000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000816486301807/5000000000000000 : ℝ)) (X := (5003337606100852547/5000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(3454982038224807/25000000000000000000 : ℝ) ≤ ((13680487779799905063/13685000000000000000 : ℝ)+2*(478370902449/273700000000000 : ℝ)*(11367/100000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (13680487779799905063/13685000000000000000 : ℝ)+2*(478370902449/273700000000000 : ℝ)*(11367/100000 : ℝ)=(2500169057699679/2500000000000000 : ℝ) by norm_num, show 1+2*(3454982038224807/25000000000000000000 : ℝ)=(12503454982038224807/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(3337606100852547/10000000000000000000 : ℝ)+(3454982038224807/25000000000000000000 : ℝ) ≤ ((13680487779799905063/13685000000000000000 : ℝ)+(478370902449/273700000000000 : ℝ)*((1763/12500 : ℝ)+(11367/100000 : ℝ)))^(4185/1024 : ℝ) := by
    rw [show (13680487779799905063/13685000000000000000 : ℝ)+(478370902449/273700000000000 : ℝ)*((1763/12500 : ℝ)+(11367/100000 : ℝ))=(2000230920340233/2000000000000000 : ℝ) by norm_num, show 1+(3337606100852547/10000000000000000000 : ℝ)+(3454982038224807/25000000000000000000 : ℝ)=(50023597994580712349/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(3337606100852547/10000000000000000000 : ℝ) ≤ ((13680487779799905063/13685000000000000000 : ℝ)+2*(478370902449/273700000000000 : ℝ)*(1763/12500 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (13680487779799905063/13685000000000000000 : ℝ)+2*(478370902449/273700000000000 : ℝ)*(1763/12500 : ℝ)=(5000816486301807/5000000000000000 : ℝ) by norm_num, show 1+2*(3337606100852547/10000000000000000000 : ℝ)=(5003337606100852547/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13680487779799905063/13685000000000000000 : ℝ)*(X 1 0+X 2 0)+(478370902449/273700000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (13680487779799905063/13685000000000000000 : ℝ)) (alpha := (478370902449/273700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13680487779799905063/13685000000000000000 : ℝ)*(X 0 1+X 2 1)+(478370902449/273700000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (13680487779799905063/13685000000000000000 : ℝ)) (alpha := (478370902449/273700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13680487779799905063/13685000000000000000 : ℝ)*(X 0 2+X 1 2)+(478370902449/273700000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (11367/100000 : ℝ)) (hi := (1763/12500 : ℝ)) (c := (13680487779799905063/13685000000000000000 : ℝ)) (alpha := (478370902449/273700000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-429952361/2000000000 : ℝ)*X 0 0+(5392663921/10000000000 : ℝ)*X 0 1+(5266035887/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344686989/10000000000 : ℝ)*X 1 0+(-2213984869/10000000000 : ℝ)*X 1 1+(1053207187/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1068937421/2000000000 : ℝ)*X 2 0+(5266035757/10000000000 : ℝ)*X 2 1+(-44279699/200000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179806137/5000000000 : ℝ)*X 0 0+(4234581129/10000000000 : ℝ)*X 0 1+(179531399/400000000 : ℝ)*X 0 2+(2179806137/5000000000 : ℝ)*X 1 0+(4234581129/10000000000 : ℝ)*X 1 1+(179531399/400000000 : ℝ)*X 1 2+(2179806137/5000000000 : ℝ)*X 2 0+(4234581129/10000000000 : ℝ)*X 2 1+(179531399/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-214976673/1000000000 : ℝ)*X 0 0+(1316588943/2500000000 : ℝ)*X 0 1+(215693713/400000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312520939/10000000000 : ℝ)*X 1 0+(-41753557/200000000 : ℝ)*X 1 1+(2696171443/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1062504189/2000000000 : ℝ)*X 2 0+(539234291/1000000000 : ℝ)*X 2 1+(-208767781/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359621839/10000000000 : ℝ)*X 0 0+(4487643923/10000000000 : ℝ)*X 0 1+(423522469/1000000000 : ℝ)*X 0 2+(4359621839/10000000000 : ℝ)*X 1 0+(4487643923/10000000000 : ℝ)*X 1 1+(423522469/1000000000 : ℝ)*X 1 2+(4359621839/10000000000 : ℝ)*X 2 0+(4487643923/10000000000 : ℝ)*X 2 1+(423522469/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (222435489468791510602814961/85531250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (27024601/12500000000000 : ℝ)*(base19) + (361232189/100000000000000 : ℝ)*(base23) + (43776477/50000000000000 : ℝ)*(lower2) + (118940087/100000000000000 : ℝ)*(upper3) + (73462861/100000000000000 : ℝ)*(lower4) + (1479846019986151/25000000000000 : ℝ)*(major0) + (1479846019986151/25000000000000 : ℝ)*(major1) + (1479846019986151/25000000000000 : ℝ)*(major2) + (7897150822784459/100000000000000 : ℝ)*(sp0) + (3948576146993981/50000000000000 : ℝ)*(sp1) + (7897152148952581/100000000000000 : ℝ)*(sp2) + (3941607860090957/100000000000000 : ℝ)*(sp3) + (1687400311/100000000000000 : ℝ)*(sp4) + (7702925669/100000000000000 : ℝ)*(sp7) + (1970807781508313/50000000000000 : ℝ)*(f.failure) + (789715251018477/10000000000000 : ℝ)*(f.sum) + (20868735023961/3421250000000000000000000000 : ℝ)*base66 + (203479036433765359/48875000000000000000000000000000 : ℝ)*base67 + (671081868783515359/48875000000000000000000000000000 : ℝ)*base69 + (197899507684265359/48875000000000000000000000000000 : ℝ)*base71 + (27825348900113/6842500000000000000000000000 : ℝ)*base73 + (472360235915765359/48875000000000000000000000000000 : ℝ)*base75 + (71066537380359641/48875000000000000000000000000000 : ℝ)*base78 + (822960375868015359/48875000000000000000000000000000 : ℝ)*base79 + (36297100206721/13685000000000000000000000000 : ℝ)*base81 + (1989363/1250000000000000000000 : ℝ)*base90 + (1989363/1250000000000000000000 : ℝ)*base92 + (1989363/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1065960784625540003347862769/136850000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (122477751/10000000000000 : ℝ)*(base19) + (287278641/20000000000000 : ℝ)*(base23) + (88438763/50000000000000 : ℝ)*(upper3) + (79116007/100000000000000 : ℝ)*(lower4) + (64766059/50000000000000 : ℝ)*(upper5) + (1189898337198593/20000000000000 : ℝ)*(major0) + (1189898337198593/20000000000000 : ℝ)*(major1) + (1189898337198593/20000000000000 : ℝ)*(major2) + (34509233303/100000000000000 : ℝ)*(sp1) + (43382690541/100000000000000 : ℝ)*(sp2) + (7937319414764059/100000000000000 : ℝ)*(sp4) + (1587456736150649/20000000000000 : ℝ)*(sp5) + (992159324460039/12500000000000 : ℝ)*(sp6) + (158466547903189/4000000000000 : ℝ)*(sp7) + (158466547903189/4000000000000 : ℝ)*(f.failure) + (7937319414764059/100000000000000 : ℝ)*(f.sum) + (3404047321043/684250000000000000000000000 : ℝ)*base65 + (122922538472132337/39100000000000000000000000000000 : ℝ)*base67 + (164252129873932337/39100000000000000000000000000000 : ℝ)*base69 + (644858809158732337/39100000000000000000000000000000 : ℝ)*base71 + (6900717797791/2737000000000000000000000000 : ℝ)*base73 + (708626505403932337/39100000000000000000000000000000 : ℝ)*base75 + (314541347469432337/39100000000000000000000000000000 : ℝ)*base77 + (1034786779630232337/39100000000000000000000000000000 : ℝ)*base79 + (9920915291797/2737000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (391161/100000000000000000000 : ℝ)*base89 + (391161/100000000000000000000 : ℝ)*base91 + (391161/100000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1178_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1178_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1178_s7_0 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074892263/5000000000 : ℝ)*x 0 + (5392391879/10000000000 : ℝ)*x 1 + (1316573257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074892263/5000000000 : ℝ)^8371 ≤ (2613302758297/20000000000000 : ℝ)^6323 := by
    have hnat : (1074892263 : ℕ)^8371*20000000000000^6323 ≤ 2613302758297^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074892263 5000000000 2613302758297 20000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5392391879/10000000000 : ℝ)^8371 ≤ (2207375898393/5000000000000 : ℝ)^6323 := by
    have hnat : (5392391879 : ℕ)^8371*5000000000000^6323 ≤ 2207375898393^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392391879 10000000000 2207375898393 5000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316573257/2500000000 : ℝ)^8371 ≤ (42785968231037/100000000000000 : ℝ)^6323 := by
    have hnat : (1316573257 : ℕ)^8371*100000000000000^6323 ≤ 42785968231037^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316573257 2500000000 42785968231037 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074892263/5000000000 : ℝ), (5392391879/10000000000 : ℝ), (1316573257/2500000000 : ℝ)] ![(2613302758297/20000000000000 : ℝ), (2207375898393/5000000000000 : ℝ), (42785968231037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074892263/5000000000 : ℝ)|^8371 ≤ (2613302758297/20000000000000 : ℝ)^6323
        have hw : |(-1074892263/5000000000 : ℝ)|=(1074892263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5392391879/10000000000 : ℝ)|^8371 ≤ (2207375898393/5000000000000 : ℝ)^6323
        have hw : |(5392391879/10000000000 : ℝ)|=(5392391879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316573257/2500000000 : ℝ)|^8371 ≤ (42785968231037/100000000000000 : ℝ)^6323
        have hw : |(1316573257/2500000000 : ℝ)|=(1316573257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s7_1 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668077339/1250000000 : ℝ)*x 0 + (-442747061/2000000000 : ℝ)*x 1 + (1316573257/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668077339/1250000000 : ℝ)^8371 ≤ (85215744519/195312500000 : ℝ)^6323 := by
    have hnat : (668077339 : ℕ)^8371*195312500000^6323 ≤ 85215744519^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668077339 1250000000 85215744519 195312500000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (442747061/2000000000 : ℝ)^8371 ≤ (13583570560739/100000000000000 : ℝ)^6323 := by
    have hnat : (442747061 : ℕ)^8371*100000000000000^6323 ≤ 13583570560739^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442747061 2000000000 13583570560739 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1316573257/2500000000 : ℝ)^8371 ≤ (42785968231037/100000000000000 : ℝ)^6323 := by
    have hnat : (1316573257 : ℕ)^8371*100000000000000^6323 ≤ 42785968231037^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1316573257 2500000000 42785968231037 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668077339/1250000000 : ℝ), (-442747061/2000000000 : ℝ), (1316573257/2500000000 : ℝ)] ![(85215744519/195312500000 : ℝ), (13583570560739/100000000000000 : ℝ), (42785968231037/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668077339/1250000000 : ℝ)|^8371 ≤ (85215744519/195312500000 : ℝ)^6323
        have hw : |(668077339/1250000000 : ℝ)|=(668077339/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-442747061/2000000000 : ℝ)|^8371 ≤ (13583570560739/100000000000000 : ℝ)^6323
        have hw : |(-442747061/2000000000 : ℝ)|=(442747061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1316573257/2500000000 : ℝ)|^8371 ≤ (42785968231037/100000000000000 : ℝ)^6323
        have hw : |(1316573257/2500000000 : ℝ)|=(1316573257/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s7_2 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534461871/1000000000 : ℝ)*x 0 + (526629303/1000000000 : ℝ)*x 1 + (-442747061/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534461871/1000000000 : ℝ)^8371 ≤ (43630461172113/100000000000000 : ℝ)^6323 := by
    have hnat : (534461871 : ℕ)^8371*100000000000000^6323 ≤ 43630461172113^6323*1000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534461871 1000000000 43630461172113 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (526629303/1000000000 : ℝ)^8371 ≤ (42785968252549/100000000000000 : ℝ)^6323 := by
    have hnat : (526629303 : ℕ)^8371*100000000000000^6323 ≤ 42785968252549^6323*1000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526629303 1000000000 42785968252549 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (442747061/2000000000 : ℝ)^8371 ≤ (13583570560739/100000000000000 : ℝ)^6323 := by
    have hnat : (442747061 : ℕ)^8371*100000000000000^6323 ≤ 13583570560739^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      442747061 2000000000 13583570560739 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534461871/1000000000 : ℝ), (526629303/1000000000 : ℝ), (-442747061/2000000000 : ℝ)] ![(43630461172113/100000000000000 : ℝ), (42785968252549/100000000000000 : ℝ), (13583570560739/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534461871/1000000000 : ℝ)|^8371 ≤ (43630461172113/100000000000000 : ℝ)^6323
        have hw : |(534461871/1000000000 : ℝ)|=(534461871/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(526629303/1000000000 : ℝ)|^8371 ≤ (42785968252549/100000000000000 : ℝ)^6323
        have hw : |(526629303/1000000000 : ℝ)|=(526629303/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-442747061/2000000000 : ℝ)|^8371 ≤ (13583570560739/100000000000000 : ℝ)^6323
        have hw : |(-442747061/2000000000 : ℝ)|=(442747061/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s7_3 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179812761/5000000000 : ℝ)*x 0 + (2117554941/5000000000 : ℝ)*x 1 + (4487752949/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179812761/5000000000 : ℝ)^8371 ≤ (33317154375769/100000000000000 : ℝ)^6323 := by
    have hnat : (2179812761 : ℕ)^8371*100000000000000^6323 ≤ 33317154375769^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179812761 5000000000 33317154375769 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117554941/5000000000 : ℝ)^8371 ≤ (32063233375719/100000000000000 : ℝ)^6323 := by
    have hnat : (2117554941 : ℕ)^8371*100000000000000^6323 ≤ 32063233375719^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117554941 5000000000 32063233375719 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4487752949/10000000000 : ℝ)^8371 ≤ (34619612230937/100000000000000 : ℝ)^6323 := by
    have hnat : (4487752949 : ℕ)^8371*100000000000000^6323 ≤ 34619612230937^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4487752949 10000000000 34619612230937 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179812761/5000000000 : ℝ), (2117554941/5000000000 : ℝ), (4487752949/10000000000 : ℝ)] ![(33317154375769/100000000000000 : ℝ), (32063233375719/100000000000000 : ℝ), (34619612230937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179812761/5000000000 : ℝ)|^8371 ≤ (33317154375769/100000000000000 : ℝ)^6323
        have hw : |(2179812761/5000000000 : ℝ)|=(2179812761/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117554941/5000000000 : ℝ)|^8371 ≤ (32063233375719/100000000000000 : ℝ)^6323
        have hw : |(2117554941/5000000000 : ℝ)|=(2117554941/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4487752949/10000000000 : ℝ)|^8371 ≤ (34619612230937/100000000000000 : ℝ)^6323
        have hw : |(4487752949/10000000000 : ℝ)|=(4487752949/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s7_4 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-214978977/1000000000 : ℝ)*x 0 + (5266609849/10000000000 : ℝ)*x 1 + (5392073577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214978977/1000000000 : ℝ)^8371 ≤ (3266638997127/25000000000000 : ℝ)^6323 := by
    have hnat : (214978977 : ℕ)^8371*25000000000000^6323 ≤ 3266638997127^6323*1000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214978977 1000000000 3266638997127 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266609849/10000000000 : ℝ)^8371 ≤ (42789375988641/100000000000000 : ℝ)^6323 := by
    have hnat : (5266609849 : ℕ)^8371*100000000000000^6323 ≤ 42789375988641^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266609849 10000000000 42789375988641 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392073577/10000000000 : ℝ)^8371 ≤ (11036017001643/25000000000000 : ℝ)^6323 := by
    have hnat : (5392073577 : ℕ)^8371*25000000000000^6323 ≤ 11036017001643^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392073577 10000000000 11036017001643 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214978977/1000000000 : ℝ), (5266609849/10000000000 : ℝ), (5392073577/10000000000 : ℝ)] ![(3266638997127/25000000000000 : ℝ), (42789375988641/100000000000000 : ℝ), (11036017001643/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214978977/1000000000 : ℝ)|^8371 ≤ (3266638997127/25000000000000 : ℝ)^6323
        have hw : |(-214978977/1000000000 : ℝ)|=(214978977/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266609849/10000000000 : ℝ)|^8371 ≤ (42789375988641/100000000000000 : ℝ)^6323
        have hw : |(5266609849/10000000000 : ℝ)|=(5266609849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392073577/10000000000 : ℝ)|^8371 ≤ (11036017001643/25000000000000 : ℝ)^6323
        have hw : |(5392073577/10000000000 : ℝ)|=(5392073577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s7_5 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664073319/1250000000 : ℝ)*x 0 + (-521988837/2500000000 : ℝ)*x 1 + (5392073513/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664073319/1250000000 : ℝ)^8371 ≤ (8656921701533/20000000000000 : ℝ)^6323 := by
    have hnat : (664073319 : ℕ)^8371*20000000000000^6323 ≤ 8656921701533^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664073319 1250000000 8656921701533 20000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (521988837/2500000000 : ℝ)^8371 ≤ (12571324162383/100000000000000 : ℝ)^6323 := by
    have hnat : (521988837 : ℕ)^8371*100000000000000^6323 ≤ 12571324162383^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      521988837 2500000000 12571324162383 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392073513/10000000000 : ℝ)^8371 ≤ (22072033656453/50000000000000 : ℝ)^6323 := by
    have hnat : (5392073513 : ℕ)^8371*50000000000000^6323 ≤ 22072033656453^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392073513 10000000000 22072033656453 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664073319/1250000000 : ℝ), (-521988837/2500000000 : ℝ), (5392073513/10000000000 : ℝ)] ![(8656921701533/20000000000000 : ℝ), (12571324162383/100000000000000 : ℝ), (22072033656453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664073319/1250000000 : ℝ)|^8371 ≤ (8656921701533/20000000000000 : ℝ)^6323
        have hw : |(664073319/1250000000 : ℝ)|=(664073319/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-521988837/2500000000 : ℝ)|^8371 ≤ (12571324162383/100000000000000 : ℝ)^6323
        have hw : |(-521988837/2500000000 : ℝ)|=(521988837/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392073513/10000000000 : ℝ)|^8371 ≤ (22072033656453/50000000000000 : ℝ)^6323
        have hw : |(5392073513/10000000000 : ℝ)|=(5392073513/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s7_6 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (664073361/1250000000 : ℝ)*x 0 + (1078414663/2000000000 : ℝ)*x 1 + (-1043977581/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (664073361/1250000000 : ℝ)^8371 ≤ (21642306065969/50000000000000 : ℝ)^6323 := by
    have hnat : (664073361 : ℕ)^8371*50000000000000^6323 ≤ 21642306065969^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      664073361 1250000000 21642306065969 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078414663/2000000000 : ℝ)^8371 ≤ (70630504267/160000000000 : ℝ)^6323 := by
    have hnat : (1078414663 : ℕ)^8371*160000000000^6323 ≤ 70630504267^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078414663 2000000000 70630504267 160000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043977581/5000000000 : ℝ)^8371 ≤ (12571322679773/100000000000000 : ℝ)^6323 := by
    have hnat : (1043977581 : ℕ)^8371*100000000000000^6323 ≤ 12571322679773^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043977581 5000000000 12571322679773 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(664073361/1250000000 : ℝ), (1078414663/2000000000 : ℝ), (-1043977581/5000000000 : ℝ)] ![(21642306065969/50000000000000 : ℝ), (70630504267/160000000000 : ℝ), (12571322679773/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(664073361/1250000000 : ℝ)|^8371 ≤ (21642306065969/50000000000000 : ℝ)^6323
        have hw : |(664073361/1250000000 : ℝ)|=(664073361/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078414663/2000000000 : ℝ)|^8371 ≤ (70630504267/160000000000 : ℝ)^6323
        have hw : |(1078414663/2000000000 : ℝ)|=(1078414663/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1043977581/5000000000 : ℝ)|^8371 ≤ (12571322679773/100000000000000 : ℝ)^6323
        have hw : |(-1043977581/5000000000 : ℝ)|=(1043977581/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s7_7 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359635233/10000000000 : ℝ)*x 0 + (89742349/200000000 : ℝ)*x 1 + (1058936897/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359635233/10000000000 : ℝ)^8371 ≤ (33317252626771/100000000000000 : ℝ)^6323 := by
    have hnat : (4359635233 : ℕ)^8371*100000000000000^6323 ≤ 33317252626771^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359635233 10000000000 33317252626771 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (89742349/200000000 : ℝ)^8371 ≤ (17306561058437/50000000000000 : ℝ)^6323 := by
    have hnat : (89742349 : ℕ)^8371*50000000000000^6323 ≤ 17306561058437^6323*200000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      89742349 200000000 17306561058437 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058936897/2500000000 : ℝ)^8371 ≤ (8017406311257/25000000000000 : ℝ)^6323 := by
    have hnat : (1058936897 : ℕ)^8371*25000000000000^6323 ≤ 8017406311257^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058936897 2500000000 8017406311257 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359635233/10000000000 : ℝ), (89742349/200000000 : ℝ), (1058936897/2500000000 : ℝ)] ![(33317252626771/100000000000000 : ℝ), (17306561058437/50000000000000 : ℝ), (8017406311257/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359635233/10000000000 : ℝ)|^8371 ≤ (33317252626771/100000000000000 : ℝ)^6323
        have hw : |(4359635233/10000000000 : ℝ)|=(4359635233/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(89742349/200000000 : ℝ)|^8371 ≤ (17306561058437/50000000000000 : ℝ)^6323
        have hw : |(89742349/200000000 : ℝ)|=(89742349/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058936897/2500000000 : ℝ)|^8371 ≤ (8017406311257/25000000000000 : ℝ)^6323
        have hw : |(1058936897/2500000000 : ℝ)|=(1058936897/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1178_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11399/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1407/10000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5697/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5697/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5697/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (3519/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5697/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5697/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (3519/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5697/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5697/50000 : ℝ) ^ (4185/1024 : ℝ) ≤ (6977289812124099/50000000000000000000 : ℝ) := by
    have hpowers : (5697/50000 : ℝ)^4185 ≤ (6977289812124099/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5697 : ℕ)^4185*50000000000000000000^1024 ≤ 6977289812124099^1024*50000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5697 50000 6977289812124099 50000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5697/50000 : ℝ)) (X := (6977289812124099/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (3519/25000 : ℝ) ^ (4185/1024 : ℝ) ≤ (33106091091174363/100000000000000000000 : ℝ) := by
    have hpowers : (3519/25000 : ℝ)^4185 ≤ (33106091091174363/100000000000000000000 : ℝ)^1024 := by
      have hnat : (3519 : ℕ)^4185*100000000000000000000^1024 ≤ 33106091091174363^1024*25000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3519 25000 33106091091174363 100000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3519/25000 : ℝ)) (X := (33106091091174363/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006977289812124099/25000000000000000000 : ℝ) ≤ (1250085352351559/1250000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (25006977289812124099/25000000000000000000 : ℝ)^1024 ≤ (1250085352351559/1250000000000000 : ℝ)^4185 := by
      have hnat : (25006977289812124099 : ℕ)^1024*1250000000000000^4185 ≤ 1250085352351559^4185*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006977289812124099 25000000000000000000 1250085352351559 1250000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250085352351559/1250000000000000 : ℝ)) (X := (25006977289812124099/25000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100047060670715422561/100000000000000000000 : ℝ) ≤ (10001151291861643/10000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (100047060670715422561/100000000000000000000 : ℝ)^1024 ≤ (10001151291861643/10000000000000000 : ℝ)^4185 := by
      have hnat : (100047060670715422561 : ℕ)^1024*10000000000000000^4185 ≤ 10001151291861643^4185*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100047060670715422561 100000000000000000000 10001151291861643 10000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001151291861643/10000000000000000 : ℝ)) (X := (100047060670715422561/100000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033106091091174363/50000000000000000000 : ℝ) ≤ (5000809882455407/5000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (50033106091091174363/50000000000000000000 : ℝ)^1024 ≤ (5000809882455407/5000000000000000 : ℝ)^4185 := by
      have hnat : (50033106091091174363 : ℕ)^1024*5000000000000000^4185 ≤ 5000809882455407^4185*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033106091091174363 50000000000000000000 5000809882455407 5000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000809882455407/5000000000000000 : ℝ)) (X := (50033106091091174363/50000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6977289812124099/50000000000000000000 : ℝ) ≤ ((744754326561403921/745000000000000000 : ℝ)+2*(52052561019/29800000000000 : ℝ)*(5697/50000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (744754326561403921/745000000000000000 : ℝ)+2*(52052561019/29800000000000 : ℝ)*(5697/50000 : ℝ)=(1250085352351559/1250000000000000 : ℝ) by norm_num, show 1+2*(6977289812124099/50000000000000000000 : ℝ)=(25006977289812124099/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33106091091174363/100000000000000000000 : ℝ)+(6977289812124099/50000000000000000000 : ℝ) ≤ ((744754326561403921/745000000000000000 : ℝ)+(52052561019/29800000000000 : ℝ)*((3519/25000 : ℝ)+(5697/50000 : ℝ)))^(4185/1024 : ℝ) := by
    rw [show (744754326561403921/745000000000000000 : ℝ)+(52052561019/29800000000000 : ℝ)*((3519/25000 : ℝ)+(5697/50000 : ℝ))=(10001151291861643/10000000000000000 : ℝ) by norm_num, show 1+(33106091091174363/100000000000000000000 : ℝ)+(6977289812124099/50000000000000000000 : ℝ)=(100047060670715422561/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33106091091174363/100000000000000000000 : ℝ) ≤ ((744754326561403921/745000000000000000 : ℝ)+2*(52052561019/29800000000000 : ℝ)*(3519/25000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (744754326561403921/745000000000000000 : ℝ)+2*(52052561019/29800000000000 : ℝ)*(3519/25000 : ℝ)=(5000809882455407/5000000000000000 : ℝ) by norm_num, show 1+2*(33106091091174363/100000000000000000000 : ℝ)=(50033106091091174363/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (744754326561403921/745000000000000000 : ℝ)*(X 1 0+X 2 0)+(52052561019/29800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (5697/50000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (744754326561403921/745000000000000000 : ℝ)) (alpha := (52052561019/29800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (744754326561403921/745000000000000000 : ℝ)*(X 0 1+X 2 1)+(52052561019/29800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (5697/50000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (744754326561403921/745000000000000000 : ℝ)) (alpha := (52052561019/29800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (744754326561403921/745000000000000000 : ℝ)*(X 0 2+X 1 2)+(52052561019/29800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (5697/50000 : ℝ)) (hi := (3519/25000 : ℝ)) (c := (744754326561403921/745000000000000000 : ℝ)) (alpha := (52052561019/29800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1074892263/5000000000 : ℝ)*X 0 0+(5392391879/10000000000 : ℝ)*X 0 1+(1316573257/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668077339/1250000000 : ℝ)*X 1 0+(-442747061/2000000000 : ℝ)*X 1 1+(1316573257/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534461871/1000000000 : ℝ)*X 2 0+(526629303/1000000000 : ℝ)*X 2 1+(-442747061/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2179812761/5000000000 : ℝ)*X 0 0+(2117554941/5000000000 : ℝ)*X 0 1+(4487752949/10000000000 : ℝ)*X 0 2+(2179812761/5000000000 : ℝ)*X 1 0+(2117554941/5000000000 : ℝ)*X 1 1+(4487752949/10000000000 : ℝ)*X 1 2+(2179812761/5000000000 : ℝ)*X 2 0+(2117554941/5000000000 : ℝ)*X 2 1+(4487752949/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-214978977/1000000000 : ℝ)*X 0 0+(5266609849/10000000000 : ℝ)*X 0 1+(5392073577/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((664073319/1250000000 : ℝ)*X 1 0+(-521988837/2500000000 : ℝ)*X 1 1+(5392073513/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((664073361/1250000000 : ℝ)*X 2 0+(1078414663/2000000000 : ℝ)*X 2 1+(-1043977581/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4359635233/10000000000 : ℝ)*X 0 0+(89742349/200000000 : ℝ)*X 0 1+(1058936897/2500000000 : ℝ)*X 0 2+(4359635233/10000000000 : ℝ)*X 1 0+(89742349/200000000 : ℝ)*X 1 1+(1058936897/2500000000 : ℝ)*X 1 2+(4359635233/10000000000 : ℝ)*X 2 0+(89742349/200000000 : ℝ)*X 2 1+(1058936897/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (248799312219524751338381463/37250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (261128601/20000000000000 : ℝ)*(base19) + (1211007147/100000000000000 : ℝ)*(base23) + (24496593/50000000000000 : ℝ)*(lower2) + (5247911/3125000000000 : ℝ)*(upper3) + (99757371/100000000000000 : ℝ)*(upper5) + (2972137487259683/50000000000000 : ℝ)*(major0) + (2972137487259683/50000000000000 : ℝ)*(major1) + (5944274974519367/100000000000000 : ℝ)*(major2) + (7930323960701207/100000000000000 : ℝ)*(sp0) + (1982589610298617/25000000000000 : ℝ)*(sp1) + (7930358535830327/100000000000000 : ℝ)*(sp2) + (989542669387167/25000000000000 : ℝ)*(sp3) + (17893068133/50000000000000 : ℝ)*(sp4) + (19302013371/100000000000000 : ℝ)*(sp7) + (98954749489051/2500000000000 : ℝ)*(f.failure) + (7930359746837473/100000000000000 : ℝ)*(f.sum) + (5108180306667/2980000000000000000000000000 : ℝ)*base65 + (539185867509329543/37250000000000000000000000000000 : ℝ)*base67 + (1476635967402088007/74500000000000000000000000000000 : ℝ)*base69 + (803104075294829543/37250000000000000000000000000000 : ℝ)*base71 + (4273229158647/2980000000000000000000000000 : ℝ)*base73 + (762535525865088007/74500000000000000000000000000000 : ℝ)*base75 + (587672415745592043/37250000000000000000000000000000 : ℝ)*base77 + (672682181889842043/37250000000000000000000000000000 : ℝ)*base79 + (43471589609/5820312500000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (862599/62500000000000000000 : ℝ)*base89 + (862599/62500000000000000000 : ℝ)*base91 + (237599/62500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4456740585623832158067987/931250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (235810029/50000000000000 : ℝ)*(base19) + (1207092413/100000000000000 : ℝ)*(base23) + (37270379/20000000000000 : ℝ)*(upper2) + (41577049/25000000000000 : ℝ)*(upper3) + (94691399/100000000000000 : ℝ)*(upper4) + (427596279/100000000000000 : ℝ)*(upper5) + (149358072734499/2500000000000 : ℝ)*(major0) + (149358072734499/2500000000000 : ℝ)*(major1) + (149358072734499/2500000000000 : ℝ)*(major2) + (4879299951/50000000000000 : ℝ)*(sp2) + (3985223639561053/50000000000000 : ℝ)*(sp4) + (7970446807502049/100000000000000 : ℝ)*(sp5) + (249076134794681/3125000000000 : ℝ)*(sp6) + (994549595028103/25000000000000 : ℝ)*(sp7) + (994549595028103/25000000000000 : ℝ)*(f.failure) + (3985223639561053/50000000000000 : ℝ)*(f.sum) + (4720917221/1490000000000000000000000 : ℝ)*base66 + (11718743928729421/1862500000000000000000000000000 : ℝ)*base68 + (37748753423429421/1862500000000000000000000000000 : ℝ)*base70 + (11008886048145579/1862500000000000000000000000000 : ℝ)*base71 + (4549396433/9312500000000000000000000 : ℝ)*base74 + (5858080185633079/1862500000000000000000000000000 : ℝ)*base75 + (49878639096004421/1862500000000000000000000000000 : ℝ)*base78 + (27544893558154421/1862500000000000000000000000000 : ℝ)*base80 + (380857431267/74500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (8219347/625000000000000000000 : ℝ)*base89 + (8219347/625000000000000000000 : ℝ)*base91 + (8219347/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1178_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (3519/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5697/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1178_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1178_s8_0 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149791499/10000000000 : ℝ)*x 0 + (2696168393/5000000000 : ℝ)*x 1 + (164573229/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149791499/10000000000 : ℝ)^8371 ≤ (6533284950651/50000000000000 : ℝ)^6323 := by
    have hnat : (2149791499 : ℕ)^8371*50000000000000^6323 ≤ 6533284950651^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149791499 10000000000 6533284950651 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696168393/5000000000 : ℝ)^8371 ≤ (2207346041493/5000000000000 : ℝ)^6323 := by
    have hnat : (2696168393 : ℕ)^8371*5000000000000^6323 ≤ 2207346041493^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696168393 5000000000 2207346041493 5000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164573229/312500000 : ℝ)^8371 ≤ (42786509258313/100000000000000 : ℝ)^6323 := by
    have hnat : (164573229 : ℕ)^8371*100000000000000^6323 ≤ 42786509258313^6323*312500000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164573229 312500000 42786509258313 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149791499/10000000000 : ℝ), (2696168393/5000000000 : ℝ), (164573229/312500000 : ℝ)] ![(6533284950651/50000000000000 : ℝ), (2207346041493/5000000000000 : ℝ), (42786509258313/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149791499/10000000000 : ℝ)|^8371 ≤ (6533284950651/50000000000000 : ℝ)^6323
        have hw : |(-2149791499/10000000000 : ℝ)|=(2149791499/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696168393/5000000000 : ℝ)|^8371 ≤ (2207346041493/5000000000000 : ℝ)^6323
        have hw : |(2696168393/5000000000 : ℝ)|=(2696168393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164573229/312500000 : ℝ)|^8371 ≤ (42786509258313/100000000000000 : ℝ)^6323
        have hw : |(164573229/312500000 : ℝ)|=(164573229/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s8_1 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (534460417/1000000000 : ℝ)*x 0 + (-553422047/2500000000 : ℝ)*x 1 + (658292903/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534460417/1000000000 : ℝ)^8371 ≤ (10907576007603/25000000000000 : ℝ)^6323 := by
    have hnat : (534460417 : ℕ)^8371*25000000000000^6323 ≤ 10907576007603^6323*1000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534460417 1000000000 10907576007603 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (553422047/2500000000 : ℝ)^8371 ≤ (1358318780779/10000000000000 : ℝ)^6323 := by
    have hnat : (553422047 : ℕ)^8371*10000000000000^6323 ≤ 1358318780779^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553422047 2500000000 1358318780779 10000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658292903/1250000000 : ℝ)^8371 ≤ (21393254069843/50000000000000 : ℝ)^6323 := by
    have hnat : (658292903 : ℕ)^8371*50000000000000^6323 ≤ 21393254069843^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658292903 1250000000 21393254069843 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534460417/1000000000 : ℝ), (-553422047/2500000000 : ℝ), (658292903/1250000000 : ℝ)] ![(10907576007603/25000000000000 : ℝ), (1358318780779/10000000000000 : ℝ), (21393254069843/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534460417/1000000000 : ℝ)|^8371 ≤ (10907576007603/25000000000000 : ℝ)^6323
        have hw : |(534460417/1000000000 : ℝ)|=(534460417/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-553422047/2500000000 : ℝ)|^8371 ≤ (1358318780779/10000000000000 : ℝ)^6323
        have hw : |(-553422047/2500000000 : ℝ)|=(553422047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658292903/1250000000 : ℝ)|^8371 ≤ (21393254069843/50000000000000 : ℝ)^6323
        have hw : |(658292903/1250000000 : ℝ)|=(658292903/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s8_2 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (334037759/625000000 : ℝ)*x 0 + (5266343299/10000000000 : ℝ)*x 1 + (-3541901/16000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (334037759/625000000 : ℝ)^8371 ≤ (5453787968677/12500000000000 : ℝ)^6323 := by
    have hnat : (334037759 : ℕ)^8371*12500000000000^6323 ≤ 5453787968677^6323*625000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      334037759 625000000 5453787968677 12500000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266343299/10000000000 : ℝ)^8371 ≤ (10696627236597/25000000000000 : ℝ)^6323 := by
    have hnat : (5266343299 : ℕ)^8371*25000000000000^6323 ≤ 10696627236597^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266343299 10000000000 10696627236597 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3541901/16000000 : ℝ)^8371 ≤ (6791593648007/50000000000000 : ℝ)^6323 := by
    have hnat : (3541901 : ℕ)^8371*50000000000000^6323 ≤ 6791593648007^6323*16000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3541901 16000000 6791593648007 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(334037759/625000000 : ℝ), (5266343299/10000000000 : ℝ), (-3541901/16000000 : ℝ)] ![(5453787968677/12500000000000 : ℝ), (10696627236597/25000000000000 : ℝ), (6791593648007/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(334037759/625000000 : ℝ)|^8371 ≤ (5453787968677/12500000000000 : ℝ)^6323
        have hw : |(334037759/625000000 : ℝ)|=(334037759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266343299/10000000000 : ℝ)|^8371 ≤ (10696627236597/25000000000000 : ℝ)^6323
        have hw : |(5266343299/10000000000 : ℝ)|=(5266343299/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-3541901/16000000 : ℝ)|^8371 ≤ (6791593648007/50000000000000 : ℝ)^6323
        have hw : |(-3541901/16000000 : ℝ)|=(3541901/16000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s8_3 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (871925633/2000000000 : ℝ)*x 0 + (2117607531/5000000000 : ℝ)*x 1 + (2243823553/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871925633/2000000000 : ℝ)^8371 ≤ (2082323819769/6250000000000 : ℝ)^6323 := by
    have hnat : (871925633 : ℕ)^8371*6250000000000^6323 ≤ 2082323819769^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871925633 2000000000 2082323819769 6250000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2117607531/5000000000 : ℝ)^8371 ≤ (1282571503873/4000000000000 : ℝ)^6323 := by
    have hnat : (2117607531 : ℕ)^8371*4000000000000^6323 ≤ 1282571503873^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2117607531 5000000000 1282571503873 4000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2243823553/5000000000 : ℝ)^8371 ≤ (17309265637613/50000000000000 : ℝ)^6323 := by
    have hnat : (2243823553 : ℕ)^8371*50000000000000^6323 ≤ 17309265637613^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2243823553 5000000000 17309265637613 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871925633/2000000000 : ℝ), (2117607531/5000000000 : ℝ), (2243823553/5000000000 : ℝ)] ![(2082323819769/6250000000000 : ℝ), (1282571503873/4000000000000 : ℝ), (17309265637613/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871925633/2000000000 : ℝ)|^8371 ≤ (2082323819769/6250000000000 : ℝ)^6323
        have hw : |(871925633/2000000000 : ℝ)|=(871925633/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2117607531/5000000000 : ℝ)|^8371 ≤ (1282571503873/4000000000000 : ℝ)^6323
        have hw : |(2117607531/5000000000 : ℝ)|=(2117607531/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2243823553/5000000000 : ℝ)|^8371 ≤ (17309265637613/50000000000000 : ℝ)^6323
        have hw : |(2243823553/5000000000 : ℝ)|=(2243823553/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s8_4 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1074898161/5000000000 : ℝ)*x 0 + (2633330027/5000000000 : ℝ)*x 1 + (5392018889/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1074898161/5000000000 : ℝ)^8371 ≤ (13066608710693/100000000000000 : ℝ)^6323 := by
    have hnat : (1074898161 : ℕ)^8371*100000000000000^6323 ≤ 13066608710693^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1074898161 5000000000 13066608710693 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2633330027/5000000000 : ℝ)^8371 ≤ (42789916004617/100000000000000 : ℝ)^6323 := by
    have hnat : (2633330027 : ℕ)^8371*100000000000000^6323 ≤ 42789916004617^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2633330027 5000000000 42789916004617 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5392018889/10000000000 : ℝ)^8371 ≤ (22071737634791/50000000000000 : ℝ)^6323 := by
    have hnat : (5392018889 : ℕ)^8371*50000000000000^6323 ≤ 22071737634791^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5392018889 10000000000 22071737634791 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1074898161/5000000000 : ℝ), (2633330027/5000000000 : ℝ), (5392018889/10000000000 : ℝ)] ![(13066608710693/100000000000000 : ℝ), (42789916004617/100000000000000 : ℝ), (22071737634791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1074898161/5000000000 : ℝ)|^8371 ≤ (13066608710693/100000000000000 : ℝ)^6323
        have hw : |(-1074898161/5000000000 : ℝ)|=(1074898161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2633330027/5000000000 : ℝ)|^8371 ≤ (42789916004617/100000000000000 : ℝ)^6323
        have hw : |(2633330027/5000000000 : ℝ)|=(2633330027/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5392018889/10000000000 : ℝ)|^8371 ≤ (22071737634791/50000000000000 : ℝ)^6323
        have hw : |(5392018889/10000000000 : ℝ)|=(5392018889/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s8_5 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5312599171/10000000000 : ℝ)*x 0 + (-1044006269/5000000000 : ℝ)*x 1 + (1078403779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312599171/10000000000 : ℝ)^8371 ≤ (21642372311451/50000000000000 : ℝ)^6323 := by
    have hnat : (5312599171 : ℕ)^8371*50000000000000^6323 ≤ 21642372311451^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312599171 10000000000 21642372311451 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1044006269/5000000000 : ℝ)^8371 ≤ (6285890013561/50000000000000 : ℝ)^6323 := by
    have hnat : (1044006269 : ℕ)^8371*50000000000000^6323 ≤ 6285890013561^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1044006269 5000000000 6285890013561 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1078403779/2000000000 : ℝ)^8371 ≤ (44143475334613/100000000000000 : ℝ)^6323 := by
    have hnat : (1078403779 : ℕ)^8371*100000000000000^6323 ≤ 44143475334613^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078403779 2000000000 44143475334613 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312599171/10000000000 : ℝ), (-1044006269/5000000000 : ℝ), (1078403779/2000000000 : ℝ)] ![(21642372311451/50000000000000 : ℝ), (6285890013561/50000000000000 : ℝ), (44143475334613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312599171/10000000000 : ℝ)|^8371 ≤ (21642372311451/50000000000000 : ℝ)^6323
        have hw : |(5312599171/10000000000 : ℝ)|=(5312599171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1044006269/5000000000 : ℝ)|^8371 ≤ (6285890013561/50000000000000 : ℝ)^6323
        have hw : |(-1044006269/5000000000 : ℝ)|=(1044006269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1078403779/2000000000 : ℝ)|^8371 ≤ (44143475334613/100000000000000 : ℝ)^6323
        have hw : |(1078403779/2000000000 : ℝ)|=(1078403779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s8_6 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656299589/5000000000 : ℝ)*x 0 + (539201889/1000000000 : ℝ)*x 1 + (-261001567/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656299589/5000000000 : ℝ)^8371 ≤ (5410593087301/12500000000000 : ℝ)^6323 := by
    have hnat : (2656299589 : ℕ)^8371*12500000000000^6323 ≤ 5410593087301^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656299589 5000000000 5410593087301 12500000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539201889/1000000000 : ℝ)^8371 ≤ (44143475280421/100000000000000 : ℝ)^6323 := by
    have hnat : (539201889 : ℕ)^8371*100000000000000^6323 ≤ 44143475280421^6323*1000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539201889 1000000000 44143475280421 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (261001567/1250000000 : ℝ)^8371 ≤ (628589000559/5000000000000 : ℝ)^6323 := by
    have hnat : (261001567 : ℕ)^8371*5000000000000^6323 ≤ 628589000559^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261001567 1250000000 628589000559 5000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656299589/5000000000 : ℝ), (539201889/1000000000 : ℝ), (-261001567/1250000000 : ℝ)] ![(5410593087301/12500000000000 : ℝ), (44143475280421/100000000000000 : ℝ), (628589000559/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656299589/5000000000 : ℝ)|^8371 ≤ (5410593087301/12500000000000 : ℝ)^6323
        have hw : |(2656299589/5000000000 : ℝ)|=(2656299589/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539201889/1000000000 : ℝ)|^8371 ≤ (44143475280421/100000000000000 : ℝ)^6323
        have hw : |(539201889/1000000000 : ℝ)|=(539201889/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-261001567/1250000000 : ℝ)|^8371 ≤ (628589000559/5000000000000 : ℝ)^6323
        have hw : |(-261001567/1250000000 : ℝ)|=(261001567/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s8_7 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089909447/2500000000 : ℝ)*x 0 + (112175311/250000000 : ℝ)*x 1 + (4235851997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089909447/2500000000 : ℝ)^8371 ≤ (4164659809623/12500000000000 : ℝ)^6323 := by
    have hnat : (1089909447 : ℕ)^8371*12500000000000^6323 ≤ 4164659809623^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089909447 2500000000 4164659809623 12500000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (112175311/250000000 : ℝ)^8371 ≤ (34612049717603/100000000000000 : ℝ)^6323 := by
    have hnat : (112175311 : ℕ)^8371*100000000000000^6323 ≤ 34612049717603^6323*250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      112175311 250000000 34612049717603 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4235851997/10000000000 : ℝ)^8371 ≤ (32070671789391/100000000000000 : ℝ)^6323 := by
    have hnat : (4235851997 : ℕ)^8371*100000000000000^6323 ≤ 32070671789391^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4235851997 10000000000 32070671789391 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089909447/2500000000 : ℝ), (112175311/250000000 : ℝ), (4235851997/10000000000 : ℝ)] ![(4164659809623/12500000000000 : ℝ), (34612049717603/100000000000000 : ℝ), (32070671789391/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089909447/2500000000 : ℝ)|^8371 ≤ (4164659809623/12500000000000 : ℝ)^6323
        have hw : |(1089909447/2500000000 : ℝ)|=(1089909447/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(112175311/250000000 : ℝ)|^8371 ≤ (34612049717603/100000000000000 : ℝ)^6323
        have hw : |(112175311/250000000 : ℝ)|=(112175311/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4235851997/10000000000 : ℝ)|^8371 ≤ (32070671789391/100000000000000 : ℝ)^6323
        have hw : |(4235851997/10000000000 : ℝ)|=(4235851997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1178_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (57/500 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14069/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (1407/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (1407/10000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11399/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (1407/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (1407/10000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11399/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (1407/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (1407/10000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11399/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11399/100000 : ℝ) ^ (4185/1024 : ℝ) ≤ (13979623422453883/100000000000000000000 : ℝ) := by
    have hpowers : (11399/100000 : ℝ)^4185 ≤ (13979623422453883/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11399 : ℕ)^4185*100000000000000000000^1024 ≤ 13979623422453883^1024*100000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11399 100000 13979623422453883 100000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11399/100000 : ℝ)) (X := (13979623422453883/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (1407/10000 : ℝ) ^ (4185/1024 : ℝ) ≤ (33048455643926549/100000000000000000000 : ℝ) := by
    have hpowers : (1407/10000 : ℝ)^4185 ≤ (33048455643926549/100000000000000000000 : ℝ)^1024 := by
      have hnat : (1407 : ℕ)^4185*100000000000000000000^1024 ≤ 33048455643926549^1024*10000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1407 10000 33048455643926549 100000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1407/10000 : ℝ)) (X := (33048455643926549/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50013979623422453883/50000000000000000000 : ℝ) ≤ (625042752757141/625000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (50013979623422453883/50000000000000000000 : ℝ)^1024 ≤ (625042752757141/625000000000000 : ℝ)^4185 := by
      have hnat : (50013979623422453883 : ℕ)^1024*625000000000000^4185 ≤ 625042752757141^4185*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50013979623422453883 50000000000000000000 625042752757141 625000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625042752757141/625000000000000 : ℝ)) (X := (50013979623422453883/50000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (6252939254941648777/6250000000000000000 : ℝ) ≤ (2000230098936273/2000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (6252939254941648777/6250000000000000000 : ℝ)^1024 ≤ (2000230098936273/2000000000000000 : ℝ)^4185 := by
      have hnat : (6252939254941648777 : ℕ)^1024*2000000000000000^4185 ≤ 2000230098936273^4185*6250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6252939254941648777 6250000000000000000 2000230098936273 2000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000230098936273/2000000000000000 : ℝ)) (X := (6252939254941648777/6250000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50033048455643926549/50000000000000000000 : ℝ) ≤ (5000808472624237/5000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (50033048455643926549/50000000000000000000 : ℝ)^1024 ≤ (5000808472624237/5000000000000000 : ℝ)^4185 := by
      have hnat : (50033048455643926549 : ℕ)^1024*5000000000000000^4185 ≤ 5000808472624237^4185*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033048455643926549 50000000000000000000 5000808472624237 5000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000808472624237/5000000000000000 : ℝ)) (X := (50033048455643926549/50000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13979623422453883/100000000000000000000 : ℝ) ≤ ((13350596470900113397/13355000000000000000 : ℝ)+2*(466450567109/267100000000000 : ℝ)*(11399/100000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (13350596470900113397/13355000000000000000 : ℝ)+2*(466450567109/267100000000000 : ℝ)*(11399/100000 : ℝ)=(625042752757141/625000000000000 : ℝ) by norm_num, show 1+2*(13979623422453883/100000000000000000000 : ℝ)=(50013979623422453883/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(33048455643926549/100000000000000000000 : ℝ)+(13979623422453883/100000000000000000000 : ℝ) ≤ ((13350596470900113397/13355000000000000000 : ℝ)+(466450567109/267100000000000 : ℝ)*((1407/10000 : ℝ)+(11399/100000 : ℝ)))^(4185/1024 : ℝ) := by
    rw [show (13350596470900113397/13355000000000000000 : ℝ)+(466450567109/267100000000000 : ℝ)*((1407/10000 : ℝ)+(11399/100000 : ℝ))=(2000230098936273/2000000000000000 : ℝ) by norm_num, show 1+(33048455643926549/100000000000000000000 : ℝ)+(13979623422453883/100000000000000000000 : ℝ)=(6252939254941648777/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(33048455643926549/100000000000000000000 : ℝ) ≤ ((13350596470900113397/13355000000000000000 : ℝ)+2*(466450567109/267100000000000 : ℝ)*(1407/10000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (13350596470900113397/13355000000000000000 : ℝ)+2*(466450567109/267100000000000 : ℝ)*(1407/10000 : ℝ)=(5000808472624237/5000000000000000 : ℝ) by norm_num, show 1+2*(33048455643926549/100000000000000000000 : ℝ)=(50033048455643926549/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (13350596470900113397/13355000000000000000 : ℝ)*(X 1 0+X 2 0)+(466450567109/267100000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (13350596470900113397/13355000000000000000 : ℝ)) (alpha := (466450567109/267100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (13350596470900113397/13355000000000000000 : ℝ)*(X 0 1+X 2 1)+(466450567109/267100000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (13350596470900113397/13355000000000000000 : ℝ)) (alpha := (466450567109/267100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (13350596470900113397/13355000000000000000 : ℝ)*(X 0 2+X 1 2)+(466450567109/267100000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (11399/100000 : ℝ)) (hi := (1407/10000 : ℝ)) (c := (13350596470900113397/13355000000000000000 : ℝ)) (alpha := (466450567109/267100000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2149791499/10000000000 : ℝ)*X 0 0+(2696168393/5000000000 : ℝ)*X 0 1+(164573229/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s8_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((534460417/1000000000 : ℝ)*X 1 0+(-553422047/2500000000 : ℝ)*X 1 1+(658292903/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s8_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((334037759/625000000 : ℝ)*X 2 0+(5266343299/10000000000 : ℝ)*X 2 1+(-3541901/16000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s8_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871925633/2000000000 : ℝ)*X 0 0+(2117607531/5000000000 : ℝ)*X 0 1+(2243823553/5000000000 : ℝ)*X 0 2+(871925633/2000000000 : ℝ)*X 1 0+(2117607531/5000000000 : ℝ)*X 1 1+(2243823553/5000000000 : ℝ)*X 1 2+(871925633/2000000000 : ℝ)*X 2 0+(2117607531/5000000000 : ℝ)*X 2 1+(2243823553/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s8_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1074898161/5000000000 : ℝ)*X 0 0+(2633330027/5000000000 : ℝ)*X 0 1+(5392018889/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s8_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5312599171/10000000000 : ℝ)*X 1 0+(-1044006269/5000000000 : ℝ)*X 1 1+(1078403779/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s8_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2656299589/5000000000 : ℝ)*X 2 0+(539201889/1000000000 : ℝ)*X 2 1+(-261001567/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s8_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089909447/2500000000 : ℝ)*X 0 0+(112175311/250000000 : ℝ)*X 0 1+(4235851997/10000000000 : ℝ)*X 0 2+(1089909447/2500000000 : ℝ)*X 1 0+(112175311/250000000 : ℝ)*X 1 1+(4235851997/10000000000 : ℝ)*X 1 2+(1089909447/2500000000 : ℝ)*X 2 0+(112175311/250000000 : ℝ)*X 2 1+(4235851997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s8_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (100454317463564818264467/13355000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1442340017/100000000000000 : ℝ)*(base19) + (636053391/50000000000000 : ℝ)*(base23) + (70346751/100000000000000 : ℝ)*(lower2) + (132921683/100000000000000 : ℝ)*(upper3) + (2063853/1562500000000 : ℝ)*(upper5) + (5949246711114033/100000000000000 : ℝ)*(major0) + (5949246711114033/100000000000000 : ℝ)*(major1) + (2974623355557017/50000000000000 : ℝ)*(major2) + (3968477708190043/50000000000000 : ℝ)*(sp0) + (1587398231223661/20000000000000 : ℝ)*(sp1) + (396849566317577/5000000000000 : ℝ)*(sp2) + (15474535453633/390625000000 : ℝ)*(sp3) + (37182078237/100000000000000 : ℝ)*(sp4) + (19496911329/100000000000000 : ℝ)*(sp7) + (3961500573041377/100000000000000 : ℝ)*(f.failure) + (3968496299229161/50000000000000 : ℝ)*(f.sum) + (196692528354063/26710000000000000000000000000 : ℝ)*base65 + (6973029390331699899/1335500000000000000000000000000000 : ℝ)*base68 + (7818647442421518251/667750000000000000000000000000000 : ℝ)*base70 + (11143969361097699899/1335500000000000000000000000000000 : ℝ)*base72 + (93900016131143/26710000000000000000000000000 : ℝ)*base73 + (407277720291231749/667750000000000000000000000000000 : ℝ)*base75 + (24666243255741850101/1335500000000000000000000000000000 : ℝ)*base77 + (227311402169850101/1335500000000000000000000000000000 : ℝ)*base79 + (2399600577121/6677500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (16253173/2500000000000000000000 : ℝ)*base89 + (16253173/2500000000000000000000 : ℝ)*base91 + (8746827/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (825476945470794483814592817/133550000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1100806263/100000000000000 : ℝ)*(base19) + (24252121/2000000000000 : ℝ)*(base23) + (7723351/2000000000000 : ℝ)*(lower1) + (62934071/50000000000000 : ℝ)*(upper3) + (8976213/20000000000000 : ℝ)*(lower4) + (122635637/100000000000000 : ℝ)*(upper5) + (1195857149488287/20000000000000 : ℝ)*(major0) + (1195857149488287/20000000000000 : ℝ)*(major1) + (1195857149488287/20000000000000 : ℝ)*(major2) + (697526473/25000000000000 : ℝ)*(sp2) + (7977068240636137/100000000000000 : ℝ)*(sp4) + (63816537118639/800000000000 : ℝ)*(sp5) + (1994266059481049/25000000000000 : ℝ)*(sp6) + (995375762053069/25000000000000 : ℝ)*(sp7) + (995375762053069/25000000000000 : ℝ)*(f.failure) + (7977068240636137/100000000000000 : ℝ)*(f.sum) + (9941696233671/2671000000000000000000000000 : ℝ)*base66 + (24260836323792369061/267100000000000000000000000000000 : ℝ)*base68 + (415089083914069061/267100000000000000000000000000000 : ℝ)*base70 + (24496053738644869061/267100000000000000000000000000000 : ℝ)*base72 + (4475610430707/2671000000000000000000000000 : ℝ)*base74 + (11602942845808730939/267100000000000000000000000000000 : ℝ)*base75 + (164783451147030939/267100000000000000000000000000000 : ℝ)*base77 + (1495344750917369061/267100000000000000000000000000000 : ℝ)*base80 + (11256256575947/2671000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (306719/625000000000000000000 : ℝ)*base90 + (306719/625000000000000000000 : ℝ)*base92 + (306719/625000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1178_s8 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1407/10000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11399/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1178_s8 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1178_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1178_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1178_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1178_s8 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (57/500 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14069/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1178_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
