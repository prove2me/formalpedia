-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1178_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:48:27.859625+00:00
-- url     : https://prove2.me/submissions/73f24a74-7a6d-46b2-82cf-a5f5c37d2596

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
theorem support_rectangle_w1178_s3_0 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1073180497/5000000000 : ℝ)*x 0 + (678197003/1250000000 : ℝ)*x 1 + (654418919/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1073180497/5000000000 : ℝ)^8371 ≤ (13038972690993/100000000000000 : ℝ)^6323 := by
    have hnat : (1073180497 : ℕ)^8371*100000000000000^6323 ≤ 13038972690993^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1073180497 5000000000 13038972690993 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (678197003/1250000000 : ℝ)^8371 ≤ (22253775209743/50000000000000 : ℝ)^6323 := by
    have hnat : (678197003 : ℕ)^8371*50000000000000^6323 ≤ 22253775209743^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      678197003 1250000000 22253775209743 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (654418919/1250000000 : ℝ)^8371 ≤ (42453476878451/100000000000000 : ℝ)^6323 := by
    have hnat : (654418919 : ℕ)^8371*100000000000000^6323 ≤ 42453476878451^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654418919 1250000000 42453476878451 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1073180497/5000000000 : ℝ), (678197003/1250000000 : ℝ), (654418919/1250000000 : ℝ)] ![(13038972690993/100000000000000 : ℝ), (22253775209743/50000000000000 : ℝ), (42453476878451/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1073180497/5000000000 : ℝ)|^8371 ≤ (13038972690993/100000000000000 : ℝ)^6323
        have hw : |(-1073180497/5000000000 : ℝ)|=(1073180497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(678197003/1250000000 : ℝ)|^8371 ≤ (22253775209743/50000000000000 : ℝ)^6323
        have hw : |(678197003/1250000000 : ℝ)|=(678197003/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(654418919/1250000000 : ℝ)|^8371 ≤ (42453476878451/100000000000000 : ℝ)^6323
        have hw : |(654418919/1250000000 : ℝ)|=(654418919/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s3_1 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5352942951/10000000000 : ℝ)*x 0 + (-448704613/2000000000 : ℝ)*x 1 + (1047070231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5352942951/10000000000 : ℝ)^8371 ≤ (5465056062943/12500000000000 : ℝ)^6323 := by
    have hnat : (5352942951 : ℕ)^8371*12500000000000^6323 ≤ 5465056062943^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5352942951 10000000000 5465056062943 12500000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (448704613/2000000000 : ℝ)^8371 ≤ (6913038361077/50000000000000 : ℝ)^6323 := by
    have hnat : (448704613 : ℕ)^8371*50000000000000^6323 ≤ 6913038361077^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      448704613 2000000000 6913038361077 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1047070231/2000000000 : ℝ)^8371 ≤ (42453474763561/100000000000000 : ℝ)^6323 := by
    have hnat : (1047070231 : ℕ)^8371*100000000000000^6323 ≤ 42453474763561^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1047070231 2000000000 42453474763561 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5352942951/10000000000 : ℝ), (-448704613/2000000000 : ℝ), (1047070231/2000000000 : ℝ)] ![(5465056062943/12500000000000 : ℝ), (6913038361077/50000000000000 : ℝ), (42453474763561/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5352942951/10000000000 : ℝ)|^8371 ≤ (5465056062943/12500000000000 : ℝ)^6323
        have hw : |(5352942951/10000000000 : ℝ)|=(5352942951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-448704613/2000000000 : ℝ)|^8371 ≤ (6913038361077/50000000000000 : ℝ)^6323
        have hw : |(-448704613/2000000000 : ℝ)|=(448704613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1047070231/2000000000 : ℝ)|^8371 ≤ (42453474763561/100000000000000 : ℝ)^6323
        have hw : |(1047070231/2000000000 : ℝ)|=(1047070231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s3_2 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2676471519/5000000000 : ℝ)*x 0 + (523535113/1000000000 : ℝ)*x 1 + (-1121761491/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2676471519/5000000000 : ℝ)^8371 ≤ (1748817977771/4000000000000 : ℝ)^6323 := by
    have hnat : (2676471519 : ℕ)^8371*4000000000000^6323 ≤ 1748817977771^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2676471519 5000000000 1748817977771 4000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (523535113/1000000000 : ℝ)^8371 ≤ (21226737247587/50000000000000 : ℝ)^6323 := by
    have hnat : (523535113 : ℕ)^8371*50000000000000^6323 ≤ 21226737247587^6323*1000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      523535113 1000000000 21226737247587 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1121761491/5000000000 : ℝ)^8371 ≤ (13826076044979/100000000000000 : ℝ)^6323 := by
    have hnat : (1121761491 : ℕ)^8371*100000000000000^6323 ≤ 13826076044979^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1121761491 5000000000 13826076044979 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2676471519/5000000000 : ℝ), (523535113/1000000000 : ℝ), (-1121761491/5000000000 : ℝ)] ![(1748817977771/4000000000000 : ℝ), (21226737247587/50000000000000 : ℝ), (13826076044979/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2676471519/5000000000 : ℝ)|^8371 ≤ (1748817977771/4000000000000 : ℝ)^6323
        have hw : |(2676471519/5000000000 : ℝ)|=(2676471519/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(523535113/1000000000 : ℝ)|^8371 ≤ (21226737247587/50000000000000 : ℝ)^6323
        have hw : |(523535113/1000000000 : ℝ)|=(523535113/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1121761491/5000000000 : ℝ)|^8371 ≤ (13826076044979/100000000000000 : ℝ)^6323
        have hw : |(-1121761491/5000000000 : ℝ)|=(1121761491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s3_3 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2178793883/5000000000 : ℝ)*x 0 + (166845337/400000000 : ℝ)*x 1 + (2276127357/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178793883/5000000000 : ℝ)^8371 ≤ (2081033684769/6250000000000 : ℝ)^6323 := by
    have hnat : (2178793883 : ℕ)^8371*6250000000000^6323 ≤ 2081033684769^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178793883 5000000000 2081033684769 6250000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (166845337/400000000 : ℝ)^8371 ≤ (122748331403/390625000000 : ℝ)^6323 := by
    have hnat : (166845337 : ℕ)^8371*390625000000^6323 ≤ 122748331403^6323*400000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      166845337 400000000 122748331403 390625000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2276127357/5000000000 : ℝ)^8371 ≤ (35279888189711/100000000000000 : ℝ)^6323 := by
    have hnat : (2276127357 : ℕ)^8371*100000000000000^6323 ≤ 35279888189711^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2276127357 5000000000 35279888189711 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178793883/5000000000 : ℝ), (166845337/400000000 : ℝ), (2276127357/5000000000 : ℝ)] ![(2081033684769/6250000000000 : ℝ), (122748331403/390625000000 : ℝ), (35279888189711/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178793883/5000000000 : ℝ)|^8371 ≤ (2081033684769/6250000000000 : ℝ)^6323
        have hw : |(2178793883/5000000000 : ℝ)|=(2178793883/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(166845337/400000000 : ℝ)|^8371 ≤ (122748331403/390625000000 : ℝ)^6323
        have hw : |(166845337/400000000 : ℝ)|=(166845337/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2276127357/5000000000 : ℝ)|^8371 ≤ (35279888189711/100000000000000 : ℝ)^6323
        have hw : |(2276127357/5000000000 : ℝ)|=(2276127357/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s3_4 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2146377343/10000000000 : ℝ)*x 0 + (1309017853/2500000000 : ℝ)*x 1 + (54248521/100000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2146377343/10000000000 : ℝ)^8371 ≤ (3259776044777/25000000000000 : ℝ)^6323 := by
    have hnat : (2146377343 : ℕ)^8371*25000000000000^6323 ≤ 3259776044777^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2146377343 10000000000 3259776044777 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1309017853/2500000000 : ℝ)^8371 ≤ (10615301810641/25000000000000 : ℝ)^6323 := by
    have hnat : (1309017853 : ℕ)^8371*25000000000000^6323 ≤ 10615301810641^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1309017853 2500000000 10615301810641 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54248521/100000000 : ℝ)^8371 ≤ (44499688554353/100000000000000 : ℝ)^6323 := by
    have hnat : (54248521 : ℕ)^8371*100000000000000^6323 ≤ 44499688554353^6323*100000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54248521 100000000 44499688554353 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2146377343/10000000000 : ℝ), (1309017853/2500000000 : ℝ), (54248521/100000000 : ℝ)] ![(3259776044777/25000000000000 : ℝ), (10615301810641/25000000000000 : ℝ), (44499688554353/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2146377343/10000000000 : ℝ)|^8371 ≤ (3259776044777/25000000000000 : ℝ)^6323
        have hw : |(-2146377343/10000000000 : ℝ)|=(2146377343/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1309017853/2500000000 : ℝ)|^8371 ≤ (10615301810641/25000000000000 : ℝ)^6323
        have hw : |(1309017853/2500000000 : ℝ)|=(1309017853/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(54248521/100000000 : ℝ)|^8371 ≤ (44499688554353/100000000000000 : ℝ)^6323
        have hw : |(54248521/100000000 : ℝ)|=(54248521/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s3_5 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5304624989/10000000000 : ℝ)*x 0 + (-513505679/2500000000 : ℝ)*x 1 + (2712425993/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5304624989/10000000000 : ℝ)^8371 ≤ (21599375871409/50000000000000 : ℝ)^6323 := by
    have hnat : (5304624989 : ℕ)^8371*50000000000000^6323 ≤ 21599375871409^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5304624989 10000000000 21599375871409 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (513505679/2500000000 : ℝ)^8371 ≤ (6150780463067/50000000000000 : ℝ)^6323 := by
    have hnat : (513505679 : ℕ)^8371*50000000000000^6323 ≤ 6150780463067^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      513505679 2500000000 6150780463067 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2712425993/5000000000 : ℝ)^8371 ≤ (11124921829083/25000000000000 : ℝ)^6323 := by
    have hnat : (2712425993 : ℕ)^8371*25000000000000^6323 ≤ 11124921829083^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2712425993 5000000000 11124921829083 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5304624989/10000000000 : ℝ), (-513505679/2500000000 : ℝ), (2712425993/5000000000 : ℝ)] ![(21599375871409/50000000000000 : ℝ), (6150780463067/50000000000000 : ℝ), (11124921829083/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5304624989/10000000000 : ℝ)|^8371 ≤ (21599375871409/50000000000000 : ℝ)^6323
        have hw : |(5304624989/10000000000 : ℝ)|=(5304624989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-513505679/2500000000 : ℝ)|^8371 ≤ (6150780463067/50000000000000 : ℝ)^6323
        have hw : |(-513505679/2500000000 : ℝ)|=(513505679/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2712425993/5000000000 : ℝ)|^8371 ≤ (11124921829083/25000000000000 : ℝ)^6323
        have hw : |(2712425993/5000000000 : ℝ)|=(2712425993/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s3_6 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1060925219/2000000000 : ℝ)*x 0 + (5424850947/10000000000 : ℝ)*x 1 + (-410804527/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060925219/2000000000 : ℝ)^8371 ≤ (10799690916731/25000000000000 : ℝ)^6323 := by
    have hnat : (1060925219 : ℕ)^8371*25000000000000^6323 ≤ 10799690916731^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060925219 2000000000 10799690916731 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424850947/10000000000 : ℝ)^8371 ≤ (11124919008241/25000000000000 : ℝ)^6323 := by
    have hnat : (5424850947 : ℕ)^8371*25000000000000^6323 ≤ 11124919008241^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424850947 10000000000 11124919008241 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (410804527/2000000000 : ℝ)^8371 ≤ (12301560283899/100000000000000 : ℝ)^6323 := by
    have hnat : (410804527 : ℕ)^8371*100000000000000^6323 ≤ 12301560283899^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      410804527 2000000000 12301560283899 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060925219/2000000000 : ℝ), (5424850947/10000000000 : ℝ), (-410804527/2000000000 : ℝ)] ![(10799690916731/25000000000000 : ℝ), (11124919008241/25000000000000 : ℝ), (12301560283899/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060925219/2000000000 : ℝ)|^8371 ≤ (10799690916731/25000000000000 : ℝ)^6323
        have hw : |(1060925219/2000000000 : ℝ)|=(1060925219/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424850947/10000000000 : ℝ)|^8371 ≤ (11124919008241/25000000000000 : ℝ)^6323
        have hw : |(5424850947/10000000000 : ℝ)|=(5424850947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-410804527/2000000000 : ℝ)|^8371 ≤ (12301560283899/100000000000000 : ℝ)^6323
        have hw : |(-410804527/2000000000 : ℝ)|=(410804527/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s3_7 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (17430481/40000000 : ℝ)*x 0 + (11377031/25000000 : ℝ)*x 1 + (32598313/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (17430481/40000000 : ℝ)^8371 ≤ (665937351271/2000000000000 : ℝ)^6323 := by
    have hnat : (17430481 : ℕ)^8371*2000000000000^6323 ≤ 665937351271^6323*40000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      17430481 40000000 665937351271 2000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (11377031/25000000 : ℝ)^8371 ≤ (17632545276879/50000000000000 : ℝ)^6323 := by
    have hnat : (11377031 : ℕ)^8371*50000000000000^6323 ≤ 17632545276879^6323*25000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      11377031 25000000 17632545276879 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (32598313/78125000 : ℝ)^8371 ≤ (31438041870183/100000000000000 : ℝ)^6323 := by
    have hnat : (32598313 : ℕ)^8371*100000000000000^6323 ≤ 31438041870183^6323*78125000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      32598313 78125000 31438041870183 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(17430481/40000000 : ℝ), (11377031/25000000 : ℝ), (32598313/78125000 : ℝ)] ![(665937351271/2000000000000 : ℝ), (17632545276879/50000000000000 : ℝ), (31438041870183/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(17430481/40000000 : ℝ)|^8371 ≤ (665937351271/2000000000000 : ℝ)^6323
        have hw : |(17430481/40000000 : ℝ)|=(17430481/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(11377031/25000000 : ℝ)|^8371 ≤ (17632545276879/50000000000000 : ℝ)^6323
        have hw : |(11377031/25000000 : ℝ)|=(11377031/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(32598313/78125000 : ℝ)|^8371 ≤ (31438041870183/100000000000000 : ℝ)^6323
        have hw : |(32598313/78125000 : ℝ)|=(32598313/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1178_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8199/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (923/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10739/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2953/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (8199/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (923/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (8199/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (923/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (8199/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (923/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (8199/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (923/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (8199/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (923/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (8199/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (923/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (923/10000 : ℝ) ^ (4185/1024 : ℝ) ≤ (2950110507427877/50000000000000000000 : ℝ) := by
    have hpowers : (923/10000 : ℝ)^4185 ≤ (2950110507427877/50000000000000000000 : ℝ)^1024 := by
      have hnat : (923 : ℕ)^4185*50000000000000000000^1024 ≤ 2950110507427877^1024*10000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        923 10000 2950110507427877 50000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (923/10000 : ℝ)) (X := (2950110507427877/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (8199/50000 : ℝ) ^ (4185/1024 : ℝ) ≤ (15447486438893787/25000000000000000000 : ℝ) := by
    have hpowers : (8199/50000 : ℝ)^4185 ≤ (15447486438893787/25000000000000000000 : ℝ)^1024 := by
      have hnat : (8199 : ℕ)^4185*25000000000000000000^1024 ≤ 15447486438893787^1024*50000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8199 50000 15447486438893787 25000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8199/50000 : ℝ)) (X := (15447486438893787/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25002950110507427877/25000000000000000000 : ℝ) ≤ (1000028872435277/1000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (25002950110507427877/25000000000000000000 : ℝ)^1024 ≤ (1000028872435277/1000000000000000 : ℝ)^4185 := by
      have hnat : (25002950110507427877 : ℕ)^1024*1000000000000000^4185 ≤ 1000028872435277^4185*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25002950110507427877 25000000000000000000 1000028872435277 1000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000028872435277/1000000000000000 : ℝ)) (X := (25002950110507427877/25000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50033845083385215451/50000000000000000000 : ℝ) ≤ (2000331168546431/2000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (50033845083385215451/50000000000000000000 : ℝ)^1024 ≤ (2000331168546431/2000000000000000 : ℝ)^4185 := by
      have hnat : (50033845083385215451 : ℕ)^1024*2000000000000000^4185 ≤ 2000331168546431^4185*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50033845083385215451 50000000000000000000 2000331168546431 2000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2000331168546431/2000000000000000 : ℝ)) (X := (50033845083385215451/50000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12515447486438893787/12500000000000000000 : ℝ) ≤ (500151148055577/500000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (12515447486438893787/12500000000000000000 : ℝ)^1024 ≤ (500151148055577/500000000000000 : ℝ)^4185 := by
      have hnat : (12515447486438893787 : ℕ)^1024*500000000000000^4185 ≤ 500151148055577^4185*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12515447486438893787 12500000000000000000 500151148055577 500000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500151148055577/500000000000000 : ℝ)) (X := (12515447486438893787/12500000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2950110507427877/50000000000000000000 : ℝ) ≤ ((3582841628543860413/3584000000000000000 : ℝ)+2*(273423675877/143360000000000 : ℝ)*(923/10000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (3582841628543860413/3584000000000000000 : ℝ)+2*(273423675877/143360000000000 : ℝ)*(923/10000 : ℝ)=(1000028872435277/1000000000000000 : ℝ) by norm_num, show 1+2*(2950110507427877/50000000000000000000 : ℝ)=(25002950110507427877/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(15447486438893787/25000000000000000000 : ℝ)+(2950110507427877/50000000000000000000 : ℝ) ≤ ((3582841628543860413/3584000000000000000 : ℝ)+(273423675877/143360000000000 : ℝ)*((8199/50000 : ℝ)+(923/10000 : ℝ)))^(4185/1024 : ℝ) := by
    rw [show (3582841628543860413/3584000000000000000 : ℝ)+(273423675877/143360000000000 : ℝ)*((8199/50000 : ℝ)+(923/10000 : ℝ))=(2000331168546431/2000000000000000 : ℝ) by norm_num, show 1+(15447486438893787/25000000000000000000 : ℝ)+(2950110507427877/50000000000000000000 : ℝ)=(50033845083385215451/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(15447486438893787/25000000000000000000 : ℝ) ≤ ((3582841628543860413/3584000000000000000 : ℝ)+2*(273423675877/143360000000000 : ℝ)*(8199/50000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (3582841628543860413/3584000000000000000 : ℝ)+2*(273423675877/143360000000000 : ℝ)*(8199/50000 : ℝ)=(500151148055577/500000000000000 : ℝ) by norm_num, show 1+2*(15447486438893787/25000000000000000000 : ℝ)=(12515447486438893787/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3582841628543860413/3584000000000000000 : ℝ)*(X 1 0+X 2 0)+(273423675877/143360000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (923/10000 : ℝ)) (hi := (8199/50000 : ℝ)) (c := (3582841628543860413/3584000000000000000 : ℝ)) (alpha := (273423675877/143360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3582841628543860413/3584000000000000000 : ℝ)*(X 0 1+X 2 1)+(273423675877/143360000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (923/10000 : ℝ)) (hi := (8199/50000 : ℝ)) (c := (3582841628543860413/3584000000000000000 : ℝ)) (alpha := (273423675877/143360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3582841628543860413/3584000000000000000 : ℝ)*(X 0 2+X 1 2)+(273423675877/143360000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (923/10000 : ℝ)) (hi := (8199/50000 : ℝ)) (c := (3582841628543860413/3584000000000000000 : ℝ)) (alpha := (273423675877/143360000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1073180497/5000000000 : ℝ)*X 0 0+(678197003/1250000000 : ℝ)*X 0 1+(654418919/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5352942951/10000000000 : ℝ)*X 1 0+(-448704613/2000000000 : ℝ)*X 1 1+(1047070231/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2676471519/5000000000 : ℝ)*X 2 0+(523535113/1000000000 : ℝ)*X 2 1+(-1121761491/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178793883/5000000000 : ℝ)*X 0 0+(166845337/400000000 : ℝ)*X 0 1+(2276127357/5000000000 : ℝ)*X 0 2+(2178793883/5000000000 : ℝ)*X 1 0+(166845337/400000000 : ℝ)*X 1 1+(2276127357/5000000000 : ℝ)*X 1 2+(2178793883/5000000000 : ℝ)*X 2 0+(166845337/400000000 : ℝ)*X 2 1+(2276127357/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2146377343/10000000000 : ℝ)*X 0 0+(1309017853/2500000000 : ℝ)*X 0 1+(54248521/100000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5304624989/10000000000 : ℝ)*X 1 0+(-513505679/2500000000 : ℝ)*X 1 1+(2712425993/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060925219/2000000000 : ℝ)*X 2 0+(5424850947/10000000000 : ℝ)*X 2 1+(-410804527/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((17430481/40000000 : ℝ)*X 0 0+(11377031/25000000 : ℝ)*X 0 1+(32598313/78125000 : ℝ)*X 0 2+(17430481/40000000 : ℝ)*X 1 0+(11377031/25000000 : ℝ)*X 1 1+(32598313/78125000 : ℝ)*X 1 2+(17430481/40000000 : ℝ)*X 2 0+(11377031/25000000 : ℝ)*X 2 1+(32598313/78125000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (52505722985073320840244201/8960000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1432105869/100000000000000 : ℝ)*(base19) + (1402973891/100000000000000 : ℝ)*(base23) + (61329953/100000000000000 : ℝ)*(lower2) + (15735367/12500000000000 : ℝ)*(upper3) + (144704353/100000000000000 : ℝ)*(upper5) + (394042346997459/10000000000000 : ℝ)*(major0) + (394042346997459/10000000000000 : ℝ)*(major1) + (394042346997459/10000000000000 : ℝ)*(major2) + (5256962952597879/100000000000000 : ℝ)*(sp0) + (164280794383437/3125000000000 : ℝ)*(sp1) + (2628492724700981/50000000000000 : ℝ)*(sp2) + (262384797803981/10000000000000 : ℝ)*(sp3) + (11949888987/50000000000000 : ℝ)*(sp4) + (5957099859/50000000000000 : ℝ)*(sp7) + (327982486529941/12500000000000 : ℝ)*(f.failure) + (5256986852375853/100000000000000 : ℝ)*(f.sum) + (7750351498053/3584000000000000000000000000 : ℝ)*base66 + (172104216175294433/35840000000000000000000000000000 : ℝ)*base68 + (589726277548734433/35840000000000000000000000000000 : ℝ)*base70 + (624452259370305567/35840000000000000000000000000000 : ℝ)*base71 + (2087736487489/716800000000000000000000000 : ℝ)*base74 + (647916234586814433/35840000000000000000000000000000 : ℝ)*base76 + (106029939178174433/35840000000000000000000000000000 : ℝ)*base78 + (27188210963134433/35840000000000000000000000000000 : ℝ)*base80 + (9356300524357/3584000000000000000000000000 : ℝ)*base82 + (4115209/312500000000000000000 : ℝ)*base89 + (4115209/312500000000000000000 : ℝ)*base91 + (4115209/312500000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (494228666044201806177/51200000000000000000000000 : ℝ) := by norm_num
    linear_combination (1202192939/100000000000000 : ℝ)*(base19) + (2419903889/100000000000000 : ℝ)*(base23) + (18885519/12500000000000 : ℝ)*(upper3) + (16768999/100000000000000 : ℝ)*(lower4) + (50688793/50000000000000 : ℝ)*(upper5) + (198526711611011/5000000000000 : ℝ)*(major0) + (198526711611011/5000000000000 : ℝ)*(major1) + (198526711611011/5000000000000 : ℝ)*(major2) + (3573064097/20000000000000 : ℝ)*(sp1) + (1676911433/6250000000000 : ℝ)*(sp2) + (5297158014217133/100000000000000 : ℝ)*(sp4) + (529713894670371/10000000000000 : ℝ)*(sp5) + (1324282190932579/25000000000000 : ℝ)*(sp6) + (660977532114961/25000000000000 : ℝ)*(sp7) + (660977532114961/25000000000000 : ℝ)*(f.failure) + (5297158014217133/100000000000000 : ℝ)*(f.sum) + (319842812931/256000000000000000000000000 : ℝ)*base66 + (14559805193905351/2560000000000000000000000000000 : ℝ)*base68 + (26108385730894649/2560000000000000000000000000000 : ℝ)*base69 + (20977259691854649/2560000000000000000000000000000 : ℝ)*base71 + (280476944487/51200000000000000000000000 : ℝ)*base74 + (53574043542705351/2560000000000000000000000000000 : ℝ)*base76 + (3226755092814649/2560000000000000000000000000000 : ℝ)*base77 + (27377254399665351/2560000000000000000000000000000 : ℝ)*base80 + (117275374951/51200000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (5913189/625000000000000000000 : ℝ)*base89 + (5913189/625000000000000000000 : ℝ)*base91 + (5913189/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1178_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8199/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (923/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10739/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1178_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1178_s4_0 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149086621/10000000000 : ℝ)*x 0 + (5400224081/10000000000 : ℝ)*x 1 + (42071353/80000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149086621/10000000000 : ℝ)^8371 ≤ (6530449119871/50000000000000 : ℝ)^6323 := by
    have hnat : (2149086621 : ℕ)^8371*50000000000000^6323 ≤ 6530449119871^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149086621 10000000000 6530449119871 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5400224081/10000000000 : ℝ)^8371 ≤ (11058107292839/25000000000000 : ℝ)^6323 := by
    have hnat : (5400224081 : ℕ)^8371*25000000000000^6323 ≤ 11058107292839^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5400224081 10000000000 11058107292839 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (42071353/80000000 : ℝ)^8371 ≤ (42706672574213/100000000000000 : ℝ)^6323 := by
    have hnat : (42071353 : ℕ)^8371*100000000000000^6323 ≤ 42706672574213^6323*80000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      42071353 80000000 42706672574213 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149086621/10000000000 : ℝ), (5400224081/10000000000 : ℝ), (42071353/80000000 : ℝ)] ![(6530449119871/50000000000000 : ℝ), (11058107292839/25000000000000 : ℝ), (42706672574213/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149086621/10000000000 : ℝ)|^8371 ≤ (6530449119871/50000000000000 : ℝ)^6323
        have hw : |(-2149086621/10000000000 : ℝ)|=(2149086621/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5400224081/10000000000 : ℝ)|^8371 ≤ (11058107292839/25000000000000 : ℝ)^6323
        have hw : |(5400224081/10000000000 : ℝ)|=(5400224081/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(42071353/80000000 : ℝ)|^8371 ≤ (42706672574213/100000000000000 : ℝ)^6323
        have hw : |(42071353/80000000 : ℝ)|=(42071353/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s4_1 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5346589279/10000000000 : ℝ)*x 0 + (-1110435223/5000000000 : ℝ)*x 1 + (164341237/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5346589279/10000000000 : ℝ)^8371 ≤ (43651759465803/100000000000000 : ℝ)^6323 := by
    have hnat : (5346589279 : ℕ)^8371*100000000000000^6323 ≤ 43651759465803^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5346589279 10000000000 43651759465803 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1110435223/5000000000 : ℝ)^8371 ≤ (1705195376081/12500000000000 : ℝ)^6323 := by
    have hnat : (1110435223 : ℕ)^8371*12500000000000^6323 ≤ 1705195376081^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110435223 5000000000 1705195376081 12500000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164341237/312500000 : ℝ)^8371 ≤ (42706677508973/100000000000000 : ℝ)^6323 := by
    have hnat : (164341237 : ℕ)^8371*100000000000000^6323 ≤ 42706677508973^6323*312500000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164341237 312500000 42706677508973 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5346589279/10000000000 : ℝ), (-1110435223/5000000000 : ℝ), (164341237/312500000 : ℝ)] ![(43651759465803/100000000000000 : ℝ), (1705195376081/12500000000000 : ℝ), (42706677508973/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5346589279/10000000000 : ℝ)|^8371 ≤ (43651759465803/100000000000000 : ℝ)^6323
        have hw : |(5346589279/10000000000 : ℝ)|=(5346589279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1110435223/5000000000 : ℝ)|^8371 ≤ (1705195376081/12500000000000 : ℝ)^6323
        have hw : |(-1110435223/5000000000 : ℝ)|=(1110435223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164341237/312500000 : ℝ)|^8371 ≤ (42706677508973/100000000000000 : ℝ)^6323
        have hw : |(164341237/312500000 : ℝ)|=(164341237/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s4_2 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (668323663/1250000000 : ℝ)*x 0 + (1314730013/2500000000 : ℝ)*x 1 + (-1110434897/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668323663/1250000000 : ℝ)^8371 ≤ (5456469967003/12500000000000 : ℝ)^6323 := by
    have hnat : (668323663 : ℕ)^8371*12500000000000^6323 ≤ 5456469967003^6323*1250000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668323663 1250000000 5456469967003 12500000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1314730013/2500000000 : ℝ)^8371 ≤ (21353341270247/50000000000000 : ℝ)^6323 := by
    have hnat : (1314730013 : ℕ)^8371*50000000000000^6323 ≤ 21353341270247^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1314730013 2500000000 21353341270247 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1110434897/5000000000 : ℝ)^8371 ≤ (3410389426653/25000000000000 : ℝ)^6323 := by
    have hnat : (1110434897 : ℕ)^8371*25000000000000^6323 ≤ 3410389426653^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1110434897 5000000000 3410389426653 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668323663/1250000000 : ℝ), (1314730013/2500000000 : ℝ), (-1110434897/5000000000 : ℝ)] ![(5456469967003/12500000000000 : ℝ), (21353341270247/50000000000000 : ℝ), (3410389426653/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668323663/1250000000 : ℝ)|^8371 ≤ (5456469967003/12500000000000 : ℝ)^6323
        have hw : |(668323663/1250000000 : ℝ)|=(668323663/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1314730013/2500000000 : ℝ)|^8371 ≤ (21353341270247/50000000000000 : ℝ)^6323
        have hw : |(1314730013/2500000000 : ℝ)|=(1314730013/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1110434897/5000000000 : ℝ)|^8371 ≤ (3410389426653/25000000000000 : ℝ)^6323
        have hw : |(-1110434897/5000000000 : ℝ)|=(1110434897/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s4_3 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359217631/10000000000 : ℝ)*x 0 + (2109964819/5000000000 : ℝ)*x 1 + (4503037951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359217631/10000000000 : ℝ)^8371 ≤ (33313027604321/100000000000000 : ℝ)^6323 := by
    have hnat : (4359217631 : ℕ)^8371*100000000000000^6323 ≤ 33313027604321^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359217631 10000000000 33313027604321 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2109964819/5000000000 : ℝ)^8371 ≤ (31911170511301/100000000000000 : ℝ)^6323 := by
    have hnat : (2109964819 : ℕ)^8371*100000000000000^6323 ≤ 31911170511301^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2109964819 5000000000 31911170511301 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4503037951/10000000000 : ℝ)^8371 ≤ (3477580186931/10000000000000 : ℝ)^6323 := by
    have hnat : (4503037951 : ℕ)^8371*10000000000000^6323 ≤ 3477580186931^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4503037951 10000000000 3477580186931 10000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359217631/10000000000 : ℝ), (2109964819/5000000000 : ℝ), (4503037951/10000000000 : ℝ)] ![(33313027604321/100000000000000 : ℝ), (31911170511301/100000000000000 : ℝ), (3477580186931/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359217631/10000000000 : ℝ)|^8371 ≤ (33313027604321/100000000000000 : ℝ)^6323
        have hw : |(4359217631/10000000000 : ℝ)|=(4359217631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2109964819/5000000000 : ℝ)|^8371 ≤ (31911170511301/100000000000000 : ℝ)^6323
        have hw : |(2109964819/5000000000 : ℝ)|=(2109964819/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4503037951/10000000000 : ℝ)|^8371 ≤ (3477580186931/10000000000000 : ℝ)^6323
        have hw : |(4503037951/10000000000 : ℝ)|=(4503037951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s4_4 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149093419/10000000000 : ℝ)*x 0 + (5259317521/10000000000 : ℝ)*x 1 + (2699912019/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149093419/10000000000 : ℝ)^8371 ≤ (13060952935629/100000000000000 : ℝ)^6323 := by
    have hnat : (2149093419 : ℕ)^8371*100000000000000^6323 ≤ 13060952935629^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149093419 10000000000 13060952935629 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259317521/10000000000 : ℝ)^8371 ≤ (10677738956737/25000000000000 : ℝ)^6323 := by
    have hnat : (5259317521 : ℕ)^8371*25000000000000^6323 ≤ 10677738956737^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259317521 10000000000 10677738956737 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699912019/5000000000 : ℝ)^8371 ≤ (11057022805107/25000000000000 : ℝ)^6323 := by
    have hnat : (2699912019 : ℕ)^8371*25000000000000^6323 ≤ 11057022805107^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699912019 5000000000 11057022805107 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149093419/10000000000 : ℝ), (5259317521/10000000000 : ℝ), (2699912019/5000000000 : ℝ)] ![(13060952935629/100000000000000 : ℝ), (10677738956737/25000000000000 : ℝ), (11057022805107/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149093419/10000000000 : ℝ)|^8371 ≤ (13060952935629/100000000000000 : ℝ)^6323
        have hw : |(-2149093419/10000000000 : ℝ)|=(2149093419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259317521/10000000000 : ℝ)|^8371 ≤ (10677738956737/25000000000000 : ℝ)^6323
        have hw : |(5259317521/10000000000 : ℝ)|=(5259317521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699912019/5000000000 : ℝ)|^8371 ≤ (11057022805107/25000000000000 : ℝ)^6323
        have hw : |(2699912019/5000000000 : ℝ)|=(2699912019/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s4_5 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310697413/10000000000 : ℝ)*x 0 + (-103998267/500000000 : ℝ)*x 1 + (1349956037/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310697413/10000000000 : ℝ)^8371 ≤ (43264232432399/100000000000000 : ℝ)^6323 := by
    have hnat : (5310697413 : ℕ)^8371*100000000000000^6323 ≤ 43264232432399^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310697413 10000000000 43264232432399 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (103998267/500000000 : ℝ)^8371 ≤ (6253837570469/50000000000000 : ℝ)^6323 := by
    have hnat : (103998267 : ℕ)^8371*50000000000000^6323 ≤ 6253837570469^6323*500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      103998267 500000000 6253837570469 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1349956037/2500000000 : ℝ)^8371 ≤ (22114046206611/50000000000000 : ℝ)^6323 := by
    have hnat : (1349956037 : ℕ)^8371*50000000000000^6323 ≤ 22114046206611^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1349956037 2500000000 22114046206611 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310697413/10000000000 : ℝ), (-103998267/500000000 : ℝ), (1349956037/2500000000 : ℝ)] ![(43264232432399/100000000000000 : ℝ), (6253837570469/50000000000000 : ℝ), (22114046206611/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310697413/10000000000 : ℝ)|^8371 ≤ (43264232432399/100000000000000 : ℝ)^6323
        have hw : |(5310697413/10000000000 : ℝ)|=(5310697413/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-103998267/500000000 : ℝ)|^8371 ≤ (6253837570469/50000000000000 : ℝ)^6323
        have hw : |(-103998267/500000000 : ℝ)|=(103998267/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1349956037/2500000000 : ℝ)|^8371 ≤ (22114046206611/50000000000000 : ℝ)^6323
        have hw : |(1349956037/2500000000 : ℝ)|=(1349956037/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s4_6 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5310697449/10000000000 : ℝ)*x 0 + (2699911991/5000000000 : ℝ)*x 1 + (-1039982759/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310697449/10000000000 : ℝ)^8371 ≤ (43264232820669/100000000000000 : ℝ)^6323 := by
    have hnat : (5310697449 : ℕ)^8371*100000000000000^6323 ≤ 43264232820669^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310697449 10000000000 43264232820669 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2699911991/5000000000 : ℝ)^8371 ≤ (44228090613187/100000000000000 : ℝ)^6323 := by
    have hnat : (2699911991 : ℕ)^8371*100000000000000^6323 ≤ 44228090613187^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699911991 5000000000 44228090613187 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1039982759/5000000000 : ℝ)^8371 ≤ (12507676558019/100000000000000 : ℝ)^6323 := by
    have hnat : (1039982759 : ℕ)^8371*100000000000000^6323 ≤ 12507676558019^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1039982759 5000000000 12507676558019 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310697449/10000000000 : ℝ), (2699911991/5000000000 : ℝ), (-1039982759/5000000000 : ℝ)] ![(43264232820669/100000000000000 : ℝ), (44228090613187/100000000000000 : ℝ), (12507676558019/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310697449/10000000000 : ℝ)|^8371 ≤ (43264232820669/100000000000000 : ℝ)^6323
        have hw : |(5310697449/10000000000 : ℝ)|=(5310697449/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2699911991/5000000000 : ℝ)|^8371 ≤ (44228090613187/100000000000000 : ℝ)^6323
        have hw : |(2699911991/5000000000 : ℝ)|=(2699911991/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1039982759/5000000000 : ℝ)|^8371 ≤ (12507676558019/100000000000000 : ℝ)^6323
        have hw : |(-1039982759/5000000000 : ℝ)|=(1039982759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s4_7 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179615149/5000000000 : ℝ)*x 0 + (4502240221/10000000000 : ℝ)*x 1 + (168829259/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179615149/5000000000 : ℝ)^8371 ≤ (33313155758771/100000000000000 : ℝ)^6323 := by
    have hnat : (2179615149 : ℕ)^8371*100000000000000^6323 ≤ 33313155758771^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179615149 5000000000 33313155758771 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4502240221/10000000000 : ℝ)^8371 ≤ (34767646020431/100000000000000 : ℝ)^6323 := by
    have hnat : (4502240221 : ℕ)^8371*100000000000000^6323 ≤ 34767646020431^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4502240221 10000000000 34767646020431 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168829259/400000000 : ℝ)^8371 ≤ (15959599105711/50000000000000 : ℝ)^6323 := by
    have hnat : (168829259 : ℕ)^8371*50000000000000^6323 ≤ 15959599105711^6323*400000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168829259 400000000 15959599105711 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179615149/5000000000 : ℝ), (4502240221/10000000000 : ℝ), (168829259/400000000 : ℝ)] ![(33313155758771/100000000000000 : ℝ), (34767646020431/100000000000000 : ℝ), (15959599105711/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179615149/5000000000 : ℝ)|^8371 ≤ (33313155758771/100000000000000 : ℝ)^6323
        have hw : |(2179615149/5000000000 : ℝ)|=(2179615149/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4502240221/10000000000 : ℝ)|^8371 ≤ (34767646020431/100000000000000 : ℝ)^6323
        have hw : |(4502240221/10000000000 : ℝ)|=(4502240221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168829259/400000000 : ℝ)|^8371 ≤ (15959599105711/50000000000000 : ℝ)^6323
        have hw : |(168829259/400000000 : ℝ)|=(168829259/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1178_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10739/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5621/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7117/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10739/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10739/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10739/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2953/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10739/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10739/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2953/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10739/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10739/100000 : ℝ) ^ (4185/1024 : ℝ) ≤ (2191101499196007/20000000000000000000 : ℝ) := by
    have hpowers : (10739/100000 : ℝ)^4185 ≤ (2191101499196007/20000000000000000000 : ℝ)^1024 := by
      have hnat : (10739 : ℕ)^4185*20000000000000000000^1024 ≤ 2191101499196007^1024*100000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10739 100000 2191101499196007 20000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10739/100000 : ℝ)) (X := (2191101499196007/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2953/20000 : ℝ) ^ (4185/1024 : ℝ) ≤ (1006163406191971/2500000000000000000 : ℝ) := by
    have hpowers : (2953/20000 : ℝ)^4185 ≤ (1006163406191971/2500000000000000000 : ℝ)^1024 := by
      have hnat : (2953 : ℕ)^4185*2500000000000000000^1024 ≤ 1006163406191971^1024*20000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2953 20000 1006163406191971 2500000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2953/20000 : ℝ)) (X := (1006163406191971/2500000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (10002191101499196007/10000000000000000000 : ℝ) ≤ (5000268040895647/5000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (10002191101499196007/10000000000000000000 : ℝ)^1024 ≤ (5000268040895647/5000000000000000 : ℝ)^4185 := by
      have hnat : (10002191101499196007 : ℕ)^1024*5000000000000000^4185 ≤ 5000268040895647^4185*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002191101499196007 10000000000000000000 5000268040895647 5000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000268040895647/5000000000000000 : ℝ)) (X := (10002191101499196007/10000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (800409616349949271/800000000000000000 : ℝ) ≤ (1250156573349261/1250000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (800409616349949271/800000000000000000 : ℝ)^1024 ≤ (1250156573349261/1250000000000000 : ℝ)^4185 := by
      have hnat : (800409616349949271 : ℕ)^1024*1250000000000000^4185 ≤ 1250156573349261^4185*800000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        800409616349949271 800000000000000000 1250156573349261 1250000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250156573349261/1250000000000000 : ℝ)) (X := (800409616349949271/800000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (1251006163406191971/1250000000000000000 : ℝ) ≤ (5000984545898441/5000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (1251006163406191971/1250000000000000000 : ℝ)^1024 ≤ (5000984545898441/5000000000000000 : ℝ)^4185 := by
      have hnat : (1251006163406191971 : ℕ)^1024*5000000000000000^4185 ≤ 5000984545898441^4185*1250000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1251006163406191971 1250000000000000000 5000984545898441 5000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000984545898441/5000000000000000 : ℝ)) (X := (1251006163406191971/1250000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2191101499196007/20000000000000000000 : ℝ) ≤ ((2515423073177608757/2516250000000000000 : ℝ)+2*(358252501397/201300000000000 : ℝ)*(10739/100000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (2515423073177608757/2516250000000000000 : ℝ)+2*(358252501397/201300000000000 : ℝ)*(10739/100000 : ℝ)=(5000268040895647/5000000000000000 : ℝ) by norm_num, show 1+2*(2191101499196007/20000000000000000000 : ℝ)=(10002191101499196007/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1006163406191971/2500000000000000000 : ℝ)+(2191101499196007/20000000000000000000 : ℝ) ≤ ((2515423073177608757/2516250000000000000 : ℝ)+(358252501397/201300000000000 : ℝ)*((2953/20000 : ℝ)+(10739/100000 : ℝ)))^(4185/1024 : ℝ) := by
    rw [show (2515423073177608757/2516250000000000000 : ℝ)+(358252501397/201300000000000 : ℝ)*((2953/20000 : ℝ)+(10739/100000 : ℝ))=(1250156573349261/1250000000000000 : ℝ) by norm_num, show 1+(1006163406191971/2500000000000000000 : ℝ)+(2191101499196007/20000000000000000000 : ℝ)=(800409616349949271/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1006163406191971/2500000000000000000 : ℝ) ≤ ((2515423073177608757/2516250000000000000 : ℝ)+2*(358252501397/201300000000000 : ℝ)*(2953/20000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (2515423073177608757/2516250000000000000 : ℝ)+2*(358252501397/201300000000000 : ℝ)*(2953/20000 : ℝ)=(5000984545898441/5000000000000000 : ℝ) by norm_num, show 1+2*(1006163406191971/2500000000000000000 : ℝ)=(1251006163406191971/1250000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (2515423073177608757/2516250000000000000 : ℝ)*(X 1 0+X 2 0)+(358252501397/201300000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (10739/100000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (2515423073177608757/2516250000000000000 : ℝ)) (alpha := (358252501397/201300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (2515423073177608757/2516250000000000000 : ℝ)*(X 0 1+X 2 1)+(358252501397/201300000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (10739/100000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (2515423073177608757/2516250000000000000 : ℝ)) (alpha := (358252501397/201300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (2515423073177608757/2516250000000000000 : ℝ)*(X 0 2+X 1 2)+(358252501397/201300000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (10739/100000 : ℝ)) (hi := (2953/20000 : ℝ)) (c := (2515423073177608757/2516250000000000000 : ℝ)) (alpha := (358252501397/201300000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2149086621/10000000000 : ℝ)*X 0 0+(5400224081/10000000000 : ℝ)*X 0 1+(42071353/80000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5346589279/10000000000 : ℝ)*X 1 0+(-1110435223/5000000000 : ℝ)*X 1 1+(164341237/312500000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((668323663/1250000000 : ℝ)*X 2 0+(1314730013/2500000000 : ℝ)*X 2 1+(-1110434897/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359217631/10000000000 : ℝ)*X 0 0+(2109964819/5000000000 : ℝ)*X 0 1+(4503037951/10000000000 : ℝ)*X 0 2+(4359217631/10000000000 : ℝ)*X 1 0+(2109964819/5000000000 : ℝ)*X 1 1+(4503037951/10000000000 : ℝ)*X 1 2+(4359217631/10000000000 : ℝ)*X 2 0+(2109964819/5000000000 : ℝ)*X 2 1+(4503037951/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2149093419/10000000000 : ℝ)*X 0 0+(5259317521/10000000000 : ℝ)*X 0 1+(2699912019/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310697413/10000000000 : ℝ)*X 1 0+(-103998267/500000000 : ℝ)*X 1 1+(1349956037/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5310697449/10000000000 : ℝ)*X 2 0+(2699911991/5000000000 : ℝ)*X 2 1+(-1039982759/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179615149/5000000000 : ℝ)*X 0 0+(4502240221/10000000000 : ℝ)*X 0 1+(168829259/400000000 : ℝ)*X 0 2+(2179615149/5000000000 : ℝ)*X 1 0+(4502240221/10000000000 : ℝ)*X 1 1+(168829259/400000000 : ℝ)*X 1 2+(2179615149/5000000000 : ℝ)*X 2 0+(4502240221/10000000000 : ℝ)*X 2 1+(168829259/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (198546171208861544034433757/41937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1238234393/100000000000000 : ℝ)*(base19) + (210767733/20000000000000 : ℝ)*(base23) + (34506531/25000000000000 : ℝ)*(lower2) + (74549669/12500000000000 : ℝ)*(upper5) + (5304633279859941/100000000000000 : ℝ)*(major0) + (5304633279859941/100000000000000 : ℝ)*(major1) + (2652316639929971/50000000000000 : ℝ)*(major2) + (1415386399532683/20000000000000 : ℝ)*(sp0) + (7076995476199843/100000000000000 : ℝ)*(sp1) + (7077001719015651/100000000000000 : ℝ)*(sp2) + (883061220838111/25000000000000 : ℝ)*(sp3) + (707751909/1000000000000 : ℝ)*(sp4) + (6058420079/100000000000000 : ℝ)*(sp5) + (18745701941/100000000000000 : ℝ)*(sp7) + (220766476815899/6250000000000 : ℝ)*(f.failure) + (1769250693213579/25000000000000 : ℝ)*(f.sum) + (4201566178469/1830000000000000000000000000 : ℝ)*base66 + (2413749420401778337/251625000000000000000000000000000 : ℝ)*base67 + (497102719600162703/125812500000000000000000000000000 : ℝ)*base70 + (8940442035957528337/251625000000000000000000000000000 : ℝ)*base71 + (9755088457709/1830000000000000000000000000 : ℝ)*base74 + (3925182201354975203/125812500000000000000000000000000 : ℝ)*base76 + (262164967603355279/83875000000000000000000000000000 : ℝ)*base77 + (2957887924137769721/83875000000000000000000000000000 : ℝ)*base80 + (3122241259879/838750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (187549/156250000000000000000 : ℝ)*base90 + (187549/156250000000000000000 : ℝ)*base92 + (1750049/156250000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (31267541390406415968485907/41937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (861993659/100000000000000 : ℝ)*(base19) + (262982903/20000000000000 : ℝ)*(base23) + (22846813/10000000000000 : ℝ)*(upper2) + (38260647/25000000000000 : ℝ)*(upper5) + (5334697392417549/100000000000000 : ℝ)*(major0) + (5334697392417549/100000000000000 : ℝ)*(major1) + (5334697392417549/100000000000000 : ℝ)*(major2) + (1831735611/100000000000000 : ℝ)*(sp0) + (8882439887/25000000000000 : ℝ)*(sp1) + (15876271763/50000000000000 : ℝ)*(sp2) + (7117110126193367/100000000000000 : ℝ)*(sp4) + (7117075566175771/100000000000000 : ℝ)*(sp5) + (7117078890470937/100000000000000 : ℝ)*(sp6) + (3552282802053623/100000000000000 : ℝ)*(sp7) + (3552282802053623/100000000000000 : ℝ)*(f.failure) + (3558555978964489/50000000000000 : ℝ)*(f.sum) + (2373463693901/3355000000000000000000000000 : ℝ)*base65 + (172283146605611969/83875000000000000000000000000000 : ℝ)*base68 + (525791882467513031/83875000000000000000000000000000 : ℝ)*base69 + (1058928588799111969/83875000000000000000000000000000 : ℝ)*base72 + (3618573930363/1677500000000000000000000000 : ℝ)*base73 + (622056073898888031/83875000000000000000000000000000 : ℝ)*base75 + (257664054745638031/83875000000000000000000000000000 : ℝ)*base77 + (1075251562050888031/83875000000000000000000000000000 : ℝ)*base79 + (4310976588087/1677500000000000000000000000 : ℝ)*base82 + (2901827/2500000000000000000000 : ℝ)*base89 + (2901827/2500000000000000000000 : ℝ)*base91 + (2901827/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1178_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2953/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10739/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1178_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1178_s5_0 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149650631/10000000000 : ℝ)*x 0 + (5393983247/10000000000 : ℝ)*x 1 + (2632394719/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149650631/10000000000 : ℝ)^8371 ≤ (6532718193303/50000000000000 : ℝ)^6323 := by
    have hnat : (2149650631 : ℕ)^8371*50000000000000^6323 ≤ 6532718193303^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149650631 10000000000 6532718193303 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5393983247/10000000000 : ℝ)^8371 ≤ (11041191806101/25000000000000 : ℝ)^6323 := by
    have hnat : (5393983247 : ℕ)^8371*25000000000000^6323 ≤ 11041191806101^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393983247 10000000000 11041191806101 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2632394719/5000000000 : ℝ)^8371 ≤ (21384898187811/50000000000000 : ℝ)^6323 := by
    have hnat : (2632394719 : ℕ)^8371*50000000000000^6323 ≤ 21384898187811^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2632394719 5000000000 21384898187811 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149650631/10000000000 : ℝ), (5393983247/10000000000 : ℝ), (2632394719/5000000000 : ℝ)] ![(6532718193303/50000000000000 : ℝ), (11041191806101/25000000000000 : ℝ), (21384898187811/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149650631/10000000000 : ℝ)|^8371 ≤ (6532718193303/50000000000000 : ℝ)^6323
        have hw : |(-2149650631/10000000000 : ℝ)|=(2149650631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5393983247/10000000000 : ℝ)|^8371 ≤ (11041191806101/25000000000000 : ℝ)^6323
        have hw : |(5393983247/10000000000 : ℝ)|=(5393983247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2632394719/5000000000 : ℝ)|^8371 ≤ (21384898187811/50000000000000 : ℝ)^6323
        have hw : |(2632394719/5000000000 : ℝ)|=(2632394719/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s5_1 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345018801/10000000000 : ℝ)*x 0 + (-2215193581/10000000000 : ℝ)*x 1 + (5264789463/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345018801/10000000000 : ℝ)^8371 ≤ (21817392613923/50000000000000 : ℝ)^6323 := by
    have hnat : (5345018801 : ℕ)^8371*50000000000000^6323 ≤ 21817392613923^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345018801 10000000000 21817392613923 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2215193581/10000000000 : ℝ)^8371 ≤ (6797709054169/50000000000000 : ℝ)^6323 := by
    have hnat : (2215193581 : ℕ)^8371*50000000000000^6323 ≤ 6797709054169^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215193581 10000000000 6797709054169 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5264789463/10000000000 : ℝ)^8371 ≤ (42769796644497/100000000000000 : ℝ)^6323 := by
    have hnat : (5264789463 : ℕ)^8371*100000000000000^6323 ≤ 42769796644497^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264789463 10000000000 42769796644497 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345018801/10000000000 : ℝ), (-2215193581/10000000000 : ℝ), (5264789463/10000000000 : ℝ)] ![(21817392613923/50000000000000 : ℝ), (6797709054169/50000000000000 : ℝ), (42769796644497/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345018801/10000000000 : ℝ)|^8371 ≤ (21817392613923/50000000000000 : ℝ)^6323
        have hw : |(5345018801/10000000000 : ℝ)|=(5345018801/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2215193581/10000000000 : ℝ)|^8371 ≤ (6797709054169/50000000000000 : ℝ)^6323
        have hw : |(-2215193581/10000000000 : ℝ)|=(2215193581/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5264789463/10000000000 : ℝ)|^8371 ≤ (42769796644497/100000000000000 : ℝ)^6323
        have hw : |(5264789463/10000000000 : ℝ)|=(5264789463/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s5_2 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5345018767/10000000000 : ℝ)*x 0 + (5264789491/10000000000 : ℝ)*x 1 + (-2215193589/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5345018767/10000000000 : ℝ)^8371 ≤ (2181739243019/5000000000000 : ℝ)^6323 := by
    have hnat : (5345018767 : ℕ)^8371*5000000000000^6323 ≤ 2181739243019^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5345018767 10000000000 2181739243019 5000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264789491/10000000000 : ℝ)^8371 ≤ (42769796945637/100000000000000 : ℝ)^6323 := by
    have hnat : (5264789491 : ℕ)^8371*100000000000000^6323 ≤ 42769796945637^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264789491 10000000000 42769796945637 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2215193589/10000000000 : ℝ)^8371 ≤ (679770908667/5000000000000 : ℝ)^6323 := by
    have hnat : (2215193589 : ℕ)^8371*5000000000000^6323 ≤ 679770908667^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2215193589 10000000000 679770908667 5000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5345018767/10000000000 : ℝ), (5264789491/10000000000 : ℝ), (-2215193589/10000000000 : ℝ)] ![(2181739243019/5000000000000 : ℝ), (42769796945637/100000000000000 : ℝ), (679770908667/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5345018767/10000000000 : ℝ)|^8371 ≤ (2181739243019/5000000000000 : ℝ)^6323
        have hw : |(5345018767/10000000000 : ℝ)|=(5345018767/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264789491/10000000000 : ℝ)|^8371 ≤ (42769796945637/100000000000000 : ℝ)^6323
        have hw : |(5264789491/10000000000 : ℝ)|=(5264789491/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2215193589/10000000000 : ℝ)|^8371 ≤ (679770908667/5000000000000 : ℝ)^6323
        have hw : |(-2215193589/10000000000 : ℝ)|=(2215193589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s5_3 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4359546183/10000000000 : ℝ)*x 0 + (423201969/1000000000 : ℝ)*x 1 + (4490863577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4359546183/10000000000 : ℝ)^8371 ≤ (8329087916607/25000000000000 : ℝ)^6323 := by
    have hnat : (4359546183 : ℕ)^8371*25000000000000^6323 ≤ 8329087916607^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4359546183 10000000000 8329087916607 25000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (423201969/1000000000 : ℝ)^8371 ≤ (6406452821743/20000000000000 : ℝ)^6323 := by
    have hnat : (423201969 : ℕ)^8371*20000000000000^6323 ≤ 6406452821743^6323*1000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      423201969 1000000000 6406452821743 20000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4490863577/10000000000 : ℝ)^8371 ≤ (34651384207643/100000000000000 : ℝ)^6323 := by
    have hnat : (4490863577 : ℕ)^8371*100000000000000^6323 ≤ 34651384207643^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490863577 10000000000 34651384207643 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4359546183/10000000000 : ℝ), (423201969/1000000000 : ℝ), (4490863577/10000000000 : ℝ)] ![(8329087916607/25000000000000 : ℝ), (6406452821743/20000000000000 : ℝ), (34651384207643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4359546183/10000000000 : ℝ)|^8371 ≤ (8329087916607/25000000000000 : ℝ)^6323
        have hw : |(4359546183/10000000000 : ℝ)|=(4359546183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(423201969/1000000000 : ℝ)|^8371 ≤ (6406452821743/20000000000000 : ℝ)^6323
        have hw : |(423201969/1000000000 : ℝ)|=(423201969/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4490863577/10000000000 : ℝ)|^8371 ≤ (34651384207643/100000000000000 : ℝ)^6323
        have hw : |(4490863577/10000000000 : ℝ)|=(4490863577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s5_4 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2149655723/10000000000 : ℝ)*x 0 + (164535079/312500000 : ℝ)*x 1 + (337103061/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2149655723/10000000000 : ℝ)^8371 ≤ (130654773597/1000000000000 : ℝ)^6323 := by
    have hnat : (2149655723 : ℕ)^8371*1000000000000^6323 ≤ 130654773597^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2149655723 10000000000 130654773597 1000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (164535079/312500000 : ℝ)^8371 ≤ (42773378794629/100000000000000 : ℝ)^6323 := by
    have hnat : (164535079 : ℕ)^8371*100000000000000^6323 ≤ 42773378794629^6323*312500000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164535079 312500000 42773378794629 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (337103061/625000000 : ℝ)^8371 ≤ (44161143836297/100000000000000 : ℝ)^6323 := by
    have hnat : (337103061 : ℕ)^8371*100000000000000^6323 ≤ 44161143836297^6323*625000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      337103061 625000000 44161143836297 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2149655723/10000000000 : ℝ), (164535079/312500000 : ℝ), (337103061/625000000 : ℝ)] ![(130654773597/1000000000000 : ℝ), (42773378794629/100000000000000 : ℝ), (44161143836297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2149655723/10000000000 : ℝ)|^8371 ≤ (130654773597/1000000000000 : ℝ)^6323
        have hw : |(-2149655723/10000000000 : ℝ)|=(2149655723/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(164535079/312500000 : ℝ)|^8371 ≤ (42773378794629/100000000000000 : ℝ)^6323
        have hw : |(164535079/312500000 : ℝ)|=(164535079/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(337103061/625000000 : ℝ)|^8371 ≤ (44161143836297/100000000000000 : ℝ)^6323
        have hw : |(337103061/625000000 : ℝ)|=(337103061/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s5_5 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2656100757/5000000000 : ℝ)*x 0 + (-2086333893/10000000000 : ℝ)*x 1 + (2696824473/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2656100757/5000000000 : ℝ)^8371 ≤ (43280455333627/100000000000000 : ℝ)^6323 := by
    have hnat : (2656100757 : ℕ)^8371*100000000000000^6323 ≤ 43280455333627^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2656100757 5000000000 43280455333627 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2086333893/10000000000 : ℝ)^8371 ≤ (6279200567767/50000000000000 : ℝ)^6323 := by
    have hnat : (2086333893 : ℕ)^8371*50000000000000^6323 ≤ 6279200567767^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2086333893 10000000000 6279200567767 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2696824473/5000000000 : ℝ)^8371 ≤ (4416114351111/10000000000000 : ℝ)^6323 := by
    have hnat : (2696824473 : ℕ)^8371*10000000000000^6323 ≤ 4416114351111^6323*5000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696824473 5000000000 4416114351111 10000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2656100757/5000000000 : ℝ), (-2086333893/10000000000 : ℝ), (2696824473/5000000000 : ℝ)] ![(43280455333627/100000000000000 : ℝ), (6279200567767/50000000000000 : ℝ), (4416114351111/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2656100757/5000000000 : ℝ)|^8371 ≤ (43280455333627/100000000000000 : ℝ)^6323
        have hw : |(2656100757/5000000000 : ℝ)|=(2656100757/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2086333893/10000000000 : ℝ)|^8371 ≤ (6279200567767/50000000000000 : ℝ)^6323
        have hw : |(-2086333893/10000000000 : ℝ)|=(2086333893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2696824473/5000000000 : ℝ)|^8371 ≤ (4416114351111/10000000000000 : ℝ)^6323
        have hw : |(2696824473/5000000000 : ℝ)|=(2696824473/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s5_6 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (332012581/625000000 : ℝ)*x 0 + (43149193/80000000 : ℝ)*x 1 + (-417266789/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (332012581/625000000 : ℝ)^8371 ≤ (43280452982219/100000000000000 : ℝ)^6323 := by
    have hnat : (332012581 : ℕ)^8371*100000000000000^6323 ≤ 43280452982219^6323*625000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      332012581 625000000 43280452982219 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (43149193/80000000 : ℝ)^8371 ≤ (345008948839/781250000000 : ℝ)^6323 := by
    have hnat : (43149193 : ℕ)^8371*781250000000^6323 ≤ 345008948839^6323*80000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      43149193 80000000 345008948839 781250000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (417266789/2000000000 : ℝ)^8371 ≤ (12558401549923/100000000000000 : ℝ)^6323 := by
    have hnat : (417266789 : ℕ)^8371*100000000000000^6323 ≤ 12558401549923^6323*2000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      417266789 2000000000 12558401549923 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(332012581/625000000 : ℝ), (43149193/80000000 : ℝ), (-417266789/2000000000 : ℝ)] ![(43280452982219/100000000000000 : ℝ), (345008948839/781250000000 : ℝ), (12558401549923/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(332012581/625000000 : ℝ)|^8371 ≤ (43280452982219/100000000000000 : ℝ)^6323
        have hw : |(332012581/625000000 : ℝ)|=(332012581/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(43149193/80000000 : ℝ)|^8371 ≤ (345008948839/781250000000 : ℝ)^6323
        have hw : |(43149193/80000000 : ℝ)|=(43149193/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-417266789/2000000000 : ℝ)|^8371 ≤ (12558401549923/100000000000000 : ℝ)^6323
        have hw : |(-417266789/2000000000 : ℝ)|=(417266789/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1178_s5_7 (p : ℝ) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (1089889121/2500000000 : ℝ)*x 0 + (4490196351/10000000000 : ℝ)*x 1 + (1058172359/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1089889121/2500000000 : ℝ)^8371 ≤ (33316455886139/100000000000000 : ℝ)^6323 := by
    have hnat : (1089889121 : ℕ)^8371*100000000000000^6323 ≤ 33316455886139^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1089889121 2500000000 33316455886139 100000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4490196351/10000000000 : ℝ)^8371 ≤ (17322284277907/50000000000000 : ℝ)^6323 := by
    have hnat : (4490196351 : ℕ)^8371*50000000000000^6323 ≤ 17322284277907^6323*10000000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4490196351 10000000000 17322284277907 50000000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1058172359/2500000000 : ℝ)^8371 ≤ (200243597147/625000000000 : ℝ)^6323 := by
    have hnat : (1058172359 : ℕ)^8371*625000000000^6323 ≤ 200243597147^6323*2500000000^8371 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058172359 2500000000 200243597147 625000000000 8371 6323 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8371/2048 : ℝ)) 8371 6323 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1089889121/2500000000 : ℝ), (4490196351/10000000000 : ℝ), (1058172359/2500000000 : ℝ)] ![(33316455886139/100000000000000 : ℝ), (17322284277907/50000000000000 : ℝ), (200243597147/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1089889121/2500000000 : ℝ)|^8371 ≤ (33316455886139/100000000000000 : ℝ)^6323
        have hw : |(1089889121/2500000000 : ℝ)|=(1089889121/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4490196351/10000000000 : ℝ)|^8371 ≤ (17322284277907/50000000000000 : ℝ)^6323
        have hw : |(4490196351/10000000000 : ℝ)|=(4490196351/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1058172359/2500000000 : ℝ)|^8371 ≤ (200243597147/625000000000 : ℝ)^6323
        have hw : |(1058172359/2500000000 : ℝ)|=(1058172359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1178_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11367/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (1763/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5621/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5621/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5621/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7117/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5621/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5621/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7117/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5621/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5621/50000 : ℝ) ^ (4185/1024 : ℝ) ≤ (6604642089373033/50000000000000000000 : ℝ) := by
    have hpowers : (5621/50000 : ℝ)^4185 ≤ (6604642089373033/50000000000000000000 : ℝ)^1024 := by
      have hnat : (5621 : ℕ)^4185*50000000000000000000^1024 ≤ 6604642089373033^1024*50000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5621 50000 6604642089373033 50000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5621/50000 : ℝ)) (X := (6604642089373033/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7117/50000 : ℝ) ^ (4185/1024 : ℝ) ≤ (1732567074712317/5000000000000000000 : ℝ) := by
    have hpowers : (7117/50000 : ℝ)^4185 ≤ (1732567074712317/5000000000000000000 : ℝ)^1024 := by
      have hnat : (7117 : ℕ)^4185*5000000000000000000^1024 ≤ 1732567074712317^1024*50000^4185 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7117 50000 1732567074712317 5000000000000000000 4185 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7117/50000 : ℝ)) (X := (1732567074712317/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25006604642089373033/25000000000000000000 : ℝ) ≤ (10000646354010133/10000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (25006604642089373033/25000000000000000000 : ℝ)^1024 ≤ (10000646354010133/10000000000000000 : ℝ)^4185 := by
      have hnat : (25006604642089373033 : ℕ)^1024*10000000000000000^4185 ≤ 10000646354010133^4185*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25006604642089373033 25000000000000000000 10000646354010133 10000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000646354010133/10000000000000000 : ℝ)) (X := (25006604642089373033/25000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50023930312836496203/50000000000000000000 : ℝ) ≤ (25002927146043/25000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (50023930312836496203/50000000000000000000 : ℝ)^1024 ≤ (25002927146043/25000000000000 : ℝ)^4185 := by
      have hnat : (50023930312836496203 : ℕ)^1024*25000000000000^4185 ≤ 25002927146043^4185*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50023930312836496203 50000000000000000000 25002927146043 25000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (25002927146043/25000000000000 : ℝ)) (X := (50023930312836496203/50000000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (2501732567074712317/2500000000000000000 : ℝ) ≤ (10001695362824267/10000000000000000 : ℝ) ^ (4185/1024 : ℝ) := by
    have hpowers : (2501732567074712317/2500000000000000000 : ℝ)^1024 ≤ (10001695362824267/10000000000000000 : ℝ)^4185 := by
      have hnat : (2501732567074712317 : ℕ)^1024*10000000000000000^4185 ≤ 10001695362824267^4185*2500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2501732567074712317 2500000000000000000 10001695362824267 10000000000000000 1024 4185 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001695362824267/10000000000000000 : ℝ)) (X := (2501732567074712317/2500000000000000000 : ℝ)) (by norm_num) 4185 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(6604642089373033/50000000000000000000 : ℝ) ≤ ((679775930320677807/680000000000000000 : ℝ)+2*(524504407067/299200000000000 : ℝ)*(5621/50000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (679775930320677807/680000000000000000 : ℝ)+2*(524504407067/299200000000000 : ℝ)*(5621/50000 : ℝ)=(10000646354010133/10000000000000000 : ℝ) by norm_num, show 1+2*(6604642089373033/50000000000000000000 : ℝ)=(25006604642089373033/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1732567074712317/5000000000000000000 : ℝ)+(6604642089373033/50000000000000000000 : ℝ) ≤ ((679775930320677807/680000000000000000 : ℝ)+(524504407067/299200000000000 : ℝ)*((7117/50000 : ℝ)+(5621/50000 : ℝ)))^(4185/1024 : ℝ) := by
    rw [show (679775930320677807/680000000000000000 : ℝ)+(524504407067/299200000000000 : ℝ)*((7117/50000 : ℝ)+(5621/50000 : ℝ))=(25002927146043/25000000000000 : ℝ) by norm_num, show 1+(1732567074712317/5000000000000000000 : ℝ)+(6604642089373033/50000000000000000000 : ℝ)=(50023930312836496203/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1732567074712317/5000000000000000000 : ℝ) ≤ ((679775930320677807/680000000000000000 : ℝ)+2*(524504407067/299200000000000 : ℝ)*(7117/50000 : ℝ))^(4185/1024 : ℝ) := by
    rw [show (679775930320677807/680000000000000000 : ℝ)+2*(524504407067/299200000000000 : ℝ)*(7117/50000 : ℝ)=(10001695362824267/10000000000000000 : ℝ) by norm_num, show 1+2*(1732567074712317/5000000000000000000 : ℝ)=(2501732567074712317/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (679775930320677807/680000000000000000 : ℝ)*(X 1 0+X 2 0)+(524504407067/299200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (5621/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (679775930320677807/680000000000000000 : ℝ)) (alpha := (524504407067/299200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (679775930320677807/680000000000000000 : ℝ)*(X 0 1+X 2 1)+(524504407067/299200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (5621/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (679775930320677807/680000000000000000 : ℝ)) (alpha := (524504407067/299200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (679775930320677807/680000000000000000 : ℝ)*(X 0 2+X 1 2)+(524504407067/299200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4185/1024 : ℝ)) (lo := (5621/50000 : ℝ)) (hi := (7117/50000 : ℝ)) (c := (679775930320677807/680000000000000000 : ℝ)) (alpha := (524504407067/299200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2149650631/10000000000 : ℝ)*X 0 0+(5393983247/10000000000 : ℝ)*X 0 1+(2632394719/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5345018801/10000000000 : ℝ)*X 1 0+(-2215193581/10000000000 : ℝ)*X 1 1+(5264789463/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5345018767/10000000000 : ℝ)*X 2 0+(5264789491/10000000000 : ℝ)*X 2 1+(-2215193589/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4359546183/10000000000 : ℝ)*X 0 0+(423201969/1000000000 : ℝ)*X 0 1+(4490863577/10000000000 : ℝ)*X 0 2+(4359546183/10000000000 : ℝ)*X 1 0+(423201969/1000000000 : ℝ)*X 1 1+(4490863577/10000000000 : ℝ)*X 1 2+(4359546183/10000000000 : ℝ)*X 2 0+(423201969/1000000000 : ℝ)*X 2 1+(4490863577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2149655723/10000000000 : ℝ)*X 0 0+(164535079/312500000 : ℝ)*X 0 1+(337103061/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2656100757/5000000000 : ℝ)*X 1 0+(-2086333893/10000000000 : ℝ)*X 1 1+(2696824473/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((332012581/625000000 : ℝ)*X 2 0+(43149193/80000000 : ℝ)*X 2 1+(-417266789/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1089889121/2500000000 : ℝ)*X 0 0+(4490196351/10000000000 : ℝ)*X 0 1+(1058172359/2500000000 : ℝ)*X 0 2+(1089889121/2500000000 : ℝ)*X 1 0+(4490196351/10000000000 : ℝ)*X 1 1+(1058172359/2500000000 : ℝ)*X 1 2+(1089889121/2500000000 : ℝ)*X 2 0+(4490196351/10000000000 : ℝ)*X 2 1+(1058172359/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1178_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (2306424220692089055002524377/374000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (649787411/50000000000000 : ℝ)*(base19) + (121894131/10000000000000 : ℝ)*(base23) + (671259/4000000000000 : ℝ)*(lower2) + (92976089/50000000000000 : ℝ)*(upper3) + (35214283/25000000000000 : ℝ)*(upper5) + (725234297174677/12500000000000 : ℝ)*(major0) + (725234297174677/12500000000000 : ℝ)*(major1) + (5801874377397417/100000000000000 : ℝ)*(major2) + (3870172919865429/50000000000000 : ℝ)*(sp0) + (774037936682231/10000000000000 : ℝ)*(sp1) + (7740379447455823/100000000000000 : ℝ)*(sp2) + (1931674868019363/50000000000000 : ℝ)*(sp3) + (17413333137/50000000000000 : ℝ)*(sp4) + (3629359061/20000000000000 : ℝ)*(sp7) + (241460492677127/6250000000000 : ℝ)*(f.failure) + (1935095166599283/25000000000000 : ℝ)*(f.sum) + (182879665583051/29920000000000000000000000000 : ℝ)*base65 + (12940348128008933/1062500000000000000000000000000 : ℝ)*base67 + (13003856798753069709/748000000000000000000000000000000 : ℝ)*base69 + (14589521108321433/1062500000000000000000000000000 : ℝ)*base71 + (53126957874389/29920000000000000000000000000 : ℝ)*base74 + (12056584884857069709/748000000000000000000000000000000 : ℝ)*base75 + (2052474957711701729/93500000000000000000000000000000 : ℝ)*base77 + (190681893789798271/93500000000000000000000000000000 : ℝ)*base80 + (4682908049909/1870000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base87 + (2479923/156250000000000000000 : ℝ)*base89 + (2479923/156250000000000000000 : ℝ)*base91 + (917423/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (150672512123302986205449/14960000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2181551/97656250000 : ℝ)*(base19) + (2070480677/100000000000000 : ℝ)*(base23) + (215661131/100000000000000 : ℝ)*(upper3) + (83069927/100000000000000 : ℝ)*(lower4) + (194947561/100000000000000 : ℝ)*(upper5) + (5831941124734803/100000000000000 : ℝ)*(major0) + (5831941124734803/100000000000000 : ℝ)*(major1) + (5831941124734803/100000000000000 : ℝ)*(major2) + (12261634501/20000000000000 : ℝ)*(sp1) + (30612590539/50000000000000 : ℝ)*(sp2) + (3890246551729471/50000000000000 : ℝ)*(sp4) + (7780429561378213/100000000000000 : ℝ)*(sp5) + (3890214903898593/50000000000000 : ℝ)*(sp6) + (485423601285949/12500000000000 : ℝ)*(sp7) + (485423601285949/12500000000000 : ℝ)*(f.failure) + (3890246551729471/50000000000000 : ℝ)*(f.sum) + (26628987018719/14960000000000000000000000000 : ℝ)*base66 + (3686383169435187769/748000000000000000000000000000000 : ℝ)*base68 + (6470289072763187769/748000000000000000000000000000000 : ℝ)*base70 + (1867999168991187769/748000000000000000000000000000000 : ℝ)*base72 + (19539319090079/14960000000000000000000000000 : ℝ)*base74 + (3710899806328812231/748000000000000000000000000000000 : ℝ)*base75 + (2577990985548812231/748000000000000000000000000000000 : ℝ)*base77 + (8112891837908812231/748000000000000000000000000000000 : ℝ)*base79 + (67930090331199/14960000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (1487401/312500000000000000000 : ℝ)*base89 + (1487401/312500000000000000000 : ℝ)*base91 + (1487401/312500000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1178_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7117/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5621/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1178_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1178_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8199/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (923/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1178_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1178_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1178_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4185/1024 : ℝ) ≤ p) (hpb : p ≤ (8371/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37544149/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (8199/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (923/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11367/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (1763/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1178_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
