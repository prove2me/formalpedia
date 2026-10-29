-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1323_b3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T20:44:16.471308+00:00
-- url     : https://prove2.me/submissions/88f742ea-c3a9-424f-b53f-0b7ffc1156fb

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
theorem support_rectangle_w1323_box_0 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1891718601/10000000000 : ℝ)*x 0 + (2695366431/5000000000 : ℝ)*x 1 + (5390732903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1891718601/10000000000 : ℝ)^4283 ≤ (5605442934197/50000000000000 : ℝ)^3259 := by
    have hnat : (1891718601 : ℕ)^4283*50000000000000^3259 ≤ 5605442934197^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1891718601 10000000000 5605442934197 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695366431/5000000000 : ℝ)^4283 ≤ (44394556838231/100000000000000 : ℝ)^3259 := by
    have hnat : (2695366431 : ℕ)^4283*100000000000000^3259 ≤ 44394556838231^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695366431 5000000000 44394556838231 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5390732903/10000000000 : ℝ)^4283 ≤ (11098639320493/25000000000000 : ℝ)^3259 := by
    have hnat : (5390732903 : ℕ)^4283*25000000000000^3259 ≤ 11098639320493^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5390732903 10000000000 11098639320493 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1891718601/10000000000 : ℝ), (2695366431/5000000000 : ℝ), (5390732903/10000000000 : ℝ)] ![(5605442934197/50000000000000 : ℝ), (44394556838231/100000000000000 : ℝ), (11098639320493/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1891718601/10000000000 : ℝ)|^4283 ≤ (5605442934197/50000000000000 : ℝ)^3259
        have hw : |(-1891718601/10000000000 : ℝ)|=(1891718601/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695366431/5000000000 : ℝ)|^4283 ≤ (44394556838231/100000000000000 : ℝ)^3259
        have hw : |(2695366431/5000000000 : ℝ)|=(2695366431/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5390732903/10000000000 : ℝ)|^4283 ≤ (11098639320493/25000000000000 : ℝ)^3259
        have hw : |(5390732903/10000000000 : ℝ)|=(5390732903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_1 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (528488823/1000000000 : ℝ)*x 0 + (-2036632593/10000000000 : ℝ)*x 1 + (84230207/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (528488823/1000000000 : ℝ)^4283 ≤ (8650511072951/20000000000000 : ℝ)^3259 := by
    have hnat : (528488823 : ℕ)^4283*20000000000000^3259 ≤ 8650511072951^3259*1000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      528488823 1000000000 8650511072951 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2036632593/10000000000 : ℝ)^4283 ≤ (6176441800173/50000000000000 : ℝ)^3259 := by
    have hnat : (2036632593 : ℕ)^4283*50000000000000^3259 ≤ 6176441800173^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036632593 10000000000 6176441800173 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (84230207/156250000 : ℝ)^4283 ≤ (44394561015889/100000000000000 : ℝ)^3259 := by
    have hnat : (84230207 : ℕ)^4283*100000000000000^3259 ≤ 44394561015889^3259*156250000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      84230207 156250000 44394561015889 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(528488823/1000000000 : ℝ), (-2036632593/10000000000 : ℝ), (84230207/156250000 : ℝ)] ![(8650511072951/20000000000000 : ℝ), (6176441800173/50000000000000 : ℝ), (44394561015889/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(528488823/1000000000 : ℝ)|^4283 ≤ (8650511072951/20000000000000 : ℝ)^3259
        have hw : |(528488823/1000000000 : ℝ)|=(528488823/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2036632593/10000000000 : ℝ)|^4283 ≤ (6176441800173/50000000000000 : ℝ)^3259
        have hw : |(-2036632593/10000000000 : ℝ)|=(2036632593/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(84230207/156250000 : ℝ)|^4283 ≤ (44394561015889/100000000000000 : ℝ)^3259
        have hw : |(84230207/156250000 : ℝ)|=(84230207/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_2 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (660611059/1250000000 : ℝ)*x 0 + (2695366497/5000000000 : ℝ)*x 1 + (-2036632611/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (660611059/1250000000 : ℝ)^4283 ≤ (1081313949191/2500000000000 : ℝ)^3259 := by
    have hnat : (660611059 : ℕ)^4283*2500000000000^3259 ≤ 1081313949191^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660611059 1250000000 1081313949191 2500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2695366497/5000000000 : ℝ)^4283 ≤ (2219727913343/5000000000000 : ℝ)^3259 := by
    have hnat : (2695366497 : ℕ)^4283*5000000000000^3259 ≤ 2219727913343^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2695366497 5000000000 2219727913343 5000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2036632611/10000000000 : ℝ)^4283 ≤ (6176441871913/50000000000000 : ℝ)^3259 := by
    have hnat : (2036632611 : ℕ)^4283*50000000000000^3259 ≤ 6176441871913^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2036632611 10000000000 6176441871913 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(660611059/1250000000 : ℝ), (2695366497/5000000000 : ℝ), (-2036632611/10000000000 : ℝ)] ![(1081313949191/2500000000000 : ℝ), (2219727913343/5000000000000 : ℝ), (6176441871913/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(660611059/1250000000 : ℝ)|^4283 ≤ (1081313949191/2500000000000 : ℝ)^3259
        have hw : |(660611059/1250000000 : ℝ)|=(660611059/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2695366497/5000000000 : ℝ)|^4283 ≤ (2219727913343/5000000000000 : ℝ)^3259
        have hw : |(2695366497/5000000000 : ℝ)|=(2695366497/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2036632611/10000000000 : ℝ)|^4283 ≤ (6176441871913/50000000000000 : ℝ)^3259
        have hw : |(-2036632611/10000000000 : ℝ)|=(2036632611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_3 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4480260831/10000000000 : ℝ)*x 0 + (4261224107/10000000000 : ℝ)*x 1 + (213061203/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4480260831/10000000000 : ℝ)^4283 ≤ (174064586931/500000000000 : ℝ)^3259 := by
    have hnat : (4480260831 : ℕ)^4283*500000000000^3259 ≤ 174064586931^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4480260831 10000000000 174064586931 500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4261224107/10000000000 : ℝ)^4283 ≤ (2037096346007/6250000000000 : ℝ)^3259 := by
    have hnat : (4261224107 : ℕ)^4283*6250000000000^3259 ≤ 2037096346007^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4261224107 10000000000 2037096346007 6250000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (213061203/500000000 : ℝ)^4283 ≤ (32593541063659/100000000000000 : ℝ)^3259 := by
    have hnat : (213061203 : ℕ)^4283*100000000000000^3259 ≤ 32593541063659^3259*500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213061203 500000000 32593541063659 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4480260831/10000000000 : ℝ), (4261224107/10000000000 : ℝ), (213061203/500000000 : ℝ)] ![(174064586931/500000000000 : ℝ), (2037096346007/6250000000000 : ℝ), (32593541063659/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4480260831/10000000000 : ℝ)|^4283 ≤ (174064586931/500000000000 : ℝ)^3259
        have hw : |(4480260831/10000000000 : ℝ)|=(4480260831/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4261224107/10000000000 : ℝ)|^4283 ≤ (2037096346007/6250000000000 : ℝ)^3259
        have hw : |(4261224107/10000000000 : ℝ)|=(4261224107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(213061203/500000000 : ℝ)|^4283 ≤ (32593541063659/100000000000000 : ℝ)^3259
        have hw : |(213061203/500000000 : ℝ)|=(213061203/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_4 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2232038743/10000000000 : ℝ)*x 0 + (658060911/1250000000 : ℝ)*x 1 + (164515239/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2232038743/10000000000 : ℝ)^4283 ≤ (13933472835459/100000000000000 : ℝ)^3259 := by
    have hnat : (2232038743 : ℕ)^4283*100000000000000^3259 ≤ 13933472835459^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2232038743 10000000000 13933472835459 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (658060911/1250000000 : ℝ)^4283 ≤ (43033261639513/100000000000000 : ℝ)^3259 := by
    have hnat : (658060911 : ℕ)^4283*100000000000000^3259 ≤ 43033261639513^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658060911 1250000000 43033261639513 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (164515239/312500000 : ℝ)^4283 ≤ (43033265506871/100000000000000 : ℝ)^3259 := by
    have hnat : (164515239 : ℕ)^4283*100000000000000^3259 ≤ 43033265506871^3259*312500000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      164515239 312500000 43033265506871 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2232038743/10000000000 : ℝ), (658060911/1250000000 : ℝ), (164515239/312500000 : ℝ)] ![(13933472835459/100000000000000 : ℝ), (43033261639513/100000000000000 : ℝ), (43033265506871/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2232038743/10000000000 : ℝ)|^4283 ≤ (13933472835459/100000000000000 : ℝ)^3259
        have hw : |(-2232038743/10000000000 : ℝ)|=(2232038743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(658060911/1250000000 : ℝ)|^4283 ≤ (43033261639513/100000000000000 : ℝ)^3259
        have hw : |(658060911/1250000000 : ℝ)|=(658060911/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(164515239/312500000 : ℝ)|^4283 ≤ (43033265506871/100000000000000 : ℝ)^3259
        have hw : |(164515239/312500000 : ℝ)|=(164515239/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_5 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (671703989/1250000000 : ℝ)*x 0 + (-2087155147/10000000000 : ℝ)*x 1 + (526448787/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (671703989/1250000000 : ℝ)^4283 ≤ (22104783214801/50000000000000 : ℝ)^3259 := by
    have hnat : (671703989 : ℕ)^4283*50000000000000^3259 ≤ 22104783214801^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      671703989 1250000000 22104783214801 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2087155147/10000000000 : ℝ)^4283 ≤ (12757165662389/100000000000000 : ℝ)^3259 := by
    have hnat : (2087155147 : ℕ)^4283*100000000000000^3259 ≤ 12757165662389^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2087155147 10000000000 12757165662389 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (526448787/1000000000 : ℝ)^4283 ≤ (21516633945871/50000000000000 : ℝ)^3259 := by
    have hnat : (526448787 : ℕ)^4283*50000000000000^3259 ≤ 21516633945871^3259*1000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      526448787 1000000000 21516633945871 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(671703989/1250000000 : ℝ), (-2087155147/10000000000 : ℝ), (526448787/1000000000 : ℝ)] ![(22104783214801/50000000000000 : ℝ), (12757165662389/100000000000000 : ℝ), (21516633945871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(671703989/1250000000 : ℝ)|^4283 ≤ (22104783214801/50000000000000 : ℝ)^3259
        have hw : |(671703989/1250000000 : ℝ)|=(671703989/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2087155147/10000000000 : ℝ)|^4283 ≤ (12757165662389/100000000000000 : ℝ)^3259
        have hw : |(-2087155147/10000000000 : ℝ)|=(2087155147/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(526448787/1000000000 : ℝ)|^4283 ≤ (21516633945871/50000000000000 : ℝ)^3259
        have hw : |(526448787/1000000000 : ℝ)|=(526448787/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_6 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5373632467/10000000000 : ℝ)*x 0 + (5264487707/10000000000 : ℝ)*x 1 + (-1043577309/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373632467/10000000000 : ℝ)^4283 ≤ (8841914486069/20000000000000 : ℝ)^3259 := by
    have hnat : (5373632467 : ℕ)^4283*20000000000000^3259 ≤ 8841914486069^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373632467 10000000000 8841914486069 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5264487707/10000000000 : ℝ)^4283 ≤ (2689579133793/6250000000000 : ℝ)^3259 := by
    have hnat : (5264487707 : ℕ)^4283*6250000000000^3259 ≤ 2689579133793^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5264487707 10000000000 2689579133793 6250000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1043577309/5000000000 : ℝ)^4283 ≤ (510286456523/4000000000000 : ℝ)^3259 := by
    have hnat : (1043577309 : ℕ)^4283*4000000000000^3259 ≤ 510286456523^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1043577309 5000000000 510286456523 4000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373632467/10000000000 : ℝ), (5264487707/10000000000 : ℝ), (-1043577309/5000000000 : ℝ)] ![(8841914486069/20000000000000 : ℝ), (2689579133793/6250000000000 : ℝ), (510286456523/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373632467/10000000000 : ℝ)|^4283 ≤ (8841914486069/20000000000000 : ℝ)^3259
        have hw : |(5373632467/10000000000 : ℝ)|=(5373632467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5264487707/10000000000 : ℝ)|^4283 ≤ (2689579133793/6250000000000 : ℝ)^3259
        have hw : |(5264487707/10000000000 : ℝ)|=(5264487707/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1043577309/5000000000 : ℝ)|^4283 ≤ (510286456523/4000000000000 : ℝ)^3259
        have hw : |(-1043577309/5000000000 : ℝ)|=(1043577309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_7 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (261379467/625000000 : ℝ)*x 0 + (2205132351/5000000000 : ℝ)*x 1 + (4410264331/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (261379467/625000000 : ℝ)^4283 ≤ (31800215673259/100000000000000 : ℝ)^3259 := by
    have hnat : (261379467 : ℕ)^4283*100000000000000^3259 ≤ 31800215673259^3259*625000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      261379467 625000000 31800215673259 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2205132351/5000000000 : ℝ)^4283 ≤ (34099894045759/100000000000000 : ℝ)^3259 := by
    have hnat : (2205132351 : ℕ)^4283*100000000000000^3259 ≤ 34099894045759^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2205132351 5000000000 34099894045759 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4410264331/10000000000 : ℝ)^4283 ≤ (34099890275893/100000000000000 : ℝ)^3259 := by
    have hnat : (4410264331 : ℕ)^4283*100000000000000^3259 ≤ 34099890275893^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4410264331 10000000000 34099890275893 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(261379467/625000000 : ℝ), (2205132351/5000000000 : ℝ), (4410264331/10000000000 : ℝ)] ![(31800215673259/100000000000000 : ℝ), (34099894045759/100000000000000 : ℝ), (34099890275893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(261379467/625000000 : ℝ)|^4283 ≤ (31800215673259/100000000000000 : ℝ)^3259
        have hw : |(261379467/625000000 : ℝ)|=(261379467/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2205132351/5000000000 : ℝ)|^4283 ≤ (34099894045759/100000000000000 : ℝ)^3259
        have hw : |(2205132351/5000000000 : ℝ)|=(2205132351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4410264331/10000000000 : ℝ)|^4283 ≤ (34099890275893/100000000000000 : ℝ)^3259
        have hw : |(4410264331/10000000000 : ℝ)|=(4410264331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_8 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2160624117/10000000000 : ℝ)*x 0 + (5177667173/10000000000 : ℝ)*x 1 + (5404759827/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160624117/10000000000 : ℝ)^4283 ≤ (1335055982899/10000000000000 : ℝ)^3259 := by
    have hnat : (2160624117 : ℕ)^4283*10000000000000^3259 ≤ 1335055982899^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160624117 10000000000 1335055982899 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5177667173/10000000000 : ℝ)^4283 ≤ (67364813071/160000000000 : ℝ)^3259 := by
    have hnat : (5177667173 : ℕ)^4283*160000000000^3259 ≤ 67364813071^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5177667173 10000000000 67364813071 160000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5404759827/10000000000 : ℝ)^4283 ≤ (44546431993691/100000000000000 : ℝ)^3259 := by
    have hnat : (5404759827 : ℕ)^4283*100000000000000^3259 ≤ 44546431993691^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5404759827 10000000000 44546431993691 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2160624117/10000000000 : ℝ), (5177667173/10000000000 : ℝ), (5404759827/10000000000 : ℝ)] ![(1335055982899/10000000000000 : ℝ), (67364813071/160000000000 : ℝ), (44546431993691/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2160624117/10000000000 : ℝ)|^4283 ≤ (1335055982899/10000000000000 : ℝ)^3259
        have hw : |(-2160624117/10000000000 : ℝ)|=(2160624117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5177667173/10000000000 : ℝ)|^4283 ≤ (67364813071/160000000000 : ℝ)^3259
        have hw : |(5177667173/10000000000 : ℝ)|=(5177667173/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5404759827/10000000000 : ℝ)|^4283 ≤ (44546431993691/100000000000000 : ℝ)^3259
        have hw : |(5404759827/10000000000 : ℝ)|=(5404759827/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_9 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1318755567/2500000000 : ℝ)*x 0 + (-1015442273/5000000000 : ℝ)*x 1 + (540476089/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1318755567/2500000000 : ℝ)^4283 ≤ (84270451033/195312500000 : ℝ)^3259 := by
    have hnat : (1318755567 : ℕ)^4283*195312500000^3259 ≤ 84270451033^3259*2500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1318755567 2500000000 84270451033 195312500000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1015442273/5000000000 : ℝ)^4283 ≤ (6153542777027/50000000000000 : ℝ)^3259 := by
    have hnat : (1015442273 : ℕ)^4283*50000000000000^3259 ≤ 6153542777027^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1015442273 5000000000 6153542777027 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (540476089/1000000000 : ℝ)^4283 ≤ (8909288701577/20000000000000 : ℝ)^3259 := by
    have hnat : (540476089 : ℕ)^4283*20000000000000^3259 ≤ 8909288701577^3259*1000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      540476089 1000000000 8909288701577 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1318755567/2500000000 : ℝ), (-1015442273/5000000000 : ℝ), (540476089/1000000000 : ℝ)] ![(84270451033/195312500000 : ℝ), (6153542777027/50000000000000 : ℝ), (8909288701577/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1318755567/2500000000 : ℝ)|^4283 ≤ (84270451033/195312500000 : ℝ)^3259
        have hw : |(1318755567/2500000000 : ℝ)|=(1318755567/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1015442273/5000000000 : ℝ)|^4283 ≤ (6153542777027/50000000000000 : ℝ)^3259
        have hw : |(-1015442273/5000000000 : ℝ)|=(1015442273/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(540476089/1000000000 : ℝ)|^4283 ≤ (8909288701577/20000000000000 : ℝ)^3259
        have hw : |(540476089/1000000000 : ℝ)|=(540476089/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_10 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2637511333/5000000000 : ℝ)*x 0 + (2702380163/5000000000 : ℝ)*x 1 + (-253860597/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2637511333/5000000000 : ℝ)^4283 ≤ (21573237603581/50000000000000 : ℝ)^3259 := by
    have hnat : (2637511333 : ℕ)^4283*50000000000000^3259 ≤ 21573237603581^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2637511333 5000000000 21573237603581 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2702380163/5000000000 : ℝ)^4283 ≤ (8909287479751/20000000000000 : ℝ)^3259 := by
    have hnat : (2702380163 : ℕ)^4283*20000000000000^3259 ≤ 8909287479751^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2702380163 5000000000 8909287479751 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (253860597/1250000000 : ℝ)^4283 ≤ (1538385923223/12500000000000 : ℝ)^3259 := by
    have hnat : (253860597 : ℕ)^4283*12500000000000^3259 ≤ 1538385923223^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      253860597 1250000000 1538385923223 12500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2637511333/5000000000 : ℝ), (2702380163/5000000000 : ℝ), (-253860597/1250000000 : ℝ)] ![(21573237603581/50000000000000 : ℝ), (8909287479751/20000000000000 : ℝ), (1538385923223/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2637511333/5000000000 : ℝ)|^4283 ≤ (21573237603581/50000000000000 : ℝ)^3259
        have hw : |(2637511333/5000000000 : ℝ)|=(2637511333/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2702380163/5000000000 : ℝ)|^4283 ≤ (8909287479751/20000000000000 : ℝ)^3259
        have hw : |(2702380163/5000000000 : ℝ)|=(2702380163/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-253860597/1250000000 : ℝ)|^4283 ≤ (1538385923223/12500000000000 : ℝ)^3259
        have hw : |(-253860597/1250000000 : ℝ)|=(253860597/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_11 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2256416663/5000000000 : ℝ)*x 0 + (4244650153/10000000000 : ℝ)*x 1 + (4244650451/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2256416663/5000000000 : ℝ)^4283 ≤ (8786479838169/25000000000000 : ℝ)^3259 := by
    have hnat : (2256416663 : ℕ)^4283*25000000000000^3259 ≤ 8786479838169^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2256416663 5000000000 8786479838169 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4244650153/10000000000 : ℝ)^4283 ≤ (6485407763679/20000000000000 : ℝ)^3259 := by
    have hnat : (4244650153 : ℕ)^4283*20000000000000^3259 ≤ 6485407763679^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244650153 10000000000 6485407763679 20000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4244650451/10000000000 : ℝ)^4283 ≤ (32427041810283/100000000000000 : ℝ)^3259 := by
    have hnat : (4244650451 : ℕ)^4283*100000000000000^3259 ≤ 32427041810283^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4244650451 10000000000 32427041810283 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2256416663/5000000000 : ℝ), (4244650153/10000000000 : ℝ), (4244650451/10000000000 : ℝ)] ![(8786479838169/25000000000000 : ℝ), (6485407763679/20000000000000 : ℝ), (32427041810283/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2256416663/5000000000 : ℝ)|^4283 ≤ (8786479838169/25000000000000 : ℝ)^3259
        have hw : |(2256416663/5000000000 : ℝ)|=(2256416663/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4244650153/10000000000 : ℝ)|^4283 ≤ (6485407763679/20000000000000 : ℝ)^3259
        have hw : |(4244650153/10000000000 : ℝ)|=(4244650153/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4244650451/10000000000 : ℝ)|^4283 ≤ (32427041810283/100000000000000 : ℝ)^3259
        have hw : |(4244650451/10000000000 : ℝ)|=(4244650451/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_12 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-981754759/5000000000 : ℝ)*x 0 + (5475304171/10000000000 : ℝ)*x 1 + (656679241/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (981754759/5000000000 : ℝ)^4283 ≤ (11773325928581/100000000000000 : ℝ)^3259 := by
    have hnat : (981754759 : ℕ)^4283*100000000000000^3259 ≤ 11773325928581^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      981754759 5000000000 11773325928581 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5475304171/10000000000 : ℝ)^4283 ≤ (354000904291/781250000000 : ℝ)^3259 := by
    have hnat : (5475304171 : ℕ)^4283*781250000000^3259 ≤ 354000904291^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5475304171 10000000000 354000904291 781250000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (656679241/1250000000 : ℝ)^4283 ≤ (42914558319863/100000000000000 : ℝ)^3259 := by
    have hnat : (656679241 : ℕ)^4283*100000000000000^3259 ≤ 42914558319863^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656679241 1250000000 42914558319863 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-981754759/5000000000 : ℝ), (5475304171/10000000000 : ℝ), (656679241/1250000000 : ℝ)] ![(11773325928581/100000000000000 : ℝ), (354000904291/781250000000 : ℝ), (42914558319863/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-981754759/5000000000 : ℝ)|^4283 ≤ (11773325928581/100000000000000 : ℝ)^3259
        have hw : |(-981754759/5000000000 : ℝ)|=(981754759/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5475304171/10000000000 : ℝ)|^4283 ≤ (354000904291/781250000000 : ℝ)^3259
        have hw : |(5475304171/10000000000 : ℝ)|=(5475304171/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(656679241/1250000000 : ℝ)|^4283 ≤ (42914558319863/100000000000000 : ℝ)^3259
        have hw : |(656679241/1250000000 : ℝ)|=(656679241/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_13 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (336337497/625000000 : ℝ)*x 0 + (-2091473557/10000000000 : ℝ)*x 1 + (2626717029/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (336337497/625000000 : ℝ)^4283 ≤ (4429357471013/10000000000000 : ℝ)^3259 := by
    have hnat : (336337497 : ℕ)^4283*10000000000000^3259 ≤ 4429357471013^3259*625000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      336337497 625000000 4429357471013 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2091473557/10000000000 : ℝ)^4283 ≤ (12791865554793/100000000000000 : ℝ)^3259 := by
    have hnat : (2091473557 : ℕ)^4283*100000000000000^3259 ≤ 12791865554793^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091473557 10000000000 12791865554793 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2626717029/5000000000 : ℝ)^4283 ≤ (42914559715487/100000000000000 : ℝ)^3259 := by
    have hnat : (2626717029 : ℕ)^4283*100000000000000^3259 ≤ 42914559715487^3259*5000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2626717029 5000000000 42914559715487 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(336337497/625000000 : ℝ), (-2091473557/10000000000 : ℝ), (2626717029/5000000000 : ℝ)] ![(4429357471013/10000000000000 : ℝ), (12791865554793/100000000000000 : ℝ), (42914559715487/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(336337497/625000000 : ℝ)|^4283 ≤ (4429357471013/10000000000000 : ℝ)^3259
        have hw : |(336337497/625000000 : ℝ)|=(336337497/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2091473557/10000000000 : ℝ)|^4283 ≤ (12791865554793/100000000000000 : ℝ)^3259
        have hw : |(-2091473557/10000000000 : ℝ)|=(2091473557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2626717029/5000000000 : ℝ)|^4283 ≤ (42914559715487/100000000000000 : ℝ)^3259
        have hw : |(2626717029/5000000000 : ℝ)|=(2626717029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_14 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5381400083/10000000000 : ℝ)*x 0 + (656679199/1250000000 : ℝ)*x 1 + (-2091474003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5381400083/10000000000 : ℝ)^4283 ≤ (11073394031791/25000000000000 : ℝ)^3259 := by
    have hnat : (5381400083 : ℕ)^4283*25000000000000^3259 ≤ 11073394031791^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5381400083 10000000000 11073394031791 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (656679199/1250000000 : ℝ)^4283 ≤ (5364319339089/12500000000000 : ℝ)^3259 := by
    have hnat : (656679199 : ℕ)^4283*12500000000000^3259 ≤ 5364319339089^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      656679199 1250000000 5364319339089 12500000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2091474003/10000000000 : ℝ)^4283 ≤ (6395934569859/50000000000000 : ℝ)^3259 := by
    have hnat : (2091474003 : ℕ)^4283*50000000000000^3259 ≤ 6395934569859^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2091474003 10000000000 6395934569859 50000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5381400083/10000000000 : ℝ), (656679199/1250000000 : ℝ), (-2091474003/10000000000 : ℝ)] ![(11073394031791/25000000000000 : ℝ), (5364319339089/12500000000000 : ℝ), (6395934569859/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5381400083/10000000000 : ℝ)|^4283 ≤ (11073394031791/25000000000000 : ℝ)^3259
        have hw : |(5381400083/10000000000 : ℝ)|=(5381400083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(656679199/1250000000 : ℝ)|^4283 ≤ (5364319339089/12500000000000 : ℝ)^3259
        have hw : |(656679199/1250000000 : ℝ)|=(656679199/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2091474003/10000000000 : ℝ)|^4283 ≤ (6395934569859/50000000000000 : ℝ)^3259
        have hw : |(-2091474003/10000000000 : ℝ)|=(2091474003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1323_box_15 (p : ℝ) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (207775829/500000000 : ℝ)*x 0 + (552912891/1250000000 : ℝ)*x 1 + (4423302997/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (207775829/500000000 : ℝ)^4283 ≤ (31535113806267/100000000000000 : ℝ)^3259 := by
    have hnat : (207775829 : ℕ)^4283*100000000000000^3259 ≤ 31535113806267^3259*500000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      207775829 500000000 31535113806267 100000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (552912891/1250000000 : ℝ)^4283 ≤ (3423244375581/10000000000000 : ℝ)^3259 := by
    have hnat : (552912891 : ℕ)^4283*10000000000000^3259 ≤ 3423244375581^3259*1250000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      552912891 1250000000 3423244375581 10000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4423302997/10000000000 : ℝ)^4283 ≤ (8558110605859/25000000000000 : ℝ)^3259 := by
    have hnat : (4423302997 : ℕ)^4283*25000000000000^3259 ≤ 8558110605859^3259*10000000000^4283 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4423302997 10000000000 8558110605859 25000000000000 4283 3259 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4283/1024 : ℝ)) 4283 3259 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(207775829/500000000 : ℝ), (552912891/1250000000 : ℝ), (4423302997/10000000000 : ℝ)] ![(31535113806267/100000000000000 : ℝ), (3423244375581/10000000000000 : ℝ), (8558110605859/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(207775829/500000000 : ℝ)|^4283 ≤ (31535113806267/100000000000000 : ℝ)^3259
        have hw : |(207775829/500000000 : ℝ)|=(207775829/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(552912891/1250000000 : ℝ)|^4283 ≤ (3423244375581/10000000000000 : ℝ)^3259
        have hw : |(552912891/1250000000 : ℝ)|=(552912891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4423302997/10000000000 : ℝ)|^4283 ≤ (8558110605859/25000000000000 : ℝ)^3259
        have hw : |(4423302997/10000000000 : ℝ)|=(4423302997/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1323_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    -(1964/3125 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(7363/12500 : ℝ) ∧ (39921/50000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42139/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7347/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2221/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7347/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2221/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7347/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2221/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7347/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2221/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7347/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2221/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7347/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2221/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2221/20000 : ℝ) ^ (2141/512 : ℝ) ≤ (10202383557347827/100000000000000000000 : ℝ) := by
    have hpowers : (2221/20000 : ℝ)^2141 ≤ (10202383557347827/100000000000000000000 : ℝ)^512 := by
      have hnat : (2221 : ℕ)^2141*100000000000000000000^512 ≤ 10202383557347827^512*20000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2221 20000 10202383557347827 100000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2221/20000 : ℝ)) (X := (10202383557347827/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hpowhi : (7347/50000 : ℝ) ^ (2141/512 : ℝ) ≤ (16453145635066619/50000000000000000000 : ℝ) := by
    have hpowers : (7347/50000 : ℝ)^2141 ≤ (16453145635066619/50000000000000000000 : ℝ)^512 := by
      have hnat : (7347 : ℕ)^2141*50000000000000000000^512 ≤ 16453145635066619^512*50000^2141 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7347 50000 16453145635066619 50000000000000000000 2141 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7347/50000 : ℝ)) (X := (16453145635066619/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010202383557347827/50000000000000000000 : ℝ) ≤ (10000487922927813/10000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (50010202383557347827/50000000000000000000 : ℝ)^512 ≤ (10000487922927813/10000000000000000 : ℝ)^2141 := by
      have hnat : (50010202383557347827 : ℕ)^512*10000000000000000^2141 ≤ 10000487922927813^2141*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010202383557347827 50000000000000000000 10000487922927813 10000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000487922927813/10000000000000000 : ℝ)) (X := (50010202383557347827/50000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (20008621734965496213/20000000000000000000 : ℝ) ≤ (400041229374531/400000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (20008621734965496213/20000000000000000000 : ℝ)^512 ≤ (400041229374531/400000000000000 : ℝ)^2141 := by
      have hnat : (20008621734965496213 : ℕ)^512*400000000000000^2141 ≤ 400041229374531^2141*20000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20008621734965496213 20000000000000000000 400041229374531 400000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (400041229374531/400000000000000 : ℝ)) (X := (20008621734965496213/20000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25016453145635066619/25000000000000000000 : ℝ) ≤ (10001573545798737/10000000000000000 : ℝ) ^ (2141/512 : ℝ) := by
    have hpowers : (25016453145635066619/25000000000000000000 : ℝ)^512 ≤ (10001573545798737/10000000000000000 : ℝ)^2141 := by
      have hnat : (25016453145635066619 : ℕ)^512*10000000000000000^2141 ≤ 10001573545798737^2141*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25016453145635066619 25000000000000000000 10001573545798737 10000000000000000 512 2141 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001573545798737/10000000000000000 : ℝ)) (X := (25016453145635066619/25000000000000000000 : ℝ)) (by norm_num) 2141 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10202383557347827/100000000000000000000 : ℝ) ≤ ((35879695313406309837/35890000000000000000 : ℝ)+2*(271405717731/179450000000000 : ℝ)*(2221/20000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (35879695313406309837/35890000000000000000 : ℝ)+2*(271405717731/179450000000000 : ℝ)*(2221/20000 : ℝ)=(10000487922927813/10000000000000000 : ℝ) by norm_num, show 1+2*(10202383557347827/100000000000000000000 : ℝ)=(50010202383557347827/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(16453145635066619/50000000000000000000 : ℝ)+(10202383557347827/100000000000000000000 : ℝ) ≤ ((35879695313406309837/35890000000000000000 : ℝ)+(271405717731/179450000000000 : ℝ)*((7347/50000 : ℝ)+(2221/20000 : ℝ)))^(2141/512 : ℝ) := by
    rw [show (35879695313406309837/35890000000000000000 : ℝ)+(271405717731/179450000000000 : ℝ)*((7347/50000 : ℝ)+(2221/20000 : ℝ))=(400041229374531/400000000000000 : ℝ) by norm_num, show 1+(16453145635066619/50000000000000000000 : ℝ)+(10202383557347827/100000000000000000000 : ℝ)=(20008621734965496213/20000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(16453145635066619/50000000000000000000 : ℝ) ≤ ((35879695313406309837/35890000000000000000 : ℝ)+2*(271405717731/179450000000000 : ℝ)*(7347/50000 : ℝ))^(2141/512 : ℝ) := by
    rw [show (35879695313406309837/35890000000000000000 : ℝ)+2*(271405717731/179450000000000 : ℝ)*(7347/50000 : ℝ)=(10001573545798737/10000000000000000 : ℝ) by norm_num, show 1+2*(16453145635066619/50000000000000000000 : ℝ)=(25016453145635066619/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (35879695313406309837/35890000000000000000 : ℝ)*(X 1 0+X 2 0)+(271405717731/179450000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (35879695313406309837/35890000000000000000 : ℝ)) (alpha := (271405717731/179450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (35879695313406309837/35890000000000000000 : ℝ)*(X 0 1+X 2 1)+(271405717731/179450000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (35879695313406309837/35890000000000000000 : ℝ)) (alpha := (271405717731/179450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (35879695313406309837/35890000000000000000 : ℝ)*(X 0 2+X 1 2)+(271405717731/179450000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2141/512 : ℝ)) (lo := (2221/20000 : ℝ)) (hi := (7347/50000 : ℝ)) (c := (35879695313406309837/35890000000000000000 : ℝ)) (alpha := (271405717731/179450000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1891718601/10000000000 : ℝ)*X 0 0+(2695366431/5000000000 : ℝ)*X 0 1+(5390732903/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((528488823/1000000000 : ℝ)*X 1 0+(-2036632593/10000000000 : ℝ)*X 1 1+(84230207/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((660611059/1250000000 : ℝ)*X 2 0+(2695366497/5000000000 : ℝ)*X 2 1+(-2036632611/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4480260831/10000000000 : ℝ)*X 0 0+(4261224107/10000000000 : ℝ)*X 0 1+(213061203/500000000 : ℝ)*X 0 2+(4480260831/10000000000 : ℝ)*X 1 0+(4261224107/10000000000 : ℝ)*X 1 1+(213061203/500000000 : ℝ)*X 1 2+(4480260831/10000000000 : ℝ)*X 2 0+(4261224107/10000000000 : ℝ)*X 2 1+(213061203/500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2232038743/10000000000 : ℝ)*X 0 0+(658060911/1250000000 : ℝ)*X 0 1+(164515239/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((671703989/1250000000 : ℝ)*X 1 0+(-2087155147/10000000000 : ℝ)*X 1 1+(526448787/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5373632467/10000000000 : ℝ)*X 2 0+(5264487707/10000000000 : ℝ)*X 2 1+(-1043577309/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((261379467/625000000 : ℝ)*X 0 0+(2205132351/5000000000 : ℝ)*X 0 1+(4410264331/10000000000 : ℝ)*X 0 2+(261379467/625000000 : ℝ)*X 1 0+(2205132351/5000000000 : ℝ)*X 1 1+(4410264331/10000000000 : ℝ)*X 1 2+(261379467/625000000 : ℝ)*X 2 0+(2205132351/5000000000 : ℝ)*X 2 1+(4410264331/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-2160624117/10000000000 : ℝ)*X 0 0+(5177667173/10000000000 : ℝ)*X 0 1+(5404759827/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((1318755567/2500000000 : ℝ)*X 1 0+(-1015442273/5000000000 : ℝ)*X 1 1+(540476089/1000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((2637511333/5000000000 : ℝ)*X 2 0+(2702380163/5000000000 : ℝ)*X 2 1+(-253860597/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((2256416663/5000000000 : ℝ)*X 0 0+(4244650153/10000000000 : ℝ)*X 0 1+(4244650451/10000000000 : ℝ)*X 0 2+(2256416663/5000000000 : ℝ)*X 1 0+(4244650153/10000000000 : ℝ)*X 1 1+(4244650451/10000000000 : ℝ)*X 1 2+(2256416663/5000000000 : ℝ)*X 2 0+(4244650153/10000000000 : ℝ)*X 2 1+(4244650451/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-981754759/5000000000 : ℝ)*X 0 0+(5475304171/10000000000 : ℝ)*X 0 1+(656679241/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((336337497/625000000 : ℝ)*X 1 0+(-2091473557/10000000000 : ℝ)*X 1 1+(2626717029/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((5381400083/10000000000 : ℝ)*X 2 0+(656679199/1250000000 : ℝ)*X 2 1+(-2091474003/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((207775829/500000000 : ℝ)*X 0 0+(552912891/1250000000 : ℝ)*X 0 1+(4423302997/10000000000 : ℝ)*X 0 2+(207775829/500000000 : ℝ)*X 1 0+(552912891/1250000000 : ℝ)*X 1 1+(4423302997/10000000000 : ℝ)*X 1 2+(207775829/500000000 : ℝ)*X 2 0+(552912891/1250000000 : ℝ)*X 2 1+(4423302997/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1323_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-1964/3125 : ℝ) ≤ (-1127768512511235065102554038615039/1794500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (921683/12500000000000 : ℝ)*(upper0) + (259068169/100000000000000 : ℝ)*(lower2) + (108441979/100000000000000 : ℝ)*(upper5) + (2899235863079049/100000000000000 : ℝ)*(major0) + (2899235863079049/100000000000000 : ℝ)*(major1) + (2899235863079049/100000000000000 : ℝ)*(major2) + (5042326271/100000000000000 : ℝ)*(sp3) + (3936556945056129/100000000000000 : ℝ)*(sp4) + (1968263442802483/50000000000000 : ℝ)*(sp5) + (1968237314782089/50000000000000 : ℝ)*(sp6) + (470713692795279/25000000000000 : ℝ)*(sp7) + (447415633/12500000000000 : ℝ)*(sp8) + (16819388113/50000000000000 : ℝ)*(sp13) + (42947408507/50000000000000 : ℝ)*(sp14) + (941429906753693/50000000000000 : ℝ)*(f.failure) + (492070065547649/12500000000000 : ℝ)*(f.sum) + (18631247402343/4486250000000000000000000000 : ℝ)*base66 + (231329737686335894987/3589000000000000000000000000000000 : ℝ)*base68 + (980746136382894987/3589000000000000000000000000000000 : ℝ)*base70 + (5507168405148105013/3589000000000000000000000000000000 : ℝ)*base71 + (588105989314387/17945000000000000000000000000 : ℝ)*base74 + (10650237393905105013/3589000000000000000000000000000000 : ℝ)*base75 + (17307932681332105013/3589000000000000000000000000000000 : ℝ)*base77 + (9300574638674105013/3589000000000000000000000000000000 : ℝ)*base79 + (29281394012703/4486250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (8363847/2500000000000000000000 : ℝ)*base90 + (8363847/2500000000000000000000 : ℝ)*base92 + (8363847/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (7363/12500 : ℝ) ≤ (528541910960224360759413134600157/897250000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1175031/50000000000000 : ℝ)*(upper0) + (5042793/50000000000000 : ℝ)*(lower1) + (11283473/25000000000000 : ℝ)*(upper4) + (576449/100000000000000 : ℝ)*(upper5) + (1483649609074213/50000000000000 : ℝ)*(major0) + (1483649609074213/50000000000000 : ℝ)*(major1) + (1483649609074213/50000000000000 : ℝ)*(major2) + (996975100294051/25000000000000 : ℝ)*(sp0) + (996972575508981/25000000000000 : ℝ)*(sp1) + (498487011375473/12500000000000 : ℝ)*(sp2) + (192706031682249/10000000000000 : ℝ)*(sp3) + (252478507/2500000000000 : ℝ)*(sp5) + (4310172419/100000000000000 : ℝ)*(sp6) + (523556517/25000000000000 : ℝ)*(sp7) + (963531205524279/50000000000000 : ℝ)*(f.failure) + (996975100294051/25000000000000 : ℝ)*(f.sum) + (26807645697161/8972500000000000000000000000 : ℝ)*base65 + (60548596282222533281/1794500000000000000000000000000000 : ℝ)*base67 + (10395698079994466719/1794500000000000000000000000000000 : ℝ)*base70 + (11299661482958533281/1794500000000000000000000000000000 : ℝ)*base71 + (70404346742441/8972500000000000000000000000 : ℝ)*base73 + (3724042347024466719/1794500000000000000000000000000000 : ℝ)*base76 + (15034167006284033281/1794500000000000000000000000000000 : ℝ)*base77 + (18362796383168033281/1794500000000000000000000000000000 : ℝ)*base79 + (37201794790689/8972500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (11075659/2500000000000000000000 : ℝ)*base89 + (11075659/2500000000000000000000 : ℝ)*base91 + (11075659/2500000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (39921/50000 : ℝ) ≤ (1432817069470625920329888328483119/1794500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12487207/20000000000000 : ℝ)*(lower1) + (200643967/100000000000000 : ℝ)*(lower3) + (198771753/100000000000000 : ℝ)*(lower5) + (3280208267665671/100000000000000 : ℝ)*(major0) + (3280208267665671/100000000000000 : ℝ)*(major1) + (3280208267665671/100000000000000 : ℝ)*(major2) + (984233773/2500000000000 : ℝ)*(sp0) + (471587315197/100000000000000 : ℝ)*(sp1) + (58790114561/20000000000000 : ℝ)*(sp2) + (160955620117/100000000000000 : ℝ)*(sp3) + (2201743139681081/50000000000000 : ℝ)*(sp8) + (1100763515349471/25000000000000 : ℝ)*(sp9) + (1100807924535069/25000000000000 : ℝ)*(sp10) + (2130114958034989/100000000000000 : ℝ)*(sp11) + (1065137956827553/50000000000000 : ℝ)*(f.failure) + (2201762824356541/50000000000000 : ℝ)*(f.sum) + (3512714258813/17945000000000000000000000000 : ℝ)*base66 + (19999090436623294373/3589000000000000000000000000000000 : ℝ)*base68 + (62609230548422294373/3589000000000000000000000000000000 : ℝ)*base70 + (8213722871347705627/3589000000000000000000000000000000 : ℝ)*base71 + (55492032288693/17945000000000000000000000000 : ℝ)*base74 + (141473010015079705627/3589000000000000000000000000000000 : ℝ)*base75 + (2273254740041705627/3589000000000000000000000000000000 : ℝ)*base77 + (4404397323256705627/3589000000000000000000000000000000 : ℝ)*base79 + (285449722693771/8972500000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (10640787/2500000000000000000000 : ℝ)*base90 + (10640787/2500000000000000000000 : ℝ)*base92 + (10640787/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (-42139/50000 : ℝ) ≤ (-40873458616561938143605612192551/48500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (15361083/12500000000000 : ℝ)*(lower0) + (7038257/50000000000000 : ℝ)*(lower1) + (157440587/100000000000000 : ℝ)*(lower4) + (3316443624194761/100000000000000 : ℝ)*(major0) + (3316443624194761/100000000000000 : ℝ)*(major1) + (3316443624194761/100000000000000 : ℝ)*(major2) + (4026896071/12500000000000 : ℝ)*(sp0) + (359870657161/100000000000000 : ℝ)*(sp5) + (79823958899/12500000000000 : ℝ)*(sp6) + (59788103619/50000000000000 : ℝ)*(sp7) + (901427680557863/20000000000000 : ℝ)*(sp12) + (2253405373650361/50000000000000 : ℝ)*(sp13) + (450653202628669/10000000000000 : ℝ)*(sp14) + (1076844389179741/50000000000000 : ℝ)*(sp15) + (2153808354566719/100000000000000 : ℝ)*(f.failure) + (4507170617957883/100000000000000 : ℝ)*(f.sum) + (1766826482027/280390625000000000000000000 : ℝ)*base66 + (22441275593960636043/3589000000000000000000000000000000 : ℝ)*base68 + (32313108301427636043/3589000000000000000000000000000000 : ℝ)*base70 + (58378025258351636043/3589000000000000000000000000000000 : ℝ)*base72 + (807138854278887/17945000000000000000000000000 : ℝ)*base73 + (50509534698685636043/3589000000000000000000000000000000 : ℝ)*base76 + (31842031500813636043/3589000000000000000000000000000000 : ℝ)*base78 + (16331766628587636043/3589000000000000000000000000000000 : ℝ)*base80 + (22087652476261/2243125000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (5054899/5000000000000000000000 : ℝ)*base89 + (5054899/5000000000000000000000 : ℝ)*base91 + (5054899/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1323_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1964/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(7363/12500 : ℝ) else (39921/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42139/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1323_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1323_b3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1964/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(7363/12500 : ℝ) else (39921/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42139/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1323_box p A d hA hpa hpb X hX hsign hratio hlower
  exact h0
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2141/512 : ℝ) ≤ p) (hpb : p ≤ (4283/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (76990221/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7347/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2221/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(1964/3125 : ℝ) ≤ X j i ∧ X j i ≤ -(7363/12500 : ℝ) else (39921/50000 : ℝ) ≤ X j i ∧ X j i ≤ (42139/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1323_b3 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
