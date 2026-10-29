-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1633_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T01:00:48.568981+00:00
-- url     : https://prove2.me/submissions/34b0d9c8-0436-44e7-a9e5-6a41b2f0ff40

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
theorem support_rectangle_w1633_s3_0 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-412000099/2500000000 : ℝ)*x 0 + (2726380369/5000000000 : ℝ)*x 1 + (5182556143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412000099/2500000000 : ℝ)^4851 ≤ (10172708813611/100000000000000 : ℝ)^3827 := by
    have hnat : (412000099 : ℕ)^4851*100000000000000^3827 ≤ 10172708813611^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412000099 2500000000 10172708813611 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2726380369/5000000000 : ℝ)^4851 ≤ (11589968357191/25000000000000 : ℝ)^3827 := by
    have hnat : (2726380369 : ℕ)^4851*25000000000000^3827 ≤ 11589968357191^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2726380369 5000000000 11589968357191 25000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182556143/10000000000 : ℝ)^4851 ≤ (43467417744737/100000000000000 : ℝ)^3827 := by
    have hnat : (5182556143 : ℕ)^4851*100000000000000^3827 ≤ 43467417744737^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182556143 10000000000 43467417744737 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412000099/2500000000 : ℝ), (2726380369/5000000000 : ℝ), (5182556143/10000000000 : ℝ)] ![(10172708813611/100000000000000 : ℝ), (11589968357191/25000000000000 : ℝ), (43467417744737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412000099/2500000000 : ℝ)|^4851 ≤ (10172708813611/100000000000000 : ℝ)^3827
        have hw : |(-412000099/2500000000 : ℝ)|=(412000099/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2726380369/5000000000 : ℝ)|^4851 ≤ (11589968357191/25000000000000 : ℝ)^3827
        have hw : |(2726380369/5000000000 : ℝ)|=(2726380369/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182556143/10000000000 : ℝ)|^4851 ≤ (43467417744737/100000000000000 : ℝ)^3827
        have hw : |(5182556143/10000000000 : ℝ)|=(5182556143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s3_1 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (668789971/1250000000 : ℝ)*x 0 + (-446800047/2500000000 : ℝ)*x 1 + (5182556143/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (668789971/1250000000 : ℝ)^4851 ≤ (45258652932557/100000000000000 : ℝ)^3827 := by
    have hnat : (668789971 : ℕ)^4851*100000000000000^3827 ≤ 45258652932557^3827*1250000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      668789971 1250000000 45258652932557 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (446800047/2500000000 : ℝ)^4851 ≤ (5636964651449/50000000000000 : ℝ)^3827 := by
    have hnat : (446800047 : ℕ)^4851*50000000000000^3827 ≤ 5636964651449^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446800047 2500000000 5636964651449 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5182556143/10000000000 : ℝ)^4851 ≤ (43467417744737/100000000000000 : ℝ)^3827 := by
    have hnat : (5182556143 : ℕ)^4851*100000000000000^3827 ≤ 43467417744737^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182556143 10000000000 43467417744737 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(668789971/1250000000 : ℝ), (-446800047/2500000000 : ℝ), (5182556143/10000000000 : ℝ)] ![(45258652932557/100000000000000 : ℝ), (5636964651449/50000000000000 : ℝ), (43467417744737/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(668789971/1250000000 : ℝ)|^4851 ≤ (45258652932557/100000000000000 : ℝ)^3827
        have hw : |(668789971/1250000000 : ℝ)|=(668789971/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-446800047/2500000000 : ℝ)|^4851 ≤ (5636964651449/50000000000000 : ℝ)^3827
        have hw : |(-446800047/2500000000 : ℝ)|=(446800047/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5182556143/10000000000 : ℝ)|^4851 ≤ (43467417744737/100000000000000 : ℝ)^3827
        have hw : |(5182556143/10000000000 : ℝ)|=(5182556143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s3_2 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (535031977/1000000000 : ℝ)*x 0 + (5182556143/10000000000 : ℝ)*x 1 + (-893600093/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535031977/1000000000 : ℝ)^4851 ≤ (22629326477001/50000000000000 : ℝ)^3827 := by
    have hnat : (535031977 : ℕ)^4851*50000000000000^3827 ≤ 22629326477001^3827*1000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535031977 1000000000 22629326477001 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5182556143/10000000000 : ℝ)^4851 ≤ (43467417744737/100000000000000 : ℝ)^3827 := by
    have hnat : (5182556143 : ℕ)^4851*100000000000000^3827 ≤ 43467417744737^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5182556143 10000000000 43467417744737 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (893600093/5000000000 : ℝ)^4851 ≤ (5636964643453/50000000000000 : ℝ)^3827 := by
    have hnat : (893600093 : ℕ)^4851*50000000000000^3827 ≤ 5636964643453^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      893600093 5000000000 5636964643453 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535031977/1000000000 : ℝ), (5182556143/10000000000 : ℝ), (-893600093/5000000000 : ℝ)] ![(22629326477001/50000000000000 : ℝ), (43467417744737/100000000000000 : ℝ), (5636964643453/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535031977/1000000000 : ℝ)|^4851 ≤ (22629326477001/50000000000000 : ℝ)^3827
        have hw : |(535031977/1000000000 : ℝ)|=(535031977/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5182556143/10000000000 : ℝ)|^4851 ≤ (43467417744737/100000000000000 : ℝ)^3827
        have hw : |(5182556143/10000000000 : ℝ)|=(5182556143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-893600093/5000000000 : ℝ)|^4851 ≤ (5636964643453/50000000000000 : ℝ)^3827
        have hw : |(-893600093/5000000000 : ℝ)|=(893600093/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s3_3 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (524242297/1250000000 : ℝ)*x 0 + (3862244183/10000000000 : ℝ)*x 1 + (4546381649/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524242297/1250000000 : ℝ)^4851 ≤ (6647771348711/20000000000000 : ℝ)^3827 := by
    have hnat : (524242297 : ℕ)^4851*20000000000000^3827 ≤ 6647771348711^3827*1250000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524242297 1250000000 6647771348711 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3862244183/10000000000 : ℝ)^4851 ≤ (14971296123921/50000000000000 : ℝ)^3827 := by
    have hnat : (3862244183 : ℕ)^4851*50000000000000^3827 ≤ 14971296123921^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3862244183 10000000000 14971296123921 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4546381649/10000000000 : ℝ)^4851 ≤ (2301159436681/6250000000000 : ℝ)^3827 := by
    have hnat : (4546381649 : ℕ)^4851*6250000000000^3827 ≤ 2301159436681^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4546381649 10000000000 2301159436681 6250000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(524242297/1250000000 : ℝ), (3862244183/10000000000 : ℝ), (4546381649/10000000000 : ℝ)] ![(6647771348711/20000000000000 : ℝ), (14971296123921/50000000000000 : ℝ), (2301159436681/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(524242297/1250000000 : ℝ)|^4851 ≤ (6647771348711/20000000000000 : ℝ)^3827
        have hw : |(524242297/1250000000 : ℝ)|=(524242297/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3862244183/10000000000 : ℝ)|^4851 ≤ (14971296123921/50000000000000 : ℝ)^3827
        have hw : |(3862244183/10000000000 : ℝ)|=(3862244183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4546381649/10000000000 : ℝ)|^4851 ≤ (2301159436681/6250000000000 : ℝ)^3827
        have hw : |(4546381649/10000000000 : ℝ)|=(4546381649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s3_4 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-824033729/5000000000 : ℝ)*x 0 + (5184588541/10000000000 : ℝ)*x 1 + (5450706893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (824033729/5000000000 : ℝ)^4851 ≤ (10173233537673/100000000000000 : ℝ)^3827 := by
    have hnat : (824033729 : ℕ)^4851*100000000000000^3827 ≤ 10173233537673^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      824033729 5000000000 10173233537673 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184588541/10000000000 : ℝ)^4851 ≤ (21744513111399/50000000000000 : ℝ)^3827 := by
    have hnat : (5184588541 : ℕ)^4851*50000000000000^3827 ≤ 21744513111399^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184588541 10000000000 21744513111399 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450706893/10000000000 : ℝ)^4851 ≤ (72402719093/156250000000 : ℝ)^3827 := by
    have hnat : (5450706893 : ℕ)^4851*156250000000^3827 ≤ 72402719093^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450706893 10000000000 72402719093 156250000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-824033729/5000000000 : ℝ), (5184588541/10000000000 : ℝ), (5450706893/10000000000 : ℝ)] ![(10173233537673/100000000000000 : ℝ), (21744513111399/50000000000000 : ℝ), (72402719093/156250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-824033729/5000000000 : ℝ)|^4851 ≤ (10173233537673/100000000000000 : ℝ)^3827
        have hw : |(-824033729/5000000000 : ℝ)|=(824033729/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184588541/10000000000 : ℝ)|^4851 ≤ (21744513111399/50000000000000 : ℝ)^3827
        have hw : |(5184588541/10000000000 : ℝ)|=(5184588541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450706893/10000000000 : ℝ)|^4851 ≤ (72402719093/156250000000 : ℝ)^3827
        have hw : |(5450706893/10000000000 : ℝ)|=(5450706893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s3_5 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278293163/10000000000 : ℝ)*x 0 + (-1519049441/10000000000 : ℝ)*x 1 + (272535347/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278293163/10000000000 : ℝ)^4851 ≤ (2780484101637/6250000000000 : ℝ)^3827 := by
    have hnat : (5278293163 : ℕ)^4851*6250000000000^3827 ≤ 2780484101637^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278293163 10000000000 2780484101637 6250000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1519049441/10000000000 : ℝ)^4851 ≤ (1834902724303/20000000000000 : ℝ)^3827 := by
    have hnat : (1519049441 : ℕ)^4851*20000000000000^3827 ≤ 1834902724303^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519049441 10000000000 1834902724303 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (272535347/500000000 : ℝ)^4851 ≤ (46337740725989/100000000000000 : ℝ)^3827 := by
    have hnat : (272535347 : ℕ)^4851*100000000000000^3827 ≤ 46337740725989^3827*500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      272535347 500000000 46337740725989 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278293163/10000000000 : ℝ), (-1519049441/10000000000 : ℝ), (272535347/500000000 : ℝ)] ![(2780484101637/6250000000000 : ℝ), (1834902724303/20000000000000 : ℝ), (46337740725989/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278293163/10000000000 : ℝ)|^4851 ≤ (2780484101637/6250000000000 : ℝ)^3827
        have hw : |(5278293163/10000000000 : ℝ)|=(5278293163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1519049441/10000000000 : ℝ)|^4851 ≤ (1834902724303/20000000000000 : ℝ)^3827
        have hw : |(-1519049441/10000000000 : ℝ)|=(1519049441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(272535347/500000000 : ℝ)|^4851 ≤ (46337740725989/100000000000000 : ℝ)^3827
        have hw : |(272535347/500000000 : ℝ)|=(272535347/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s3_6 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278293217/10000000000 : ℝ)*x 0 + (1090141391/2000000000 : ℝ)*x 1 + (-303809869/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278293217/10000000000 : ℝ)^4851 ≤ (44487746203109/100000000000000 : ℝ)^3827 := by
    have hnat : (5278293217 : ℕ)^4851*100000000000000^3827 ≤ 44487746203109^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278293217 10000000000 44487746203109 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090141391/2000000000 : ℝ)^4851 ≤ (11584435221907/25000000000000 : ℝ)^3827 := by
    have hnat : (1090141391 : ℕ)^4851*25000000000000^3827 ≤ 11584435221907^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090141391 2000000000 11584435221907 25000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (303809869/2000000000 : ℝ)^4851 ≤ (917451288657/10000000000000 : ℝ)^3827 := by
    have hnat : (303809869 : ℕ)^4851*10000000000000^3827 ≤ 917451288657^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      303809869 2000000000 917451288657 10000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278293217/10000000000 : ℝ), (1090141391/2000000000 : ℝ), (-303809869/2000000000 : ℝ)] ![(44487746203109/100000000000000 : ℝ), (11584435221907/25000000000000 : ℝ), (917451288657/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278293217/10000000000 : ℝ)|^4851 ≤ (44487746203109/100000000000000 : ℝ)^3827
        have hw : |(5278293217/10000000000 : ℝ)|=(5278293217/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090141391/2000000000 : ℝ)|^4851 ≤ (11584435221907/25000000000000 : ℝ)^3827
        have hw : |(1090141391/2000000000 : ℝ)|=(1090141391/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-303809869/2000000000 : ℝ)|^4851 ≤ (917451288657/10000000000000 : ℝ)^3827
        have hw : |(-303809869/2000000000 : ℝ)|=(303809869/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s3_7 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2097054063/5000000000 : ℝ)*x 0 + (2270617939/5000000000 : ℝ)*x 1 + (483430523/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2097054063/5000000000 : ℝ)^4851 ≤ (16620281037853/50000000000000 : ℝ)^3827 := by
    have hnat : (2097054063 : ℕ)^4851*50000000000000^3827 ≤ 16620281037853^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2097054063 5000000000 16620281037853 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2270617939/5000000000 : ℝ)^4851 ≤ (36765735865291/100000000000000 : ℝ)^3827 := by
    have hnat : (2270617939 : ℕ)^4851*100000000000000^3827 ≤ 36765735865291^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2270617939 5000000000 36765735865291 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (483430523/1250000000 : ℝ)^4851 ≤ (29993702038579/100000000000000 : ℝ)^3827 := by
    have hnat : (483430523 : ℕ)^4851*100000000000000^3827 ≤ 29993702038579^3827*1250000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483430523 1250000000 29993702038579 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2097054063/5000000000 : ℝ), (2270617939/5000000000 : ℝ), (483430523/1250000000 : ℝ)] ![(16620281037853/50000000000000 : ℝ), (36765735865291/100000000000000 : ℝ), (29993702038579/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2097054063/5000000000 : ℝ)|^4851 ≤ (16620281037853/50000000000000 : ℝ)^3827
        have hw : |(2097054063/5000000000 : ℝ)|=(2097054063/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2270617939/5000000000 : ℝ)|^4851 ≤ (36765735865291/100000000000000 : ℝ)^3827
        have hw : |(2270617939/5000000000 : ℝ)|=(2270617939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(483430523/1250000000 : ℝ)|^4851 ≤ (29993702038579/100000000000000 : ℝ)^3827
        have hw : |(483430523/1250000000 : ℝ)|=(483430523/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1633_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4101/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2621/25000 : ℝ)*pair X i i ≤ pair X i h) :
    (1057/10000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4077/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4101/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2621/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4101/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2621/25000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4101/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2621/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4101/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2621/25000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4101/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2621/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4101/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2621/25000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2621/25000 : ℝ) ^ (4847/1024 : ℝ) ≤ (2310809212781483/100000000000000000000 : ℝ) := by
    have hpowers : (2621/25000 : ℝ)^4847 ≤ (2310809212781483/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2621 : ℕ)^4847*100000000000000000000^1024 ≤ 2310809212781483^1024*25000^4847 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2621 25000 2310809212781483 100000000000000000000 4847 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2621/25000 : ℝ)) (X := (2310809212781483/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4101/25000 : ℝ) ^ (4847/1024 : ℝ) ≤ (19232884500563107/100000000000000000000 : ℝ) := by
    have hpowers : (4101/25000 : ℝ)^4847 ≤ (19232884500563107/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4101 : ℕ)^4847*100000000000000000000^1024 ≤ 19232884500563107^1024*25000^4847 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4101 25000 19232884500563107 100000000000000000000 4847 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4101/25000 : ℝ)) (X := (19232884500563107/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50002310809212781483/50000000000000000000 : ℝ) ≤ (10000097636703407/10000000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (50002310809212781483/50000000000000000000 : ℝ)^1024 ≤ (10000097636703407/10000000000000000 : ℝ)^4847 := by
      have hnat : (50002310809212781483 : ℕ)^1024*10000000000000000^4847 ≤ 10000097636703407^4847*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50002310809212781483 50000000000000000000 10000097636703407 10000000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000097636703407/10000000000000000 : ℝ)) (X := (50002310809212781483/50000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10002154369371334459/10000000000000000000 : ℝ) ≤ (1250056887941749/1250000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (10002154369371334459/10000000000000000000 : ℝ)^1024 ≤ (1250056887941749/1250000000000000 : ℝ)^4847 := by
      have hnat : (10002154369371334459 : ℕ)^1024*1250000000000000^4847 ≤ 1250056887941749^4847*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10002154369371334459 10000000000000000000 1250056887941749 1250000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250056887941749/1250000000000000 : ℝ)) (X := (10002154369371334459/10000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50019232884500563107/50000000000000000000 : ℝ) ≤ (10000812570364577/10000000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (50019232884500563107/50000000000000000000 : ℝ)^1024 ≤ (10000812570364577/10000000000000000 : ℝ)^4847 := by
      have hnat : (50019232884500563107 : ℕ)^1024*10000000000000000^4847 ≤ 10000812570364577^4847*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019232884500563107 50000000000000000000 10000812570364577 10000000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000812570364577/10000000000000000 : ℝ)) (X := (50019232884500563107/50000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2310809212781483/100000000000000000000 : ℝ) ≤ ((1479827066119511579/1480000000000000000 : ℝ)+2*(71493366117/118400000000000 : ℝ)*(2621/25000 : ℝ))^(4847/1024 : ℝ) := by
    rw [show (1479827066119511579/1480000000000000000 : ℝ)+2*(71493366117/118400000000000 : ℝ)*(2621/25000 : ℝ)=(10000097636703407/10000000000000000 : ℝ) by norm_num, show 1+2*(2310809212781483/100000000000000000000 : ℝ)=(50002310809212781483/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(19232884500563107/100000000000000000000 : ℝ)+(2310809212781483/100000000000000000000 : ℝ) ≤ ((1479827066119511579/1480000000000000000 : ℝ)+(71493366117/118400000000000 : ℝ)*((4101/25000 : ℝ)+(2621/25000 : ℝ)))^(4847/1024 : ℝ) := by
    rw [show (1479827066119511579/1480000000000000000 : ℝ)+(71493366117/118400000000000 : ℝ)*((4101/25000 : ℝ)+(2621/25000 : ℝ))=(1250056887941749/1250000000000000 : ℝ) by norm_num, show 1+(19232884500563107/100000000000000000000 : ℝ)+(2310809212781483/100000000000000000000 : ℝ)=(10002154369371334459/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(19232884500563107/100000000000000000000 : ℝ) ≤ ((1479827066119511579/1480000000000000000 : ℝ)+2*(71493366117/118400000000000 : ℝ)*(4101/25000 : ℝ))^(4847/1024 : ℝ) := by
    rw [show (1479827066119511579/1480000000000000000 : ℝ)+2*(71493366117/118400000000000 : ℝ)*(4101/25000 : ℝ)=(10000812570364577/10000000000000000 : ℝ) by norm_num, show 1+2*(19232884500563107/100000000000000000000 : ℝ)=(50019232884500563107/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1479827066119511579/1480000000000000000 : ℝ)*(X 1 0+X 2 0)+(71493366117/118400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (2621/25000 : ℝ)) (hi := (4101/25000 : ℝ)) (c := (1479827066119511579/1480000000000000000 : ℝ)) (alpha := (71493366117/118400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1479827066119511579/1480000000000000000 : ℝ)*(X 0 1+X 2 1)+(71493366117/118400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (2621/25000 : ℝ)) (hi := (4101/25000 : ℝ)) (c := (1479827066119511579/1480000000000000000 : ℝ)) (alpha := (71493366117/118400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1479827066119511579/1480000000000000000 : ℝ)*(X 0 2+X 1 2)+(71493366117/118400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (2621/25000 : ℝ)) (hi := (4101/25000 : ℝ)) (c := (1479827066119511579/1480000000000000000 : ℝ)) (alpha := (71493366117/118400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-412000099/2500000000 : ℝ)*X 0 0+(2726380369/5000000000 : ℝ)*X 0 1+(5182556143/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((668789971/1250000000 : ℝ)*X 1 0+(-446800047/2500000000 : ℝ)*X 1 1+(5182556143/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535031977/1000000000 : ℝ)*X 2 0+(5182556143/10000000000 : ℝ)*X 2 1+(-893600093/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((524242297/1250000000 : ℝ)*X 0 0+(3862244183/10000000000 : ℝ)*X 0 1+(4546381649/10000000000 : ℝ)*X 0 2+(524242297/1250000000 : ℝ)*X 1 0+(3862244183/10000000000 : ℝ)*X 1 1+(4546381649/10000000000 : ℝ)*X 1 2+(524242297/1250000000 : ℝ)*X 2 0+(3862244183/10000000000 : ℝ)*X 2 1+(4546381649/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-824033729/5000000000 : ℝ)*X 0 0+(5184588541/10000000000 : ℝ)*X 0 1+(5450706893/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278293163/10000000000 : ℝ)*X 1 0+(-1519049441/10000000000 : ℝ)*X 1 1+(272535347/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278293217/10000000000 : ℝ)*X 2 0+(1090141391/2000000000 : ℝ)*X 2 1+(-303809869/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2097054063/5000000000 : ℝ)*X 0 0+(2270617939/5000000000 : ℝ)*X 0 1+(483430523/1250000000 : ℝ)*X 0 2+(2097054063/5000000000 : ℝ)*X 1 0+(2270617939/5000000000 : ℝ)*X 1 1+(483430523/1250000000 : ℝ)*X 1 2+(2097054063/5000000000 : ℝ)*X 2 0+(2270617939/5000000000 : ℝ)*X 2 1+(483430523/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (950731352789155202818078773/74000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2069176263/100000000000000 : ℝ)*(base19) + (1938169109/100000000000000 : ℝ)*(base23) + (35416603/50000000000000 : ℝ)*(lower2) + (315076091/100000000000000 : ℝ)*(upper3) + (221340483/100000000000000 : ℝ)*(upper5) + (2581333207047771/100000000000000 : ℝ)*(major0) + (2581333207047771/100000000000000 : ℝ)*(major1) + (2581333207047771/100000000000000 : ℝ)*(major2) + (370092548553807/10000000000000 : ℝ)*(sp0) + (925237210011111/25000000000000 : ℝ)*(sp1) + (1850474485525799/50000000000000 : ℝ)*(sp2) + (182713025968661/12500000000000 : ℝ)*(sp3) + (25423682637/100000000000000 : ℝ)*(sp4) + (10868868173/100000000000000 : ℝ)*(sp7) + (1461715076617461/100000000000000 : ℝ)*(f.failure) + (925237727305177/25000000000000 : ℝ)*(f.sum) + (2209310135193/5920000000000000000000000000 : ℝ)*base66 + (28938682073803457/4000000000000000000000000000000 : ℝ)*base67 + (3333684806196543/4000000000000000000000000000000 : ℝ)*base70 + (31825649261803457/4000000000000000000000000000000 : ℝ)*base71 + (14392740789287/5920000000000000000000000000 : ℝ)*base73 + (4797839370196543/4000000000000000000000000000000 : ℝ)*base76 + (16874755389803457/4000000000000000000000000000000 : ℝ)*base77 + (14243849125803457/4000000000000000000000000000000 : ℝ)*base79 + (15155325359513/5920000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3367821/2000000000000000000000 : ℝ)*base90 + (3367821/2000000000000000000000 : ℝ)*base92 + (3367821/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (449196307017940768720912767/37000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1807520731/100000000000000 : ℝ)*(base19) + (50206319/2500000000000 : ℝ)*(base23) + (139978391/50000000000000 : ℝ)*(upper3) + (12026199/20000000000000 : ℝ)*(lower4) + (24063247/10000000000000 : ℝ)*(upper5) + (1310465947594191/50000000000000 : ℝ)*(major0) + (1310465947594191/50000000000000 : ℝ)*(major1) + (1310465947594191/50000000000000 : ℝ)*(major2) + (2610465281/12500000000000 : ℝ)*(sp1) + (3053525139/12500000000000 : ℝ)*(sp2) + (187886250636597/5000000000000 : ℝ)*(sp4) + (11742819754653/312500000000 : ℝ)*(sp5) + (939424644069517/25000000000000 : ℝ)*(sp6) + (742069186481731/50000000000000 : ℝ)*(sp7) + (742069186481731/50000000000000 : ℝ)*(f.failure) + (187886250636597/5000000000000 : ℝ)*(f.sum) + (11927617698027/2960000000000000000000000000 : ℝ)*base65 + (5028428049269597/2000000000000000000000000000000 : ℝ)*base67 + (4156128454730403/2000000000000000000000000000000 : ℝ)*base70 + (16497064089269597/2000000000000000000000000000000 : ℝ)*base71 + (4033744103573/2960000000000000000000000000 : ℝ)*base74 + (8884707342730403/2000000000000000000000000000000 : ℝ)*base76 + (3615076014730403/2000000000000000000000000000000 : ℝ)*base78 + (1907360782730403/2000000000000000000000000000000 : ℝ)*base80 + (4446960586987/2960000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (6322709/1000000000000000000000 : ℝ)*base89 + (6322709/1000000000000000000000 : ℝ)*base91 + (6322709/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1633_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4101/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2621/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1057/10000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1633_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1633_s4_0 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1648068063/10000000000 : ℝ)*x 0 + (1090484137/2000000000 : ℝ)*x 1 + (2591425523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1648068063/10000000000 : ℝ)^4851 ≤ (5086619135749/50000000000000 : ℝ)^3827 := by
    have hnat : (1648068063 : ℕ)^4851*50000000000000^3827 ≤ 5086619135749^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1648068063 10000000000 5086619135749 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090484137/2000000000 : ℝ)^4851 ≤ (9271241740401/20000000000000 : ℝ)^3827 := by
    have hnat : (1090484137 : ℕ)^4851*20000000000000^3827 ≤ 9271241740401^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090484137 2000000000 9271241740401 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591425523/5000000000 : ℝ)^4851 ≤ (43470553016091/100000000000000 : ℝ)^3827 := by
    have hnat : (2591425523 : ℕ)^4851*100000000000000^3827 ≤ 43470553016091^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591425523 5000000000 43470553016091 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1648068063/10000000000 : ℝ), (1090484137/2000000000 : ℝ), (2591425523/5000000000 : ℝ)] ![(5086619135749/50000000000000 : ℝ), (9271241740401/20000000000000 : ℝ), (43470553016091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1648068063/10000000000 : ℝ)|^4851 ≤ (5086619135749/50000000000000 : ℝ)^3827
        have hw : |(-1648068063/10000000000 : ℝ)|=(1648068063/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090484137/2000000000 : ℝ)|^4851 ≤ (9271241740401/20000000000000 : ℝ)^3827
        have hw : |(1090484137/2000000000 : ℝ)|=(1090484137/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591425523/5000000000 : ℝ)|^4851 ≤ (43470553016091/100000000000000 : ℝ)^3827
        have hw : |(2591425523/5000000000 : ℝ)|=(2591425523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s4_1 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350227987/10000000000 : ℝ)*x 0 + (-357386231/2000000000 : ℝ)*x 1 + (2591425523/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350227987/10000000000 : ℝ)^4851 ≤ (1131441720403/2500000000000 : ℝ)^3827 := by
    have hnat : (5350227987 : ℕ)^4851*2500000000000^3827 ≤ 1131441720403^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350227987 10000000000 1131441720403 2500000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (357386231/2000000000 : ℝ)^4851 ≤ (11271778147791/100000000000000 : ℝ)^3827 := by
    have hnat : (357386231 : ℕ)^4851*100000000000000^3827 ≤ 11271778147791^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357386231 2000000000 11271778147791 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2591425523/5000000000 : ℝ)^4851 ≤ (43470553016091/100000000000000 : ℝ)^3827 := by
    have hnat : (2591425523 : ℕ)^4851*100000000000000^3827 ≤ 43470553016091^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591425523 5000000000 43470553016091 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350227987/10000000000 : ℝ), (-357386231/2000000000 : ℝ), (2591425523/5000000000 : ℝ)] ![(1131441720403/2500000000000 : ℝ), (11271778147791/100000000000000 : ℝ), (43470553016091/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350227987/10000000000 : ℝ)|^4851 ≤ (1131441720403/2500000000000 : ℝ)^3827
        have hw : |(5350227987/10000000000 : ℝ)|=(5350227987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-357386231/2000000000 : ℝ)|^4851 ≤ (11271778147791/100000000000000 : ℝ)^3827
        have hw : |(-357386231/2000000000 : ℝ)|=(357386231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2591425523/5000000000 : ℝ)|^4851 ≤ (43470553016091/100000000000000 : ℝ)^3827
        have hw : |(2591425523/5000000000 : ℝ)|=(2591425523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s4_2 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5350227987/10000000000 : ℝ)*x 0 + (2591425523/5000000000 : ℝ)*x 1 + (-357386231/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5350227987/10000000000 : ℝ)^4851 ≤ (1131441720403/2500000000000 : ℝ)^3827 := by
    have hnat : (5350227987 : ℕ)^4851*2500000000000^3827 ≤ 1131441720403^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5350227987 10000000000 1131441720403 2500000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591425523/5000000000 : ℝ)^4851 ≤ (43470553016091/100000000000000 : ℝ)^3827 := by
    have hnat : (2591425523 : ℕ)^4851*100000000000000^3827 ≤ 43470553016091^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591425523 5000000000 43470553016091 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (357386231/2000000000 : ℝ)^4851 ≤ (11271778147791/100000000000000 : ℝ)^3827 := by
    have hnat : (357386231 : ℕ)^4851*100000000000000^3827 ≤ 11271778147791^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      357386231 2000000000 11271778147791 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5350227987/10000000000 : ℝ), (2591425523/5000000000 : ℝ), (-357386231/2000000000 : ℝ)] ![(1131441720403/2500000000000 : ℝ), (43470553016091/100000000000000 : ℝ), (11271778147791/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5350227987/10000000000 : ℝ)|^4851 ≤ (1131441720403/2500000000000 : ℝ)^3827
        have hw : |(5350227987/10000000000 : ℝ)|=(5350227987/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591425523/5000000000 : ℝ)|^4851 ≤ (43470553016091/100000000000000 : ℝ)^3827
        have hw : |(2591425523/5000000000 : ℝ)|=(2591425523/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-357386231/2000000000 : ℝ)|^4851 ≤ (11271778147791/100000000000000 : ℝ)^3827
        have hw : |(-357386231/2000000000 : ℝ)|=(357386231/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s4_3 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4193982493/10000000000 : ℝ)*x 0 + (386304347/1000000000 : ℝ)*x 1 + (181822931/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193982493/10000000000 : ℝ)^4851 ≤ (33239299947307/100000000000000 : ℝ)^3827 := by
    have hnat : (4193982493 : ℕ)^4851*100000000000000^3827 ≤ 33239299947307^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193982493 10000000000 33239299947307 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (386304347/1000000000 : ℝ)^4851 ≤ (7487611771557/25000000000000 : ℝ)^3827 := by
    have hnat : (386304347 : ℕ)^4851*25000000000000^3827 ≤ 7487611771557^3827*1000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      386304347 1000000000 7487611771557 25000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (181822931/400000000 : ℝ)^4851 ≤ (36810252945059/100000000000000 : ℝ)^3827 := by
    have hnat : (181822931 : ℕ)^4851*100000000000000^3827 ≤ 36810252945059^3827*400000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      181822931 400000000 36810252945059 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193982493/10000000000 : ℝ), (386304347/1000000000 : ℝ), (181822931/400000000 : ℝ)] ![(33239299947307/100000000000000 : ℝ), (7487611771557/25000000000000 : ℝ), (36810252945059/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193982493/10000000000 : ℝ)|^4851 ≤ (33239299947307/100000000000000 : ℝ)^3827
        have hw : |(4193982493/10000000000 : ℝ)|=(4193982493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(386304347/1000000000 : ℝ)|^4851 ≤ (7487611771557/25000000000000 : ℝ)^3827
        have hw : |(386304347/1000000000 : ℝ)|=(386304347/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(181822931/400000000 : ℝ)|^4851 ≤ (36810252945059/100000000000000 : ℝ)^3827
        have hw : |(181822931/400000000 : ℝ)|=(181822931/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s4_4 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1648134611/10000000000 : ℝ)*x 0 + (2592436967/5000000000 : ℝ)*x 1 + (1362594133/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1648134611/10000000000 : ℝ)^4851 ≤ (2034751795897/20000000000000 : ℝ)^3827 := by
    have hnat : (1648134611 : ℕ)^4851*20000000000000^3827 ≤ 2034751795897^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1648134611 10000000000 2034751795897 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2592436967/5000000000 : ℝ)^4851 ≤ (21746030352921/50000000000000 : ℝ)^3827 := by
    have hnat : (2592436967 : ℕ)^4851*50000000000000^3827 ≤ 21746030352921^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2592436967 5000000000 21746030352921 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362594133/2500000000 : ℝ)^4851 ≤ (23167090150391/50000000000000 : ℝ)^3827 := by
    have hnat : (1362594133 : ℕ)^4851*50000000000000^3827 ≤ 23167090150391^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362594133 2500000000 23167090150391 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1648134611/10000000000 : ℝ), (2592436967/5000000000 : ℝ), (1362594133/2500000000 : ℝ)] ![(2034751795897/20000000000000 : ℝ), (21746030352921/50000000000000 : ℝ), (23167090150391/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1648134611/10000000000 : ℝ)|^4851 ≤ (2034751795897/20000000000000 : ℝ)^3827
        have hw : |(-1648134611/10000000000 : ℝ)|=(1648134611/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2592436967/5000000000 : ℝ)|^4851 ≤ (21746030352921/50000000000000 : ℝ)^3827
        have hw : |(2592436967/5000000000 : ℝ)|=(2592436967/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362594133/2500000000 : ℝ)|^4851 ≤ (23167090150391/50000000000000 : ℝ)^3827
        have hw : |(1362594133/2500000000 : ℝ)|=(1362594133/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s4_5 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278371121/10000000000 : ℝ)*x 0 + (-189925701/1250000000 : ℝ)*x 1 + (1362594151/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278371121/10000000000 : ℝ)^4851 ≤ (44488578503923/100000000000000 : ℝ)^3827 := by
    have hnat : (5278371121 : ℕ)^4851*100000000000000^3827 ≤ 44488578503923^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278371121 10000000000 44488578503923 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (189925701/1250000000 : ℝ)^4851 ≤ (9177240408757/100000000000000 : ℝ)^3827 := by
    have hnat : (189925701 : ℕ)^4851*100000000000000^3827 ≤ 9177240408757^3827*1250000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      189925701 1250000000 9177240408757 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1362594151/2500000000 : ℝ)^4851 ≤ (11583545269159/25000000000000 : ℝ)^3827 := by
    have hnat : (1362594151 : ℕ)^4851*25000000000000^3827 ≤ 11583545269159^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1362594151 2500000000 11583545269159 25000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278371121/10000000000 : ℝ), (-189925701/1250000000 : ℝ), (1362594151/2500000000 : ℝ)] ![(44488578503923/100000000000000 : ℝ), (9177240408757/100000000000000 : ℝ), (11583545269159/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278371121/10000000000 : ℝ)|^4851 ≤ (44488578503923/100000000000000 : ℝ)^3827
        have hw : |(5278371121/10000000000 : ℝ)|=(5278371121/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-189925701/1250000000 : ℝ)|^4851 ≤ (9177240408757/100000000000000 : ℝ)^3827
        have hw : |(-189925701/1250000000 : ℝ)|=(189925701/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1362594151/2500000000 : ℝ)|^4851 ≤ (11583545269159/25000000000000 : ℝ)^3827
        have hw : |(1362594151/2500000000 : ℝ)|=(1362594151/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s4_6 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278371177/10000000000 : ℝ)*x 0 + (5450376517/10000000000 : ℝ)*x 1 + (-379851413/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278371177/10000000000 : ℝ)^4851 ≤ (4448857910221/10000000000000 : ℝ)^3827 := by
    have hnat : (5278371177 : ℕ)^4851*10000000000000^3827 ≤ 4448857910221^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278371177 10000000000 4448857910221 10000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5450376517/10000000000 : ℝ)^4851 ≤ (23167090069573/50000000000000 : ℝ)^3827 := by
    have hnat : (5450376517 : ℕ)^4851*50000000000000^3827 ≤ 23167090069573^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450376517 10000000000 23167090069573 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (379851413/2500000000 : ℝ)^4851 ≤ (2294310186407/25000000000000 : ℝ)^3827 := by
    have hnat : (379851413 : ℕ)^4851*25000000000000^3827 ≤ 2294310186407^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      379851413 2500000000 2294310186407 25000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278371177/10000000000 : ℝ), (5450376517/10000000000 : ℝ), (-379851413/2500000000 : ℝ)] ![(4448857910221/10000000000000 : ℝ), (23167090069573/50000000000000 : ℝ), (2294310186407/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278371177/10000000000 : ℝ)|^4851 ≤ (4448857910221/10000000000000 : ℝ)^3827
        have hw : |(5278371177/10000000000 : ℝ)|=(5278371177/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5450376517/10000000000 : ℝ)|^4851 ≤ (23167090069573/50000000000000 : ℝ)^3827
        have hw : |(5450376517/10000000000 : ℝ)|=(5450376517/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-379851413/2500000000 : ℝ)|^4851 ≤ (2294310186407/25000000000000 : ℝ)^3827
        have hw : |(-379851413/2500000000 : ℝ)|=(379851413/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s4_7 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (838830209/2000000000 : ℝ)*x 0 + (4540451559/10000000000 : ℝ)*x 1 + (3868219043/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838830209/2000000000 : ℝ)^4851 ≤ (6648198649777/20000000000000 : ℝ)^3827 := by
    have hnat : (838830209 : ℕ)^4851*20000000000000^3827 ≤ 6648198649777^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838830209 2000000000 6648198649777 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4540451559/10000000000 : ℝ)^4851 ≤ (18378843592143/50000000000000 : ℝ)^3827 := by
    have hnat : (4540451559 : ℕ)^4851*50000000000000^3827 ≤ 18378843592143^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540451559 10000000000 18378843592143 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3868219043/10000000000 : ℝ)^4851 ≤ (750032988767/2500000000000 : ℝ)^3827 := by
    have hnat : (3868219043 : ℕ)^4851*2500000000000^3827 ≤ 750032988767^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3868219043 10000000000 750032988767 2500000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838830209/2000000000 : ℝ), (4540451559/10000000000 : ℝ), (3868219043/10000000000 : ℝ)] ![(6648198649777/20000000000000 : ℝ), (18378843592143/50000000000000 : ℝ), (750032988767/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838830209/2000000000 : ℝ)|^4851 ≤ (6648198649777/20000000000000 : ℝ)^3827
        have hw : |(838830209/2000000000 : ℝ)|=(838830209/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4540451559/10000000000 : ℝ)|^4851 ≤ (18378843592143/50000000000000 : ℝ)^3827
        have hw : |(4540451559/10000000000 : ℝ)|=(4540451559/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3868219043/10000000000 : ℝ)|^4851 ≤ (750032988767/2500000000000 : ℝ)^3827
        have hw : |(3868219043/10000000000 : ℝ)|=(3868219043/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1633_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1057/10000 : ℝ)*pair X i i ≤ pair X i h) :
    (10577/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16301/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4077/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1057/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4077/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1057/10000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4077/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1057/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4077/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1057/10000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4077/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1057/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4077/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1057/10000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1057/10000 : ℝ) ^ (4847/1024 : ℝ) ≤ (1200958704194117/50000000000000000000 : ℝ) := by
    have hpowers : (1057/10000 : ℝ)^4847 ≤ (1200958704194117/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1057 : ℕ)^4847*50000000000000000000^1024 ≤ 1200958704194117^1024*10000^4847 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1057 10000 1200958704194117 50000000000000000000 4847 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1057/10000 : ℝ)) (X := (1200958704194117/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4077/25000 : ℝ) ^ (4847/1024 : ℝ) ≤ (9352952344094639/50000000000000000000 : ℝ) := by
    have hpowers : (4077/25000 : ℝ)^4847 ≤ (9352952344094639/50000000000000000000 : ℝ)^1024 := by
      have hnat : (4077 : ℕ)^4847*50000000000000000000^1024 ≤ 9352952344094639^1024*25000^4847 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4077 25000 9352952344094639 50000000000000000000 4847 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4077/25000 : ℝ)) (X := (9352952344094639/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001200958704194117/25000000000000000000 : ℝ) ≤ (31250317144217/31250000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (25001200958704194117/25000000000000000000 : ℝ)^1024 ≤ (31250317144217/31250000000000 : ℝ)^4847 := by
      have hnat : (25001200958704194117 : ℕ)^1024*31250000000000^4847 ≤ 31250317144217^4847*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001200958704194117 25000000000000000000 31250317144217 31250000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (31250317144217/31250000000000 : ℝ)) (X := (25001200958704194117/25000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (12502638477762072189/12500000000000000000 : ℝ) ≤ (10000445896653961/10000000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (12502638477762072189/12500000000000000000 : ℝ)^1024 ≤ (10000445896653961/10000000000000000 : ℝ)^4847 := by
      have hnat : (12502638477762072189 : ℕ)^1024*10000000000000000^4847 ≤ 10000445896653961^4847*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12502638477762072189 12500000000000000000 10000445896653961 10000000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000445896653961/10000000000000000 : ℝ)) (X := (12502638477762072189/12500000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (25009352952344094639/25000000000000000000 : ℝ) ≤ (5000395153579241/5000000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (25009352952344094639/25000000000000000000 : ℝ)^1024 ≤ (5000395153579241/5000000000000000 : ℝ)^4847 := by
      have hnat : (25009352952344094639 : ℕ)^1024*5000000000000000^4847 ≤ 5000395153579241^4847*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25009352952344094639 25000000000000000000 5000395153579241 5000000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5000395153579241/5000000000000000 : ℝ)) (X := (25009352952344094639/25000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1200958704194117/50000000000000000000 : ℝ) ≤ ((999883260534331/1000000000000000 : ℝ)+2*(18126868659/30200000000000 : ℝ)*(1057/10000 : ℝ))^(4847/1024 : ℝ) := by
    rw [show (999883260534331/1000000000000000 : ℝ)+2*(18126868659/30200000000000 : ℝ)*(1057/10000 : ℝ)=(31250317144217/31250000000000 : ℝ) by norm_num, show 1+2*(1200958704194117/50000000000000000000 : ℝ)=(25001200958704194117/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9352952344094639/50000000000000000000 : ℝ)+(1200958704194117/50000000000000000000 : ℝ) ≤ ((999883260534331/1000000000000000 : ℝ)+(18126868659/30200000000000 : ℝ)*((4077/25000 : ℝ)+(1057/10000 : ℝ)))^(4847/1024 : ℝ) := by
    rw [show (999883260534331/1000000000000000 : ℝ)+(18126868659/30200000000000 : ℝ)*((4077/25000 : ℝ)+(1057/10000 : ℝ))=(10000445896653961/10000000000000000 : ℝ) by norm_num, show 1+(9352952344094639/50000000000000000000 : ℝ)+(1200958704194117/50000000000000000000 : ℝ)=(12502638477762072189/12500000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9352952344094639/50000000000000000000 : ℝ) ≤ ((999883260534331/1000000000000000 : ℝ)+2*(18126868659/30200000000000 : ℝ)*(4077/25000 : ℝ))^(4847/1024 : ℝ) := by
    rw [show (999883260534331/1000000000000000 : ℝ)+2*(18126868659/30200000000000 : ℝ)*(4077/25000 : ℝ)=(5000395153579241/5000000000000000 : ℝ) by norm_num, show 1+2*(9352952344094639/50000000000000000000 : ℝ)=(25009352952344094639/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (999883260534331/1000000000000000 : ℝ)*(X 1 0+X 2 0)+(18126868659/30200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (1057/10000 : ℝ)) (hi := (4077/25000 : ℝ)) (c := (999883260534331/1000000000000000 : ℝ)) (alpha := (18126868659/30200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (999883260534331/1000000000000000 : ℝ)*(X 0 1+X 2 1)+(18126868659/30200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (1057/10000 : ℝ)) (hi := (4077/25000 : ℝ)) (c := (999883260534331/1000000000000000 : ℝ)) (alpha := (18126868659/30200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (999883260534331/1000000000000000 : ℝ)*(X 0 2+X 1 2)+(18126868659/30200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (1057/10000 : ℝ)) (hi := (4077/25000 : ℝ)) (c := (999883260534331/1000000000000000 : ℝ)) (alpha := (18126868659/30200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1648068063/10000000000 : ℝ)*X 0 0+(1090484137/2000000000 : ℝ)*X 0 1+(2591425523/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5350227987/10000000000 : ℝ)*X 1 0+(-357386231/2000000000 : ℝ)*X 1 1+(2591425523/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5350227987/10000000000 : ℝ)*X 2 0+(2591425523/5000000000 : ℝ)*X 2 1+(-357386231/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4193982493/10000000000 : ℝ)*X 0 0+(386304347/1000000000 : ℝ)*X 0 1+(181822931/400000000 : ℝ)*X 0 2+(4193982493/10000000000 : ℝ)*X 1 0+(386304347/1000000000 : ℝ)*X 1 1+(181822931/400000000 : ℝ)*X 1 2+(4193982493/10000000000 : ℝ)*X 2 0+(386304347/1000000000 : ℝ)*X 2 1+(181822931/400000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1648134611/10000000000 : ℝ)*X 0 0+(2592436967/5000000000 : ℝ)*X 0 1+(1362594133/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278371121/10000000000 : ℝ)*X 1 0+(-189925701/1250000000 : ℝ)*X 1 1+(1362594151/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278371177/10000000000 : ℝ)*X 2 0+(5450376517/10000000000 : ℝ)*X 2 1+(-379851413/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((838830209/2000000000 : ℝ)*X 0 0+(4540451559/10000000000 : ℝ)*X 0 1+(3868219043/10000000000 : ℝ)*X 0 2+(838830209/2000000000 : ℝ)*X 1 0+(4540451559/10000000000 : ℝ)*X 1 1+(3868219043/10000000000 : ℝ)*X 1 2+(838830209/2000000000 : ℝ)*X 2 0+(4540451559/10000000000 : ℝ)*X 2 1+(3868219043/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11089623898243107136134849/1887500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (474108533/50000000000000 : ℝ)*(base19) + (55507961/6250000000000 : ℝ)*(base23) + (16074677/50000000000000 : ℝ)*(lower2) + (36098617/25000000000000 : ℝ)*(upper3) + (101038441/100000000000000 : ℝ)*(upper5) + (1293696847193357/50000000000000 : ℝ)*(major0) + (1293696847193357/50000000000000 : ℝ)*(major1) + (1293696847193357/50000000000000 : ℝ)*(major2) + (3709628606347683/100000000000000 : ℝ)*(sp0) + (927409833654687/25000000000000 : ℝ)*(sp1) + (1854819697354219/50000000000000 : ℝ)*(sp2) + (1465141919531007/100000000000000 : ℝ)*(sp3) + (11676488131/100000000000000 : ℝ)*(sp4) + (998112671/20000000000000 : ℝ)*(sp7) + (732573455047181/50000000000000 : ℝ)*(f.failure) + (1854820141417907/50000000000000 : ℝ)*(f.sum) + (2759645800517/755000000000000000000000000 : ℝ)*base66 + (45496965203629217/7550000000000000000000000000000 : ℝ)*base67 + (110082833515829217/7550000000000000000000000000000 : ℝ)*base69 + (2640735930729217/7550000000000000000000000000000 : ℝ)*base71 + (293051150981/377500000000000000000000000 : ℝ)*base74 + (67592624165929217/7550000000000000000000000000000 : ℝ)*base75 + (6178826995770783/7550000000000000000000000000000 : ℝ)*base78 + (10917769364179217/7550000000000000000000000000000 : ℝ)*base79 + (3676008216763/755000000000000000000000000 : ℝ)*base81 + (2015259/1000000000000000000000 : ℝ)*base89 + (2015259/1000000000000000000000 : ℝ)*base91 + (2015259/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (10040795470848853147881/755000000000000000000000000 : ℝ) := by norm_num
    linear_combination (984612887/50000000000000 : ℝ)*(base19) + (546721599/25000000000000 : ℝ)*(base23) + (127423421/20000000000000 : ℝ)*(lower1) + (285924651/100000000000000 : ℝ)*(upper3) + (81484519/100000000000000 : ℝ)*(lower4) + (3312131/1250000000000 : ℝ)*(upper5) + (1313496824828563/50000000000000 : ℝ)*(major0) + (1313496824828563/50000000000000 : ℝ)*(major1) + (1313496824828563/50000000000000 : ℝ)*(major2) + (1713535757/100000000000000 : ℝ)*(sp2) + (941603983010537/25000000000000 : ℝ)*(sp4) + (1883206981408187/50000000000000 : ℝ)*(sp5) + (753282406323999/20000000000000 : ℝ)*(sp6) + (743785461984933/50000000000000 : ℝ)*(sp7) + (743785461984933/50000000000000 : ℝ)*(f.failure) + (941603983010537/25000000000000 : ℝ)*(f.sum) + (3115440577193/755000000000000000000000000 : ℝ)*base66 + (83842955490865697/7550000000000000000000000000000 : ℝ)*base68 + (47074515266734303/7550000000000000000000000000000 : ℝ)*base69 + (224858017579234303/7550000000000000000000000000000 : ℝ)*base71 + (345426452007/755000000000000000000000000 : ℝ)*base73 + (258727990591265697/7550000000000000000000000000000 : ℝ)*base76 + (14507031571765697/7550000000000000000000000000000 : ℝ)*base78 + (35545655021384303/7550000000000000000000000000000 : ℝ)*base79 + (135326481381/94375000000000000000000000 : ℝ)*base82 + (3025987/1000000000000000000000 : ℝ)*base89 + (3025987/1000000000000000000000 : ℝ)*base91 + (3025987/1000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1633_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4077/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1057/10000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10577/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16301/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1633_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1633_s5_0 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1337555543/2500000000 : ℝ)*x 0 + (2591438129/5000000000 : ℝ)*x 1 + (-1786905429/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1337555543/2500000000 : ℝ)^4851 ≤ (45257606465273/100000000000000 : ℝ)^3827 := by
    have hnat : (1337555543 : ℕ)^4851*100000000000000^3827 ≤ 45257606465273^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1337555543 2500000000 45257606465273 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2591438129/5000000000 : ℝ)^4851 ≤ (43470821060549/100000000000000 : ℝ)^3827 := by
    have hnat : (2591438129 : ℕ)^4851*100000000000000^3827 ≤ 43470821060549^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2591438129 5000000000 43470821060549 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1786905429/10000000000 : ℝ)^4851 ≤ (11271572450367/100000000000000 : ℝ)^3827 := by
    have hnat : (1786905429 : ℕ)^4851*100000000000000^3827 ≤ 11271572450367^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1786905429 10000000000 11271572450367 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1337555543/2500000000 : ℝ), (2591438129/5000000000 : ℝ), (-1786905429/10000000000 : ℝ)] ![(45257606465273/100000000000000 : ℝ), (43470821060549/100000000000000 : ℝ), (11271572450367/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1337555543/2500000000 : ℝ)|^4851 ≤ (45257606465273/100000000000000 : ℝ)^3827
        have hw : |(1337555543/2500000000 : ℝ)|=(1337555543/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2591438129/5000000000 : ℝ)|^4851 ≤ (43470821060549/100000000000000 : ℝ)^3827
        have hw : |(2591438129/5000000000 : ℝ)|=(2591438129/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1786905429/10000000000 : ℝ)|^4851 ≤ (11271572450367/100000000000000 : ℝ)^3827
        have hw : |(-1786905429/10000000000 : ℝ)|=(1786905429/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s5_1 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4193976879/10000000000 : ℝ)*x 0 + (482887799/1250000000 : ℝ)*x 1 + (4545522359/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4193976879/10000000000 : ℝ)^4851 ≤ (16619621774219/50000000000000 : ℝ)^3827 := by
    have hnat : (4193976879 : ℕ)^4851*50000000000000^3827 ≤ 16619621774219^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4193976879 10000000000 16619621774219 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (482887799/1250000000 : ℝ)^4851 ≤ (29951026147997/100000000000000 : ℝ)^3827 := by
    have hnat : (482887799 : ℕ)^4851*100000000000000^3827 ≤ 29951026147997^3827*1250000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      482887799 1250000000 29951026147997 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4545522359/10000000000 : ℝ)^4851 ≤ (18404865150163/50000000000000 : ℝ)^3827 := by
    have hnat : (4545522359 : ℕ)^4851*50000000000000^3827 ≤ 18404865150163^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4545522359 10000000000 18404865150163 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4193976879/10000000000 : ℝ), (482887799/1250000000 : ℝ), (4545522359/10000000000 : ℝ)] ![(16619621774219/50000000000000 : ℝ), (29951026147997/100000000000000 : ℝ), (18404865150163/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4193976879/10000000000 : ℝ)|^4851 ≤ (16619621774219/50000000000000 : ℝ)^3827
        have hw : |(4193976879/10000000000 : ℝ)|=(4193976879/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(482887799/1250000000 : ℝ)|^4851 ≤ (29951026147997/100000000000000 : ℝ)^3827
        have hw : |(482887799/1250000000 : ℝ)|=(482887799/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4545522359/10000000000 : ℝ)|^4851 ≤ (18404865150163/50000000000000 : ℝ)^3827
        have hw : |(4545522359/10000000000 : ℝ)|=(4545522359/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s5_2 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-412034593/2500000000 : ℝ)*x 0 + (648112117/1250000000 : ℝ)*x 1 + (10645217/19531250 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (412034593/2500000000 : ℝ)^4851 ≤ (317930887743/3125000000000 : ℝ)^3827 := by
    have hnat : (412034593 : ℕ)^4851*3125000000000^3827 ≤ 317930887743^3827*2500000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      412034593 2500000000 317930887743 3125000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (648112117/1250000000 : ℝ)^4851 ≤ (679567269999/1562500000000 : ℝ)^3827 := by
    have hnat : (648112117 : ℕ)^4851*1562500000000^3827 ≤ 679567269999^3827*1250000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      648112117 1250000000 679567269999 1562500000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (10645217/19531250 : ℝ)^4851 ≤ (46333906295003/100000000000000 : ℝ)^3827 := by
    have hnat : (10645217 : ℕ)^4851*100000000000000^3827 ≤ 46333906295003^3827*19531250^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      10645217 19531250 46333906295003 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-412034593/2500000000 : ℝ), (648112117/1250000000 : ℝ), (10645217/19531250 : ℝ)] ![(317930887743/3125000000000 : ℝ), (679567269999/1562500000000 : ℝ), (46333906295003/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-412034593/2500000000 : ℝ)|^4851 ≤ (317930887743/3125000000000 : ℝ)^3827
        have hw : |(-412034593/2500000000 : ℝ)|=(412034593/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(648112117/1250000000 : ℝ)|^4851 ≤ (679567269999/1562500000000 : ℝ)^3827
        have hw : |(648112117/1250000000 : ℝ)|=(648112117/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(10645217/19531250 : ℝ)|^4851 ≤ (46333906295003/100000000000000 : ℝ)^3827
        have hw : |(10645217/19531250 : ℝ)|=(10645217/19531250 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s5_3 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278377851/10000000000 : ℝ)*x 0 + (-151943141/1000000000 : ℝ)*x 1 + (5450351599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278377851/10000000000 : ℝ)^4851 ≤ (44488650405193/100000000000000 : ℝ)^3827 := by
    have hnat : (5278377851 : ℕ)^4851*100000000000000^3827 ≤ 44488650405193^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278377851 10000000000 44488650405193 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (151943141/1000000000 : ℝ)^4851 ≤ (1835487590707/20000000000000 : ℝ)^3827 := by
    have hnat : (151943141 : ℕ)^4851*20000000000000^3827 ≤ 1835487590707^3827*1000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      151943141 1000000000 1835487590707 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5450351599/10000000000 : ℝ)^4851 ≤ (11583477907249/25000000000000 : ℝ)^3827 := by
    have hnat : (5450351599 : ℕ)^4851*25000000000000^3827 ≤ 11583477907249^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5450351599 10000000000 11583477907249 25000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278377851/10000000000 : ℝ), (-151943141/1000000000 : ℝ), (5450351599/10000000000 : ℝ)] ![(44488650405193/100000000000000 : ℝ), (1835487590707/20000000000000 : ℝ), (11583477907249/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278377851/10000000000 : ℝ)|^4851 ≤ (44488650405193/100000000000000 : ℝ)^3827
        have hw : |(5278377851/10000000000 : ℝ)|=(5278377851/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-151943141/1000000000 : ℝ)|^4851 ≤ (1835487590707/20000000000000 : ℝ)^3827
        have hw : |(-151943141/1000000000 : ℝ)|=(151943141/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5450351599/10000000000 : ℝ)|^4851 ≤ (11583477907249/25000000000000 : ℝ)^3827
        have hw : |(5450351599/10000000000 : ℝ)|=(5450351599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s5_4 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2639189049/5000000000 : ℝ)*x 0 + (1090070303/2000000000 : ℝ)*x 1 + (-1519431183/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2639189049/5000000000 : ℝ)^4851 ≤ (22244326522033/50000000000000 : ℝ)^3827 := by
    have hnat : (2639189049 : ℕ)^4851*50000000000000^3827 ≤ 22244326522033^3827*5000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2639189049 5000000000 22244326522033 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1090070303/2000000000 : ℝ)^4851 ≤ (23166955361917/50000000000000 : ℝ)^3827 := by
    have hnat : (1090070303 : ℕ)^4851*50000000000000^3827 ≤ 23166955361917^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1090070303 2000000000 23166955361917 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1519431183/10000000000 : ℝ)^4851 ≤ (4588718107789/50000000000000 : ℝ)^3827 := by
    have hnat : (1519431183 : ℕ)^4851*50000000000000^3827 ≤ 4588718107789^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519431183 10000000000 4588718107789 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2639189049/5000000000 : ℝ), (1090070303/2000000000 : ℝ), (-1519431183/10000000000 : ℝ)] ![(22244326522033/50000000000000 : ℝ), (23166955361917/50000000000000 : ℝ), (4588718107789/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2639189049/5000000000 : ℝ)|^4851 ≤ (22244326522033/50000000000000 : ℝ)^3827
        have hw : |(2639189049/5000000000 : ℝ)|=(2639189049/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1090070303/2000000000 : ℝ)|^4851 ≤ (23166955361917/50000000000000 : ℝ)^3827
        have hw : |(1090070303/2000000000 : ℝ)|=(1090070303/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1519431183/10000000000 : ℝ)|^4851 ≤ (4588718107789/50000000000000 : ℝ)^3827
        have hw : |(-1519431183/10000000000 : ℝ)|=(1519431183/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1633_s5_5 (p : ℝ) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (838830929/2000000000 : ℝ)*x 0 + (4540393467/10000000000 : ℝ)*x 1 + (967069/2500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (838830929/2000000000 : ℝ)^4851 ≤ (6648205883057/20000000000000 : ℝ)^3827 := by
    have hnat : (838830929 : ℕ)^4851*20000000000000^3827 ≤ 6648205883057^3827*2000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      838830929 2000000000 6648205883057 20000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4540393467/10000000000 : ℝ)^4851 ≤ (36757091059021/100000000000000 : ℝ)^3827 := by
    have hnat : (4540393467 : ℕ)^4851*100000000000000^3827 ≤ 36757091059021^3827*10000000000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4540393467 10000000000 36757091059021 100000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (967069/2500000 : ℝ)^4851 ≤ (15000939750871/50000000000000 : ℝ)^3827 := by
    have hnat : (967069 : ℕ)^4851*50000000000000^3827 ≤ 15000939750871^3827*2500000^4851 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      967069 2500000 15000939750871 50000000000000 4851 3827 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4851/1024 : ℝ)) 4851 3827 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(838830929/2000000000 : ℝ), (4540393467/10000000000 : ℝ), (967069/2500000 : ℝ)] ![(6648205883057/20000000000000 : ℝ), (36757091059021/100000000000000 : ℝ), (15000939750871/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(838830929/2000000000 : ℝ)|^4851 ≤ (6648205883057/20000000000000 : ℝ)^3827
        have hw : |(838830929/2000000000 : ℝ)|=(838830929/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4540393467/10000000000 : ℝ)|^4851 ≤ (36757091059021/100000000000000 : ℝ)^3827
        have hw : |(4540393467/10000000000 : ℝ)|=(4540393467/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(967069/2500000 : ℝ)|^4851 ≤ (15000939750871/50000000000000 : ℝ)^3827
        have hw : |(967069/2500000 : ℝ)|=(967069/2500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1633_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16301/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10577/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (10577/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (163/1000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16301/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (10577/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16301/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (10577/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16301/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (10577/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16301/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (10577/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16301/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (10577/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16301/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (10577/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (10577/100000 : ℝ) ^ (4847/1024 : ℝ) ≤ (1204728007345109/50000000000000000000 : ℝ) := by
    have hpowers : (10577/100000 : ℝ)^4847 ≤ (1204728007345109/50000000000000000000 : ℝ)^1024 := by
      have hnat : (10577 : ℕ)^4847*50000000000000000000^1024 ≤ 1204728007345109^1024*100000^4847 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10577 100000 1204728007345109 50000000000000000000 4847 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (10577/100000 : ℝ)) (X := (1204728007345109/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (16301/100000 : ℝ) ^ (4847/1024 : ℝ) ≤ (18667929395238659/100000000000000000000 : ℝ) := by
    have hpowers : (16301/100000 : ℝ)^4847 ≤ (18667929395238659/100000000000000000000 : ℝ)^1024 := by
      have hnat : (16301 : ℕ)^4847*100000000000000000000^1024 ≤ 18667929395238659^1024*100000^4847 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16301 100000 18667929395238659 100000000000000000000 4847 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16301/100000 : ℝ)) (X := (18667929395238659/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25001204728007345109/25000000000000000000 : ℝ) ≤ (312503181395801/312500000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (25001204728007345109/25000000000000000000 : ℝ)^1024 ≤ (312503181395801/312500000000000 : ℝ)^4847 := by
      have hnat : (25001204728007345109 : ℕ)^1024*312500000000000^4847 ≤ 312503181395801^4847*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25001204728007345109 25000000000000000000 312503181395801 312500000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312503181395801/312500000000000 : ℝ)) (X := (25001204728007345109/25000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100021077385409928877/100000000000000000000 : ℝ) ≤ (1000044525374117/1000000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (100021077385409928877/100000000000000000000 : ℝ)^1024 ≤ (1000044525374117/1000000000000000 : ℝ)^4847 := by
      have hnat : (100021077385409928877 : ℕ)^1024*1000000000000000^4847 ≤ 1000044525374117^4847*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100021077385409928877 100000000000000000000 1000044525374117 1000000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000044525374117/1000000000000000 : ℝ)) (X := (100021077385409928877/100000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50018667929395238659/50000000000000000000 : ℝ) ≤ (2500197175704177/2500000000000000 : ℝ) ^ (4847/1024 : ℝ) := by
    have hpowers : (50018667929395238659/50000000000000000000 : ℝ)^1024 ≤ (2500197175704177/2500000000000000 : ℝ)^4847 := by
      have hnat : (50018667929395238659 : ℕ)^1024*2500000000000000^4847 ≤ 2500197175704177^4847*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50018667929395238659 50000000000000000000 2500197175704177 2500000000000000 1024 4847 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500197175704177/2500000000000000 : ℝ)) (X := (50018667929395238659/50000000000000000000 : ℝ)) (by norm_num) 4847 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1204728007345109/50000000000000000000 : ℝ) ≤ ((14308329352040536679/14310000000000000000 : ℝ)+2*(171724537769/286200000000000 : ℝ)*(10577/100000 : ℝ))^(4847/1024 : ℝ) := by
    rw [show (14308329352040536679/14310000000000000000 : ℝ)+2*(171724537769/286200000000000 : ℝ)*(10577/100000 : ℝ)=(312503181395801/312500000000000 : ℝ) by norm_num, show 1+2*(1204728007345109/50000000000000000000 : ℝ)=(25001204728007345109/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(18667929395238659/100000000000000000000 : ℝ)+(1204728007345109/50000000000000000000 : ℝ) ≤ ((14308329352040536679/14310000000000000000 : ℝ)+(171724537769/286200000000000 : ℝ)*((16301/100000 : ℝ)+(10577/100000 : ℝ)))^(4847/1024 : ℝ) := by
    rw [show (14308329352040536679/14310000000000000000 : ℝ)+(171724537769/286200000000000 : ℝ)*((16301/100000 : ℝ)+(10577/100000 : ℝ))=(1000044525374117/1000000000000000 : ℝ) by norm_num, show 1+(18667929395238659/100000000000000000000 : ℝ)+(1204728007345109/50000000000000000000 : ℝ)=(100021077385409928877/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(18667929395238659/100000000000000000000 : ℝ) ≤ ((14308329352040536679/14310000000000000000 : ℝ)+2*(171724537769/286200000000000 : ℝ)*(16301/100000 : ℝ))^(4847/1024 : ℝ) := by
    rw [show (14308329352040536679/14310000000000000000 : ℝ)+2*(171724537769/286200000000000 : ℝ)*(16301/100000 : ℝ)=(2500197175704177/2500000000000000 : ℝ) by norm_num, show 1+2*(18667929395238659/100000000000000000000 : ℝ)=(50018667929395238659/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14308329352040536679/14310000000000000000 : ℝ)*(X 1 0+X 2 0)+(171724537769/286200000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (10577/100000 : ℝ)) (hi := (16301/100000 : ℝ)) (c := (14308329352040536679/14310000000000000000 : ℝ)) (alpha := (171724537769/286200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14308329352040536679/14310000000000000000 : ℝ)*(X 0 1+X 2 1)+(171724537769/286200000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (10577/100000 : ℝ)) (hi := (16301/100000 : ℝ)) (c := (14308329352040536679/14310000000000000000 : ℝ)) (alpha := (171724537769/286200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14308329352040536679/14310000000000000000 : ℝ)*(X 0 2+X 1 2)+(171724537769/286200000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4847/1024 : ℝ)) (lo := (10577/100000 : ℝ)) (hi := (16301/100000 : ℝ)) (c := (14308329352040536679/14310000000000000000 : ℝ)) (alpha := (171724537769/286200000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((1337555543/2500000000 : ℝ)*X 2 0+(2591438129/5000000000 : ℝ)*X 2 1+(-1786905429/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s5_0 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((4193976879/10000000000 : ℝ)*X 0 0+(482887799/1250000000 : ℝ)*X 0 1+(4545522359/10000000000 : ℝ)*X 0 2+(4193976879/10000000000 : ℝ)*X 1 0+(482887799/1250000000 : ℝ)*X 1 1+(4545522359/10000000000 : ℝ)*X 1 2+(4193976879/10000000000 : ℝ)*X 2 0+(482887799/1250000000 : ℝ)*X 2 1+(4545522359/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s5_1 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((-412034593/2500000000 : ℝ)*X 0 0+(648112117/1250000000 : ℝ)*X 0 1+(10645217/19531250 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s5_2 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((5278377851/10000000000 : ℝ)*X 1 0+(-151943141/1000000000 : ℝ)*X 1 1+(5450351599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s5_3 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((2639189049/5000000000 : ℝ)*X 2 0+(1090070303/2000000000 : ℝ)*X 2 1+(-1519431183/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s5_4 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((838830929/2000000000 : ℝ)*X 0 0+(4540393467/10000000000 : ℝ)*X 0 1+(967069/2500000 : ℝ)*X 0 2+(838830929/2000000000 : ℝ)*X 1 0+(4540393467/10000000000 : ℝ)*X 1 1+(967069/2500000 : ℝ)*X 1 2+(838830929/2000000000 : ℝ)*X 2 0+(4540393467/10000000000 : ℝ)*X 2 1+(967069/2500000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1633_s5_5 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (0 : ℝ) := by norm_num
    linear_combination (1 : ℝ)*(lower0) + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (166307889248372141222404199/26500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (155694217/12500000000000 : ℝ)*(base19) + (527856347/25000000000000 : ℝ)*(base23) + (121072329/20000000000000 : ℝ)*(lower1) + (147792927/100000000000000 : ℝ)*(upper3) + (17090839/6250000000000 : ℝ)*(lower4) + (2627470135897929/100000000000000 : ℝ)*(major0) + (2627470135897929/100000000000000 : ℝ)*(major1) + (2627470135897929/100000000000000 : ℝ)*(major2) + (6301080179/50000000000000 : ℝ)*(sp0) + (175810519/2500000000000 : ℝ)*(sp1) + (3767099321811849/100000000000000 : ℝ)*(sp2) + (3767098076258113/100000000000000 : ℝ)*(sp3) + (3767084608226103/100000000000000 : ℝ)*(sp4) + (743916854185463/50000000000000 : ℝ)*(sp5) + (297568148158337/20000000000000 : ℝ)*(f.failure) + (3767099321811849/100000000000000 : ℝ)*(f.sum) + (269322988109/1590000000000000000000000000 : ℝ)*base65 + (330032335646715267/53000000000000000000000000000000 : ℝ)*base68 + (64294952476715267/53000000000000000000000000000000 : ℝ)*base70 + (127637427662284733/53000000000000000000000000000000 : ℝ)*base71 + (3492266496391/1590000000000000000000000000 : ℝ)*base74 + (469683546199715267/53000000000000000000000000000000 : ℝ)*base76 + (2128036981208715267/53000000000000000000000000000000 : ℝ)*base78 + (354357631868284733/53000000000000000000000000000000 : ℝ)*base79 + (9867348564179/1590000000000000000000000000 : ℝ)*base81 + (1654457/400000000000000000000 : ℝ)*base90 + (1654457/400000000000000000000 : ℝ)*base92 + (1654457/400000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1633_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16301/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (10577/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10577/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (163/1000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1633_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1633_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4101/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2621/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10577/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (163/1000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1633_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1633_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1633_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4847/1024 : ℝ) ≤ p) (hpb : p ≤ (4851/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (35319239/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4101/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2621/25000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (10577/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (163/1000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1633_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
