-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1597_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-29T00:38:22.4487+00:00
-- url     : https://prove2.me/submissions/a0703a86-0ef2-47c0-91f5-1a0338ac870c

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
theorem support_rectangle_w1597_s0_0 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-397599549/2500000000 : ℝ)*x 0 + (5854979167/10000000000 : ℝ)*x 1 + (976624831/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (397599549/2500000000 : ℝ)^4707 ≤ (4769437855101/50000000000000 : ℝ)^3683 := by
    have hnat : (397599549 : ℕ)^4707*50000000000000^3683 ≤ 4769437855101^3683*2500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      397599549 2500000000 4769437855101 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5854979167/10000000000 : ℝ)^4707 ≤ (50453285119097/100000000000000 : ℝ)^3683 := by
    have hnat : (5854979167 : ℕ)^4707*100000000000000^3683 ≤ 50453285119097^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5854979167 10000000000 50453285119097 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (976624831/2000000000 : ℝ)^4707 ≤ (40007839156837/100000000000000 : ℝ)^3683 := by
    have hnat : (976624831 : ℕ)^4707*100000000000000^3683 ≤ 40007839156837^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      976624831 2000000000 40007839156837 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-397599549/2500000000 : ℝ), (5854979167/10000000000 : ℝ), (976624831/2000000000 : ℝ)] ![(4769437855101/50000000000000 : ℝ), (50453285119097/100000000000000 : ℝ), (40007839156837/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-397599549/2500000000 : ℝ)|^4707 ≤ (4769437855101/50000000000000 : ℝ)^3683
        have hw : |(-397599549/2500000000 : ℝ)|=(397599549/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5854979167/10000000000 : ℝ)|^4707 ≤ (50453285119097/100000000000000 : ℝ)^3683
        have hw : |(5854979167/10000000000 : ℝ)|=(5854979167/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(976624831/2000000000 : ℝ)|^4707 ≤ (40007839156837/100000000000000 : ℝ)^3683
        have hw : |(976624831/2000000000 : ℝ)|=(976624831/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s0_1 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5459107073/10000000000 : ℝ)*x 0 + (-213008383/1000000000 : ℝ)*x 1 + (4883123921/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5459107073/10000000000 : ℝ)^4707 ≤ (23067601046871/50000000000000 : ℝ)^3683 := by
    have hnat : (5459107073 : ℕ)^4707*50000000000000^3683 ≤ 23067601046871^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5459107073 10000000000 23067601046871 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (213008383/1000000000 : ℝ)^4707 ≤ (13856961187203/100000000000000 : ℝ)^3683 := by
    have hnat : (213008383 : ℕ)^4707*100000000000000^3683 ≤ 13856961187203^3683*1000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      213008383 1000000000 13856961187203 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4883123921/10000000000 : ℝ)^4707 ≤ (40007836706613/100000000000000 : ℝ)^3683 := by
    have hnat : (4883123921 : ℕ)^4707*100000000000000^3683 ≤ 40007836706613^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4883123921 10000000000 40007836706613 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5459107073/10000000000 : ℝ), (-213008383/1000000000 : ℝ), (4883123921/10000000000 : ℝ)] ![(23067601046871/50000000000000 : ℝ), (13856961187203/100000000000000 : ℝ), (40007836706613/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5459107073/10000000000 : ℝ)|^4707 ≤ (23067601046871/50000000000000 : ℝ)^3683
        have hw : |(5459107073/10000000000 : ℝ)|=(5459107073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-213008383/1000000000 : ℝ)|^4707 ≤ (13856961187203/100000000000000 : ℝ)^3683
        have hw : |(-213008383/1000000000 : ℝ)|=(213008383/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4883123921/10000000000 : ℝ)|^4707 ≤ (40007836706613/100000000000000 : ℝ)^3683
        have hw : |(4883123921/10000000000 : ℝ)|=(4883123921/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s0_2 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2729553509/5000000000 : ℝ)*x 0 + (2441561963/5000000000 : ℝ)*x 1 + (-426016779/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2729553509/5000000000 : ℝ)^4707 ≤ (23067600749851/50000000000000 : ℝ)^3683 := by
    have hnat : (2729553509 : ℕ)^4707*50000000000000^3683 ≤ 23067600749851^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2729553509 5000000000 23067600749851 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2441561963/5000000000 : ℝ)^4707 ≤ (40007836758969/100000000000000 : ℝ)^3683 := by
    have hnat : (2441561963 : ℕ)^4707*100000000000000^3683 ≤ 40007836758969^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2441561963 5000000000 40007836758969 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (426016779/2000000000 : ℝ)^4707 ≤ (13856961727617/100000000000000 : ℝ)^3683 := by
    have hnat : (426016779 : ℕ)^4707*100000000000000^3683 ≤ 13856961727617^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      426016779 2000000000 13856961727617 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2729553509/5000000000 : ℝ), (2441561963/5000000000 : ℝ), (-426016779/2000000000 : ℝ)] ![(23067600749851/50000000000000 : ℝ), (40007836758969/100000000000000 : ℝ), (13856961727617/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2729553509/5000000000 : ℝ)|^4707 ≤ (23067600749851/50000000000000 : ℝ)^3683
        have hw : |(2729553509/5000000000 : ℝ)|=(2729553509/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2441561963/5000000000 : ℝ)|^4707 ≤ (40007836758969/100000000000000 : ℝ)^3683
        have hw : |(2441561963/5000000000 : ℝ)|=(2441561963/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-426016779/2000000000 : ℝ)|^4707 ≤ (13856961727617/100000000000000 : ℝ)^3683
        have hw : |(-426016779/2000000000 : ℝ)|=(426016779/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s0_3 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2058106813/5000000000 : ℝ)*x 0 + (1536190647/5000000000 : ℝ)*x 1 + (541973299/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2058106813/5000000000 : ℝ)^4707 ≤ (32159933003119/100000000000000 : ℝ)^3683 := by
    have hnat : (2058106813 : ℕ)^4707*100000000000000^3683 ≤ 32159933003119^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2058106813 5000000000 32159933003119 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1536190647/5000000000 : ℝ)^4707 ≤ (5532426692903/25000000000000 : ℝ)^3683 := by
    have hnat : (1536190647 : ℕ)^4707*25000000000000^3683 ≤ 5532426692903^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1536190647 5000000000 5532426692903 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (541973299/1000000000 : ℝ)^4707 ≤ (45710360219357/100000000000000 : ℝ)^3683 := by
    have hnat : (541973299 : ℕ)^4707*100000000000000^3683 ≤ 45710360219357^3683*1000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      541973299 1000000000 45710360219357 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2058106813/5000000000 : ℝ), (1536190647/5000000000 : ℝ), (541973299/1000000000 : ℝ)] ![(32159933003119/100000000000000 : ℝ), (5532426692903/25000000000000 : ℝ), (45710360219357/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2058106813/5000000000 : ℝ)|^4707 ≤ (32159933003119/100000000000000 : ℝ)^3683
        have hw : |(2058106813/5000000000 : ℝ)|=(2058106813/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1536190647/5000000000 : ℝ)|^4707 ≤ (5532426692903/25000000000000 : ℝ)^3683
        have hw : |(1536190647/5000000000 : ℝ)|=(1536190647/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(541973299/1000000000 : ℝ)|^4707 ≤ (45710360219357/100000000000000 : ℝ)^3683
        have hw : |(541973299/1000000000 : ℝ)|=(541973299/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s0_4 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1593373739/10000000000 : ℝ)*x 0 + (196314823/400000000 : ℝ)*x 1 + (2914673409/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1593373739/10000000000 : ℝ)^4707 ≤ (2390422578317/25000000000000 : ℝ)^3683 := by
    have hnat : (1593373739 : ℕ)^4707*25000000000000^3683 ≤ 2390422578317^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1593373739 10000000000 2390422578317 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (196314823/400000000 : ℝ)^4707 ≤ (4026714223367/10000000000000 : ℝ)^3683 := by
    have hnat : (196314823 : ℕ)^4707*10000000000000^3683 ≤ 4026714223367^3683*400000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196314823 400000000 4026714223367 10000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2914673409/5000000000 : ℝ)^4707 ≤ (10034233486823/20000000000000 : ℝ)^3683 := by
    have hnat : (2914673409 : ℕ)^4707*20000000000000^3683 ≤ 10034233486823^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2914673409 5000000000 10034233486823 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1593373739/10000000000 : ℝ), (196314823/400000000 : ℝ), (2914673409/5000000000 : ℝ)] ![(2390422578317/25000000000000 : ℝ), (4026714223367/10000000000000 : ℝ), (10034233486823/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1593373739/10000000000 : ℝ)|^4707 ≤ (2390422578317/25000000000000 : ℝ)^3683
        have hw : |(-1593373739/10000000000 : ℝ)|=(1593373739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(196314823/400000000 : ℝ)|^4707 ≤ (4026714223367/10000000000000 : ℝ)^3683
        have hw : |(196314823/400000000 : ℝ)|=(196314823/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2914673409/5000000000 : ℝ)|^4707 ≤ (10034233486823/20000000000000 : ℝ)^3683
        have hw : |(2914673409/5000000000 : ℝ)|=(2914673409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s0_5 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5193660589/10000000000 : ℝ)*x 0 + (-1183860549/10000000000 : ℝ)*x 1 + (1457336749/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5193660589/10000000000 : ℝ)^4707 ≤ (43287796732297/100000000000000 : ℝ)^3683 := by
    have hnat : (5193660589 : ℕ)^4707*100000000000000^3683 ≤ 43287796732297^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193660589 10000000000 43287796732297 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1183860549/10000000000 : ℝ)^4707 ≤ (1635258464931/25000000000000 : ℝ)^3683 := by
    have hnat : (1183860549 : ℕ)^4707*25000000000000^3683 ≤ 1635258464931^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183860549 10000000000 1635258464931 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1457336749/2500000000 : ℝ)^4707 ≤ (12542792348011/25000000000000 : ℝ)^3683 := by
    have hnat : (1457336749 : ℕ)^4707*25000000000000^3683 ≤ 12542792348011^3683*2500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1457336749 2500000000 12542792348011 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5193660589/10000000000 : ℝ), (-1183860549/10000000000 : ℝ), (1457336749/2500000000 : ℝ)] ![(43287796732297/100000000000000 : ℝ), (1635258464931/25000000000000 : ℝ), (12542792348011/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5193660589/10000000000 : ℝ)|^4707 ≤ (43287796732297/100000000000000 : ℝ)^3683
        have hw : |(5193660589/10000000000 : ℝ)|=(5193660589/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1183860549/10000000000 : ℝ)|^4707 ≤ (1635258464931/25000000000000 : ℝ)^3683
        have hw : |(-1183860549/10000000000 : ℝ)|=(1183860549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1457336749/2500000000 : ℝ)|^4707 ≤ (12542792348011/25000000000000 : ℝ)^3683
        have hw : |(1457336749/2500000000 : ℝ)|=(1457336749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s0_6 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5193660619/10000000000 : ℝ)*x 0 + (2914673413/5000000000 : ℝ)*x 1 + (-1183860769/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5193660619/10000000000 : ℝ)^4707 ≤ (43287797051859/100000000000000 : ℝ)^3683 := by
    have hnat : (5193660619 : ℕ)^4707*100000000000000^3683 ≤ 43287797051859^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5193660619 10000000000 43287797051859 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2914673413/5000000000 : ℝ)^4707 ≤ (783924492533/1562500000000 : ℝ)^3683 := by
    have hnat : (2914673413 : ℕ)^4707*1562500000000^3683 ≤ 783924492533^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2914673413 5000000000 783924492533 1562500000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1183860769/10000000000 : ℝ)^4707 ≤ (817629426653/12500000000000 : ℝ)^3683 := by
    have hnat : (1183860769 : ℕ)^4707*12500000000000^3683 ≤ 817629426653^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1183860769 10000000000 817629426653 12500000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5193660619/10000000000 : ℝ), (2914673413/5000000000 : ℝ), (-1183860769/10000000000 : ℝ)] ![(43287797051859/100000000000000 : ℝ), (783924492533/1562500000000 : ℝ), (817629426653/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5193660619/10000000000 : ℝ)|^4707 ≤ (43287797051859/100000000000000 : ℝ)^3683
        have hw : |(5193660619/10000000000 : ℝ)|=(5193660619/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2914673413/5000000000 : ℝ)|^4707 ≤ (783924492533/1562500000000 : ℝ)^3683
        have hw : |(2914673413/5000000000 : ℝ)|=(2914673413/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1183860769/10000000000 : ℝ)|^4707 ≤ (817629426653/12500000000000 : ℝ)^3683
        have hw : |(-1183860769/10000000000 : ℝ)|=(1183860769/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s0_7 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4123401201/10000000000 : ℝ)*x 0 + (5359961773/10000000000 : ℝ)*x 1 + (783572873/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4123401201/10000000000 : ℝ)^4707 ≤ (32231720277541/100000000000000 : ℝ)^3683 := by
    have hnat : (4123401201 : ℕ)^4707*100000000000000^3683 ≤ 32231720277541^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4123401201 10000000000 32231720277541 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5359961773/10000000000 : ℝ)^4707 ≤ (45067075542881/100000000000000 : ℝ)^3683 := by
    have hnat : (5359961773 : ℕ)^4707*100000000000000^3683 ≤ 45067075542881^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5359961773 10000000000 45067075542881 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (783572873/2500000000 : ℝ)^4707 ≤ (1418825261071/6250000000000 : ℝ)^3683 := by
    have hnat : (783572873 : ℕ)^4707*6250000000000^3683 ≤ 1418825261071^3683*2500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      783572873 2500000000 1418825261071 6250000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4123401201/10000000000 : ℝ), (5359961773/10000000000 : ℝ), (783572873/2500000000 : ℝ)] ![(32231720277541/100000000000000 : ℝ), (45067075542881/100000000000000 : ℝ), (1418825261071/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4123401201/10000000000 : ℝ)|^4707 ≤ (32231720277541/100000000000000 : ℝ)^3683
        have hw : |(4123401201/10000000000 : ℝ)|=(4123401201/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5359961773/10000000000 : ℝ)|^4707 ≤ (45067075542881/100000000000000 : ℝ)^3683
        have hw : |(5359961773/10000000000 : ℝ)|=(5359961773/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(783572873/2500000000 : ℝ)|^4707 ≤ (1418825261071/6250000000000 : ℝ)^3683
        have hw : |(783572873/2500000000 : ℝ)|=(783572873/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1597_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1867/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (4909/20000 : ℝ)*pair X 0 0 := by
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
  have base32 : ((1 : ℝ)*X 0 1+(1 : ℝ)*X 1 1+(1 : ℝ)*X 2 1+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 1).2]
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
  have hpowlo : (0 : ℝ) ^ (4703/1024 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^4703 ≤ (0 : ℝ)^1024 := by
      have hnat : (0 : ℕ)^4703*1^1024 ≤ 0^1024*1^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (4703/1024 : ℝ) ≤ (1487139463542457153/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^4703 ≤ (1487139463542457153/100000000000000000000 : ℝ)^1024 := by
      have hnat : (2 : ℕ)^4703*100000000000000000000^1024 ≤ 1487139463542457153^1024*5^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 1487139463542457153 100000000000000000000 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (1487139463542457153/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (1 : ℝ)^1024 ≤ (1 : ℝ)^4703 := by
      have hnat : (1 : ℕ)^1024*1^4703 ≤ 1^4703*1^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (101487139463542457153/100000000000000000000 : ℝ) ≤ (2006438657970533/2000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (101487139463542457153/100000000000000000000 : ℝ)^1024 ≤ (2006438657970533/2000000000000000 : ℝ)^4703 := by
      have hnat : (101487139463542457153 : ℕ)^1024*2000000000000000^4703 ≤ 2006438657970533^4703*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        101487139463542457153 100000000000000000000 2006438657970533 2000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2006438657970533/2000000000000000 : ℝ)) (X := (101487139463542457153/100000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (51487139463542457153/50000000000000000000 : ℝ) ≤ (1006438657970533/1000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (51487139463542457153/50000000000000000000 : ℝ)^1024 ≤ (1006438657970533/1000000000000000 : ℝ)^4703 := by
      have hnat : (51487139463542457153 : ℕ)^1024*1000000000000000^4703 ≤ 1006438657970533^4703*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        51487139463542457153 50000000000000000000 1006438657970533 1000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1006438657970533/1000000000000000 : ℝ)) (X := (51487139463542457153/50000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(6438657970533/800000000000000 : ℝ)*(0 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6438657970533/800000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(1487139463542457153/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(6438657970533/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(4703/1024 : ℝ) := by
    rw [show (1 : ℝ)+(6438657970533/800000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(2006438657970533/2000000000000000 : ℝ) by norm_num, show 1+(1487139463542457153/100000000000000000000 : ℝ)+(0 : ℝ)=(101487139463542457153/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(1487139463542457153/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(6438657970533/800000000000000 : ℝ)*(2/5 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (1 : ℝ)+2*(6438657970533/800000000000000 : ℝ)*(2/5 : ℝ)=(1006438657970533/1000000000000000 : ℝ) by norm_num, show 1+2*(1487139463542457153/100000000000000000000 : ℝ)=(51487139463542457153/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(6438657970533/800000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6438657970533/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(6438657970533/800000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6438657970533/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(6438657970533/800000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (6438657970533/800000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-397599549/2500000000 : ℝ)*X 0 0+(5854979167/10000000000 : ℝ)*X 0 1+(976624831/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5459107073/10000000000 : ℝ)*X 1 0+(-213008383/1000000000 : ℝ)*X 1 1+(4883123921/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2729553509/5000000000 : ℝ)*X 2 0+(2441561963/5000000000 : ℝ)*X 2 1+(-426016779/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2058106813/5000000000 : ℝ)*X 0 0+(1536190647/5000000000 : ℝ)*X 0 1+(541973299/1000000000 : ℝ)*X 0 2+(2058106813/5000000000 : ℝ)*X 1 0+(1536190647/5000000000 : ℝ)*X 1 1+(541973299/1000000000 : ℝ)*X 1 2+(2058106813/5000000000 : ℝ)*X 2 0+(1536190647/5000000000 : ℝ)*X 2 1+(541973299/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1593373739/10000000000 : ℝ)*X 0 0+(196314823/400000000 : ℝ)*X 0 1+(2914673409/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5193660589/10000000000 : ℝ)*X 1 0+(-1183860549/10000000000 : ℝ)*X 1 1+(1457336749/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5193660619/10000000000 : ℝ)*X 2 0+(2914673413/5000000000 : ℝ)*X 2 1+(-1183860769/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4123401201/10000000000 : ℝ)*X 0 0+(5359961773/10000000000 : ℝ)*X 0 1+(783572873/2500000000 : ℝ)*X 0 2+(4123401201/10000000000 : ℝ)*X 1 0+(5359961773/10000000000 : ℝ)*X 1 1+(783572873/2500000000 : ℝ)*X 1 2+(4123401201/10000000000 : ℝ)*X 2 0+(5359961773/10000000000 : ℝ)*X 2 1+(783572873/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7197416034768080160573/1000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (60477939/100000000000000 : ℝ)*(base1) + (85758983/6250000000000 : ℝ)*(base19) + (1361776967/100000000000000 : ℝ)*(base23) + (186580783/100000000000000 : ℝ)*(upper3) + (163769849/100000000000000 : ℝ)*(upper5) + (36374654804791/5000000000000 : ℝ)*(major0) + (36374654804791/5000000000000 : ℝ)*(major1) + (36374654804791/5000000000000 : ℝ)*(major2) + (205792976573213/20000000000000 : ℝ)*(sp0) + (128621041493871/12500000000000 : ℝ)*(sp1) + (1028968342317729/100000000000000 : ℝ)*(sp2) + (426014009741091/100000000000000 : ℝ)*(sp3) + (488170657/10000000000000 : ℝ)*(sp4) + (2177964041/100000000000000 : ℝ)*(sp7) + (13313007755721/3125000000000 : ℝ)*(f.failure) + (128621213011837/12500000000000 : ℝ)*(f.sum) + (711074749603/2000000000000000000000000000 : ℝ)*base65 + (18002937015603/4000000000000000000000000000 : ℝ)*base67 + (23217242835603/4000000000000000000000000000 : ℝ)*base69 + (17263281739603/4000000000000000000000000000 : ℝ)*base71 + (3636327209603/2000000000000000000000000000 : ℝ)*base73 + (12939598063603/4000000000000000000000000000 : ℝ)*base75 + (19376379907603/4000000000000000000000000000 : ℝ)*base77 + (961183219603/4000000000000000000000000000 : ℝ)*base79 + (5410031609603/2000000000000000000000000000 : ℝ)*base81 + (613297/156250000000000000000 : ℝ)*base89 + (613297/156250000000000000000 : ℝ)*base91 + (613297/156250000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (13776914834220628404939/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (604994759/100000000000000 : ℝ)*(base19) + (615264909/100000000000000 : ℝ)*(base23) + (48676237/50000000000000 : ℝ)*(base32) + (22875957/20000000000000 : ℝ)*(upper3) + (28311083/100000000000000 : ℝ)*(upper5) + (383629331452661/50000000000000 : ℝ)*(major0) + (383629331452661/50000000000000 : ℝ)*(major1) + (383629331452661/50000000000000 : ℝ)*(major2) + (1661969119/100000000000000 : ℝ)*(sp1) + (870132577/50000000000000 : ℝ)*(sp2) + (135651809073729/12500000000000 : ℝ)*(sp4) + (542606102812977/50000000000000 : ℝ)*(sp5) + (135651514632471/12500000000000 : ℝ)*(sp6) + (56162833002779/12500000000000 : ℝ)*(sp7) + (89860552274941/20000000000000 : ℝ)*(f.failure) + (135651809073729/12500000000000 : ℝ)*(f.sum) + (23986553241687/20000000000000000000000000000 : ℝ)*base66 + (736506207001687/40000000000000000000000000000 : ℝ)*base68 + (63933166361687/40000000000000000000000000000 : ℝ)*base70 + (275153226561687/40000000000000000000000000000 : ℝ)*base72 + (214337033961687/20000000000000000000000000000 : ℝ)*base74 + (256468174641687/40000000000000000000000000000 : ℝ)*base76 + (135446089401687/40000000000000000000000000000 : ℝ)*base78 + (320809309881687/40000000000000000000000000000 : ℝ)*base80 + (47300747998313/20000000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base88 + (2062837/1000000000000000000000 : ℝ)*base89 + (2062837/1000000000000000000000 : ℝ)*base91 + (2062837/1000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
theorem rectangle_w1597_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1867/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (4909/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1597_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1597_s1_0 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1719932427/10000000000 : ℝ)*x 0 + (2771274029/5000000000 : ℝ)*x 1 + (638987991/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1719932427/10000000000 : ℝ)^4707 ≤ (5271417327053/50000000000000 : ℝ)^3683 := by
    have hnat : (1719932427 : ℕ)^4707*50000000000000^3683 ≤ 5271417327053^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1719932427 10000000000 5271417327053 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2771274029/5000000000 : ℝ)^4707 ≤ (23519166992489/50000000000000 : ℝ)^3683 := by
    have hnat : (2771274029 : ℕ)^4707*50000000000000^3683 ≤ 23519166992489^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2771274029 5000000000 23519166992489 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (638987991/1250000000 : ℝ)^4707 ≤ (21209415672729/50000000000000 : ℝ)^3683 := by
    have hnat : (638987991 : ℕ)^4707*50000000000000^3683 ≤ 21209415672729^3683*1250000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      638987991 1250000000 21209415672729 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1719932427/10000000000 : ℝ), (2771274029/5000000000 : ℝ), (638987991/1250000000 : ℝ)] ![(5271417327053/50000000000000 : ℝ), (23519166992489/50000000000000 : ℝ), (21209415672729/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1719932427/10000000000 : ℝ)|^4707 ≤ (5271417327053/50000000000000 : ℝ)^3683
        have hw : |(-1719932427/10000000000 : ℝ)|=(1719932427/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2771274029/5000000000 : ℝ)|^4707 ≤ (23519166992489/50000000000000 : ℝ)^3683
        have hw : |(2771274029/5000000000 : ℝ)|=(2771274029/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(638987991/1250000000 : ℝ)|^4707 ≤ (21209415672729/50000000000000 : ℝ)^3683
        have hw : |(638987991/1250000000 : ℝ)|=(638987991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s1_1 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5375916809/10000000000 : ℝ)*x 0 + (-389133743/2000000000 : ℝ)*x 1 + (204476151/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375916809/10000000000 : ℝ)^4707 ≤ (11309649155833/25000000000000 : ℝ)^3683 := by
    have hnat : (5375916809 : ℕ)^4707*25000000000000^3683 ≤ 11309649155833^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375916809 10000000000 11309649155833 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (389133743/2000000000 : ℝ)^4707 ≤ (12342573638591/100000000000000 : ℝ)^3683 := by
    have hnat : (389133743 : ℕ)^4707*100000000000000^3683 ≤ 12342573638591^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      389133743 2000000000 12342573638591 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (204476151/400000000 : ℝ)^4707 ≤ (2651176857679/6250000000000 : ℝ)^3683 := by
    have hnat : (204476151 : ℕ)^4707*6250000000000^3683 ≤ 2651176857679^3683*400000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      204476151 400000000 2651176857679 6250000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375916809/10000000000 : ℝ), (-389133743/2000000000 : ℝ), (204476151/400000000 : ℝ)] ![(11309649155833/25000000000000 : ℝ), (12342573638591/100000000000000 : ℝ), (2651176857679/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375916809/10000000000 : ℝ)|^4707 ≤ (11309649155833/25000000000000 : ℝ)^3683
        have hw : |(5375916809/10000000000 : ℝ)|=(5375916809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-389133743/2000000000 : ℝ)|^4707 ≤ (12342573638591/100000000000000 : ℝ)^3683
        have hw : |(-389133743/2000000000 : ℝ)|=(389133743/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(204476151/400000000 : ℝ)|^4707 ≤ (2651176857679/6250000000000 : ℝ)^3683
        have hw : |(204476151/400000000 : ℝ)|=(204476151/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s1_2 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1075183293/2000000000 : ℝ)*x 0 + (5111904067/10000000000 : ℝ)*x 1 + (-194566879/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1075183293/2000000000 : ℝ)^4707 ≤ (45238592923709/100000000000000 : ℝ)^3683 := by
    have hnat : (1075183293 : ℕ)^4707*100000000000000^3683 ≤ 45238592923709^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1075183293 2000000000 45238592923709 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5111904067/10000000000 : ℝ)^4707 ≤ (2120941640979/5000000000000 : ℝ)^3683 := by
    have hnat : (5111904067 : ℕ)^4707*5000000000000^3683 ≤ 2120941640979^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5111904067 10000000000 2120941640979 5000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (194566879/1000000000 : ℝ)^4707 ≤ (12342574246643/100000000000000 : ℝ)^3683 := by
    have hnat : (194566879 : ℕ)^4707*100000000000000^3683 ≤ 12342574246643^3683*1000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      194566879 1000000000 12342574246643 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1075183293/2000000000 : ℝ), (5111904067/10000000000 : ℝ), (-194566879/1000000000 : ℝ)] ![(45238592923709/100000000000000 : ℝ), (2120941640979/5000000000000 : ℝ), (12342574246643/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1075183293/2000000000 : ℝ)|^4707 ≤ (45238592923709/100000000000000 : ℝ)^3683
        have hw : |(1075183293/2000000000 : ℝ)|=(1075183293/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5111904067/10000000000 : ℝ)|^4707 ≤ (2120941640979/5000000000000 : ℝ)^3683
        have hw : |(5111904067/10000000000 : ℝ)|=(5111904067/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-194566879/1000000000 : ℝ)|^4707 ≤ (12342574246643/100000000000000 : ℝ)^3683
        have hw : |(-194566879/1000000000 : ℝ)|=(194566879/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s1_3 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2105281643/5000000000 : ℝ)*x 0 + (928911001/2500000000 : ℝ)*x 1 + (594473991/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105281643/5000000000 : ℝ)^4707 ≤ (16552512604767/50000000000000 : ℝ)^3683 := by
    have hnat : (2105281643 : ℕ)^4707*50000000000000^3683 ≤ 16552512604767^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105281643 5000000000 16552512604767 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (928911001/2500000000 : ℝ)^4707 ≤ (1128622900961/4000000000000 : ℝ)^3683 := by
    have hnat : (928911001 : ℕ)^4707*4000000000000^3683 ≤ 1128622900961^3683*2500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      928911001 2500000000 1128622900961 4000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (594473991/1250000000 : ℝ)^4707 ≤ (38679402245459/100000000000000 : ℝ)^3683 := by
    have hnat : (594473991 : ℕ)^4707*100000000000000^3683 ≤ 38679402245459^3683*1250000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      594473991 1250000000 38679402245459 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105281643/5000000000 : ℝ), (928911001/2500000000 : ℝ), (594473991/1250000000 : ℝ)] ![(16552512604767/50000000000000 : ℝ), (1128622900961/4000000000000 : ℝ), (38679402245459/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105281643/5000000000 : ℝ)|^4707 ≤ (16552512604767/50000000000000 : ℝ)^3683
        have hw : |(2105281643/5000000000 : ℝ)|=(2105281643/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(928911001/2500000000 : ℝ)|^4707 ≤ (1128622900961/4000000000000 : ℝ)^3683
        have hw : |(928911001/2500000000 : ℝ)|=(928911001/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(594473991/1250000000 : ℝ)|^4707 ≤ (38679402245459/100000000000000 : ℝ)^3683
        have hw : |(594473991/1250000000 : ℝ)|=(594473991/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s1_4 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-215023093/1250000000 : ℝ)*x 0 + (1279177639/2500000000 : ℝ)*x 1 + (5537664857/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215023093/1250000000 : ℝ)^4707 ≤ (5272405684101/50000000000000 : ℝ)^3683 := by
    have hnat : (215023093 : ℕ)^4707*50000000000000^3683 ≤ 5272405684101^3683*1250000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215023093 1250000000 5272405684101 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1279177639/2500000000 : ℝ)^4707 ≤ (21234906607657/50000000000000 : ℝ)^3683 := by
    have hnat : (1279177639 : ℕ)^4707*50000000000000^3683 ≤ 21234906607657^3683*2500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1279177639 2500000000 21234906607657 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5537664857/10000000000 : ℝ)^4707 ≤ (2349268770213/5000000000000 : ℝ)^3683 := by
    have hnat : (5537664857 : ℕ)^4707*5000000000000^3683 ≤ 2349268770213^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5537664857 10000000000 2349268770213 5000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-215023093/1250000000 : ℝ), (1279177639/2500000000 : ℝ), (5537664857/10000000000 : ℝ)] ![(5272405684101/50000000000000 : ℝ), (21234906607657/50000000000000 : ℝ), (2349268770213/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-215023093/1250000000 : ℝ)|^4707 ≤ (5272405684101/50000000000000 : ℝ)^3683
        have hw : |(-215023093/1250000000 : ℝ)|=(215023093/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1279177639/2500000000 : ℝ)|^4707 ≤ (21234906607657/50000000000000 : ℝ)^3683
        have hw : |(1279177639/2500000000 : ℝ)|=(1279177639/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5537664857/10000000000 : ℝ)|^4707 ≤ (2349268770213/5000000000000 : ℝ)^3683
        have hw : |(5537664857/10000000000 : ℝ)|=(5537664857/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s1_5 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1052318371/2000000000 : ℝ)*x 0 + (-1519907631/10000000000 : ℝ)*x 1 + (5537665119/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1052318371/2000000000 : ℝ)^4707 ≤ (22006358795341/50000000000000 : ℝ)^3683 := by
    have hnat : (1052318371 : ℕ)^4707*50000000000000^3683 ≤ 22006358795341^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1052318371 2000000000 22006358795341 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1519907631/10000000000 : ℝ)^4707 ≤ (9001904158061/100000000000000 : ℝ)^3683 := by
    have hnat : (1519907631 : ℕ)^4707*100000000000000^3683 ≤ 9001904158061^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519907631 10000000000 9001904158061 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5537665119/10000000000 : ℝ)^4707 ≤ (11746344561329/25000000000000 : ℝ)^3683 := by
    have hnat : (5537665119 : ℕ)^4707*25000000000000^3683 ≤ 11746344561329^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5537665119 10000000000 11746344561329 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1052318371/2000000000 : ℝ), (-1519907631/10000000000 : ℝ), (5537665119/10000000000 : ℝ)] ![(22006358795341/50000000000000 : ℝ), (9001904158061/100000000000000 : ℝ), (11746344561329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1052318371/2000000000 : ℝ)|^4707 ≤ (22006358795341/50000000000000 : ℝ)^3683
        have hw : |(1052318371/2000000000 : ℝ)|=(1052318371/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1519907631/10000000000 : ℝ)|^4707 ≤ (9001904158061/100000000000000 : ℝ)^3683
        have hw : |(-1519907631/10000000000 : ℝ)|=(1519907631/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5537665119/10000000000 : ℝ)|^4707 ≤ (11746344561329/25000000000000 : ℝ)^3683
        have hw : |(5537665119/10000000000 : ℝ)|=(5537665119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s1_6 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5261591349/10000000000 : ℝ)*x 0 + (2768832651/5000000000 : ℝ)*x 1 + (-1519908083/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5261591349/10000000000 : ℝ)^4707 ≤ (2200635609061/5000000000000 : ℝ)^3683 := by
    have hnat : (5261591349 : ℕ)^4707*5000000000000^3683 ≤ 2200635609061^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5261591349 10000000000 2200635609061 5000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2768832651/5000000000 : ℝ)^4707 ≤ (23492690114859/50000000000000 : ℝ)^3683 := by
    have hnat : (2768832651 : ℕ)^4707*50000000000000^3683 ≤ 23492690114859^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2768832651 5000000000 23492690114859 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1519908083/10000000000 : ℝ)^4707 ≤ (1125238447427/12500000000000 : ℝ)^3683 := by
    have hnat : (1519908083 : ℕ)^4707*12500000000000^3683 ≤ 1125238447427^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1519908083 10000000000 1125238447427 12500000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5261591349/10000000000 : ℝ), (2768832651/5000000000 : ℝ), (-1519908083/10000000000 : ℝ)] ![(2200635609061/5000000000000 : ℝ), (23492690114859/50000000000000 : ℝ), (1125238447427/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5261591349/10000000000 : ℝ)|^4707 ≤ (2200635609061/5000000000000 : ℝ)^3683
        have hw : |(5261591349/10000000000 : ℝ)|=(5261591349/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2768832651/5000000000 : ℝ)|^4707 ≤ (23492690114859/50000000000000 : ℝ)^3683
        have hw : |(2768832651/5000000000 : ℝ)|=(2768832651/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1519908083/10000000000 : ℝ)|^4707 ≤ (1125238447427/12500000000000 : ℝ)^3683
        have hw : |(-1519908083/10000000000 : ℝ)|=(1519908083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s1_7 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4211172007/10000000000 : ℝ)*x 0 + (4744183031/10000000000 : ℝ)*x 1 + (745487561/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4211172007/10000000000 : ℝ)^4707 ≤ (33111141994533/100000000000000 : ℝ)^3683 := by
    have hnat : (4211172007 : ℕ)^4707*100000000000000^3683 ≤ 33111141994533^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4211172007 10000000000 33111141994533 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4744183031/10000000000 : ℝ)^4707 ≤ (7711755141687/20000000000000 : ℝ)^3683 := by
    have hnat : (4744183031 : ℕ)^4707*20000000000000^3683 ≤ 7711755141687^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4744183031 10000000000 7711755141687 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (745487561/2000000000 : ℝ)^4707 ≤ (7082520570049/25000000000000 : ℝ)^3683 := by
    have hnat : (745487561 : ℕ)^4707*25000000000000^3683 ≤ 7082520570049^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      745487561 2000000000 7082520570049 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4211172007/10000000000 : ℝ), (4744183031/10000000000 : ℝ), (745487561/2000000000 : ℝ)] ![(33111141994533/100000000000000 : ℝ), (7711755141687/20000000000000 : ℝ), (7082520570049/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4211172007/10000000000 : ℝ)|^4707 ≤ (33111141994533/100000000000000 : ℝ)^3683
        have hw : |(4211172007/10000000000 : ℝ)|=(4211172007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4744183031/10000000000 : ℝ)|^4707 ≤ (7711755141687/20000000000000 : ℝ)^3683
        have hw : |(4744183031/10000000000 : ℝ)|=(4744183031/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(745487561/2000000000 : ℝ)|^4707 ≤ (7082520570049/25000000000000 : ℝ)^3683
        have hw : |(745487561/2000000000 : ℝ)|=(745487561/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1597_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4909/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1867/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (8887/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (18007/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (4909/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1867/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (4909/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1867/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (4909/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1867/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (4909/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1867/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (4909/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1867/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (4909/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1867/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (1867/50000 : ℝ) ^ (4703/1024 : ℝ) ≤ (13844909413261/50000000000000000000 : ℝ) := by
    have hpowers : (1867/50000 : ℝ)^4703 ≤ (13844909413261/50000000000000000000 : ℝ)^1024 := by
      have hnat : (1867 : ℕ)^4703*50000000000000000000^1024 ≤ 13844909413261^1024*50000^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1867 50000 13844909413261 50000000000000000000 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1867/50000 : ℝ)) (X := (13844909413261/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (4909/20000 : ℝ) ^ (4703/1024 : ℝ) ≤ (157847765307321379/100000000000000000000 : ℝ) := by
    have hpowers : (4909/20000 : ℝ)^4703 ≤ (157847765307321379/100000000000000000000 : ℝ)^1024 := by
      have hnat : (4909 : ℕ)^4703*100000000000000000000^1024 ≤ 157847765307321379^1024*20000^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        4909 20000 157847765307321379 100000000000000000000 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (4909/20000 : ℝ)) (X := (157847765307321379/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000013844909413261/25000000000000000000 : ℝ) ≤ (10000001205799207/10000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (25000013844909413261/25000000000000000000 : ℝ)^1024 ≤ (10000001205799207/10000000000000000 : ℝ)^4703 := by
      have hnat : (25000013844909413261 : ℕ)^1024*10000000000000000^4703 ≤ 10000001205799207^4703*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000013844909413261 25000000000000000000 10000001205799207 10000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000001205799207/10000000000000000 : ℝ)) (X := (25000013844909413261/25000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100157875455126147901/100000000000000000000 : ℝ) ≤ (10003435354692807/10000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (100157875455126147901/100000000000000000000 : ℝ)^1024 ≤ (10003435354692807/10000000000000000 : ℝ)^4703 := by
      have hnat : (100157875455126147901 : ℕ)^1024*10000000000000000^4703 ≤ 10003435354692807^4703*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100157875455126147901 100000000000000000000 10003435354692807 10000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003435354692807/10000000000000000 : ℝ)) (X := (100157875455126147901/100000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50157847765307321379/50000000000000000000 : ℝ) ≤ (10006869503586407/10000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (50157847765307321379/50000000000000000000 : ℝ)^1024 ≤ (10006869503586407/10000000000000000 : ℝ)^4703 := by
      have hnat : (50157847765307321379 : ℕ)^1024*10000000000000000^4703 ≤ 10006869503586407^4703*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50157847765307321379 50000000000000000000 10006869503586407 10000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10006869503586407/10000000000000000 : ℝ)) (X := (50157847765307321379/50000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(13844909413261/50000000000000000000 : ℝ) ≤ ((208084378869949892077/208110000000000000000 : ℝ)+2*(4292686117/2601375000000 : ℝ)*(1867/50000 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (208084378869949892077/208110000000000000000 : ℝ)+2*(4292686117/2601375000000 : ℝ)*(1867/50000 : ℝ)=(10000001205799207/10000000000000000 : ℝ) by norm_num, show 1+2*(13844909413261/50000000000000000000 : ℝ)=(25000013844909413261/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(157847765307321379/100000000000000000000 : ℝ)+(13844909413261/50000000000000000000 : ℝ) ≤ ((208084378869949892077/208110000000000000000 : ℝ)+(4292686117/2601375000000 : ℝ)*((4909/20000 : ℝ)+(1867/50000 : ℝ)))^(4703/1024 : ℝ) := by
    rw [show (208084378869949892077/208110000000000000000 : ℝ)+(4292686117/2601375000000 : ℝ)*((4909/20000 : ℝ)+(1867/50000 : ℝ))=(10003435354692807/10000000000000000 : ℝ) by norm_num, show 1+(157847765307321379/100000000000000000000 : ℝ)+(13844909413261/50000000000000000000 : ℝ)=(100157875455126147901/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(157847765307321379/100000000000000000000 : ℝ) ≤ ((208084378869949892077/208110000000000000000 : ℝ)+2*(4292686117/2601375000000 : ℝ)*(4909/20000 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (208084378869949892077/208110000000000000000 : ℝ)+2*(4292686117/2601375000000 : ℝ)*(4909/20000 : ℝ)=(10006869503586407/10000000000000000 : ℝ) by norm_num, show 1+2*(157847765307321379/100000000000000000000 : ℝ)=(50157847765307321379/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (208084378869949892077/208110000000000000000 : ℝ)*(X 1 0+X 2 0)+(4292686117/2601375000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (1867/50000 : ℝ)) (hi := (4909/20000 : ℝ)) (c := (208084378869949892077/208110000000000000000 : ℝ)) (alpha := (4292686117/2601375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (208084378869949892077/208110000000000000000 : ℝ)*(X 0 1+X 2 1)+(4292686117/2601375000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (1867/50000 : ℝ)) (hi := (4909/20000 : ℝ)) (c := (208084378869949892077/208110000000000000000 : ℝ)) (alpha := (4292686117/2601375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (208084378869949892077/208110000000000000000 : ℝ)*(X 0 2+X 1 2)+(4292686117/2601375000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (1867/50000 : ℝ)) (hi := (4909/20000 : ℝ)) (c := (208084378869949892077/208110000000000000000 : ℝ)) (alpha := (4292686117/2601375000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1719932427/10000000000 : ℝ)*X 0 0+(2771274029/5000000000 : ℝ)*X 0 1+(638987991/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5375916809/10000000000 : ℝ)*X 1 0+(-389133743/2000000000 : ℝ)*X 1 1+(204476151/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((1075183293/2000000000 : ℝ)*X 2 0+(5111904067/10000000000 : ℝ)*X 2 1+(-194566879/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2105281643/5000000000 : ℝ)*X 0 0+(928911001/2500000000 : ℝ)*X 0 1+(594473991/1250000000 : ℝ)*X 0 2+(2105281643/5000000000 : ℝ)*X 1 0+(928911001/2500000000 : ℝ)*X 1 1+(594473991/1250000000 : ℝ)*X 1 2+(2105281643/5000000000 : ℝ)*X 2 0+(928911001/2500000000 : ℝ)*X 2 1+(594473991/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-215023093/1250000000 : ℝ)*X 0 0+(1279177639/2500000000 : ℝ)*X 0 1+(5537664857/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((1052318371/2000000000 : ℝ)*X 1 0+(-1519907631/10000000000 : ℝ)*X 1 1+(5537665119/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5261591349/10000000000 : ℝ)*X 2 0+(2768832651/5000000000 : ℝ)*X 2 1+(-1519908083/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4211172007/10000000000 : ℝ)*X 0 0+(4744183031/10000000000 : ℝ)*X 0 1+(745487561/2000000000 : ℝ)*X 0 2+(4211172007/10000000000 : ℝ)*X 1 0+(4744183031/10000000000 : ℝ)*X 1 1+(745487561/2000000000 : ℝ)*X 1 2+(4211172007/10000000000 : ℝ)*X 2 0+(4744183031/10000000000 : ℝ)*X 2 1+(745487561/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (7911026722218244323299949/867125000000000000000000000000 : ℝ) := by norm_num
    linear_combination (8602347/10000000000000 : ℝ)*(base1) + (1952691137/100000000000000 : ℝ)*(base19) + (451025009/25000000000000 : ℝ)*(base23) + (240568983/100000000000000 : ℝ)*(upper3) + (86387863/50000000000000 : ℝ)*(upper5) + (820887201587/50000000000 : ℝ)*(major0) + (820887201587/50000000000 : ℝ)*(major1) + (820887201587/50000000000 : ℝ)*(major2) + (290264870865233/12500000000000 : ℝ)*(sp0) + (145133239319369/6250000000000 : ℝ)*(sp1) + (1161065988850503/50000000000000 : ℝ)*(sp2) + (240351999456487/25000000000000 : ℝ)*(sp3) + (1862612831/12500000000000 : ℝ)*(sp4) + (3318294051/50000000000000 : ℝ)*(sp7) + (961414720437521/100000000000000 : ℝ)*(f.failure) + (1161066890900521/50000000000000 : ℝ)*(f.sum) + (30772997359711/10405500000000000000000000000 : ℝ)*base66 + (11249532582640267/3468500000000000000000000000000 : ℝ)*base68 + (9698286289358267/3468500000000000000000000000000 : ℝ)*base70 + (1492082553315733/3468500000000000000000000000000 : ℝ)*base71 + (20849686065367/10405500000000000000000000000 : ℝ)*base74 + (20412359560490267/3468500000000000000000000000000 : ℝ)*base76 + (7458338180883267/3468500000000000000000000000000 : ℝ)*base78 + (43785793371077267/3468500000000000000000000000000 : ℝ)*base80 + (19520711421727/10405500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (7985897/5000000000000000000000 : ℝ)*base89 + (7985897/5000000000000000000000 : ℝ)*base91 + (7985897/5000000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (665155586371031789843491581/61937500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2051812623/100000000000000 : ℝ)*(base19) + (1813588251/100000000000000 : ℝ)*(base23) + (9392387/100000000000000 : ℝ)*(upper2) + (328289497/100000000000000 : ℝ)*(upper3) + (97570267/50000000000000 : ℝ)*(upper5) + (419885395684371/25000000000000 : ℝ)*(major0) + (419885395684371/25000000000000 : ℝ)*(major1) + (419885395684371/25000000000000 : ℝ)*(major2) + (15255905063/100000000000000 : ℝ)*(sp1) + (6992320279/50000000000000 : ℝ)*(sp2) + (47511036385151/2000000000000 : ℝ)*(sp4) + (296941813942483/12500000000000 : ℝ)*(sp5) + (2375536021028741/100000000000000 : ℝ)*(sp6) + (122941373530753/12500000000000 : ℝ)*(sp7) + (122941373530753/12500000000000 : ℝ)*(f.failure) + (47511036385151/2000000000000 : ℝ)*(f.sum) + (3683287185143/867125000000000000000000000 : ℝ)*base65 + (3685391687910123811/1734250000000000000000000000000000 : ℝ)*base68 + (15580163485675623811/1734250000000000000000000000000000 : ℝ)*base70 + (13248471618511873811/1734250000000000000000000000000000 : ℝ)*base72 + (4242975572721/1387400000000000000000000000 : ℝ)*base73 + (15537147653342373811/1734250000000000000000000000000000 : ℝ)*base76 + (686509134412126189/1734250000000000000000000000000000 : ℝ)*base77 + (12679379314114123811/1734250000000000000000000000000000 : ℝ)*base80 + (16508711842029/6937000000000000000000000000 : ℝ)*base82 + (5802521/625000000000000000000 : ℝ)*base89 + (5802521/625000000000000000000 : ℝ)*base91 + (5802521/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1597_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (4909/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1867/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8887/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (18007/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1597_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1597_s2_0 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-347146429/2000000000 : ℝ)*x 0 + (5472554249/10000000000 : ℝ)*x 1 + (323223799/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (347146429/2000000000 : ℝ)^4707 ≤ (10666768767963/100000000000000 : ℝ)^3683 := by
    have hnat : (347146429 : ℕ)^4707*100000000000000^3683 ≤ 10666768767963^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      347146429 2000000000 10666768767963 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5472554249/10000000000 : ℝ)^4707 ≤ (4628049117831/10000000000000 : ℝ)^3683 := by
    have hnat : (5472554249 : ℕ)^4707*10000000000000^3683 ≤ 4628049117831^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472554249 10000000000 4628049117831 10000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (323223799/625000000 : ℝ)^4707 ≤ (8610548007903/20000000000000 : ℝ)^3683 := by
    have hnat : (323223799 : ℕ)^4707*20000000000000^3683 ≤ 8610548007903^3683*625000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323223799 625000000 8610548007903 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-347146429/2000000000 : ℝ), (5472554249/10000000000 : ℝ), (323223799/625000000 : ℝ)] ![(10666768767963/100000000000000 : ℝ), (4628049117831/10000000000000 : ℝ), (8610548007903/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-347146429/2000000000 : ℝ)|^4707 ≤ (10666768767963/100000000000000 : ℝ)^3683
        have hw : |(-347146429/2000000000 : ℝ)|=(347146429/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5472554249/10000000000 : ℝ)|^4707 ≤ (4628049117831/10000000000000 : ℝ)^3683
        have hw : |(5472554249/10000000000 : ℝ)|=(5472554249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(323223799/625000000 : ℝ)|^4707 ≤ (8610548007903/20000000000000 : ℝ)^3683
        have hw : |(323223799/625000000 : ℝ)|=(323223799/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s2_1 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2678892979/5000000000 : ℝ)*x 0 + (-472826711/2500000000 : ℝ)*x 1 + (1034316119/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2678892979/5000000000 : ℝ)^4707 ≤ (9008739182733/20000000000000 : ℝ)^3683 := by
    have hnat : (2678892979 : ℕ)^4707*20000000000000^3683 ≤ 9008739182733^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2678892979 5000000000 9008739182733 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (472826711/2500000000 : ℝ)^4707 ≤ (11903566037349/100000000000000 : ℝ)^3683 := by
    have hnat : (472826711 : ℕ)^4707*100000000000000^3683 ≤ 11903566037349^3683*2500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472826711 2500000000 11903566037349 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1034316119/2000000000 : ℝ)^4707 ≤ (2690796126791/6250000000000 : ℝ)^3683 := by
    have hnat : (1034316119 : ℕ)^4707*6250000000000^3683 ≤ 2690796126791^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1034316119 2000000000 2690796126791 6250000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2678892979/5000000000 : ℝ), (-472826711/2500000000 : ℝ), (1034316119/2000000000 : ℝ)] ![(9008739182733/20000000000000 : ℝ), (11903566037349/100000000000000 : ℝ), (2690796126791/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2678892979/5000000000 : ℝ)|^4707 ≤ (9008739182733/20000000000000 : ℝ)^3683
        have hw : |(2678892979/5000000000 : ℝ)|=(2678892979/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-472826711/2500000000 : ℝ)|^4707 ≤ (11903566037349/100000000000000 : ℝ)^3683
        have hw : |(-472826711/2500000000 : ℝ)|=(472826711/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1034316119/2000000000 : ℝ)|^4707 ≤ (2690796126791/6250000000000 : ℝ)^3683
        have hw : |(1034316119/2000000000 : ℝ)|=(1034316119/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s2_2 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5357785549/10000000000 : ℝ)*x 0 + (1292895269/2500000000 : ℝ)*x 1 + (-378261351/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5357785549/10000000000 : ℝ)^4707 ≤ (22521845759557/50000000000000 : ℝ)^3683 := by
    have hnat : (5357785549 : ℕ)^4707*50000000000000^3683 ≤ 22521845759557^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5357785549 10000000000 22521845759557 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1292895269/2500000000 : ℝ)^4707 ≤ (33634955583/78125000000 : ℝ)^3683 := by
    have hnat : (1292895269 : ℕ)^4707*78125000000^3683 ≤ 33634955583^3683*2500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1292895269 2500000000 33634955583 78125000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (378261351/2000000000 : ℝ)^4707 ≤ (11903565321457/100000000000000 : ℝ)^3683 := by
    have hnat : (378261351 : ℕ)^4707*100000000000000^3683 ≤ 11903565321457^3683*2000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      378261351 2000000000 11903565321457 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5357785549/10000000000 : ℝ), (1292895269/2500000000 : ℝ), (-378261351/2000000000 : ℝ)] ![(22521845759557/50000000000000 : ℝ), (33634955583/78125000000 : ℝ), (11903565321457/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5357785549/10000000000 : ℝ)|^4707 ≤ (22521845759557/50000000000000 : ℝ)^3683
        have hw : |(5357785549/10000000000 : ℝ)|=(5357785549/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1292895269/2500000000 : ℝ)|^4707 ≤ (33634955583/78125000000 : ℝ)^3683
        have hw : |(1292895269/2500000000 : ℝ)|=(1292895269/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-378261351/2000000000 : ℝ)|^4707 ≤ (11903565321457/100000000000000 : ℝ)^3683
        have hw : |(-378261351/2000000000 : ℝ)|=(378261351/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s2_3 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4222179373/10000000000 : ℝ)*x 0 + (3870992933/10000000000 : ℝ)*x 1 + (4597943159/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4222179373/10000000000 : ℝ)^4707 ≤ (6644358568543/20000000000000 : ℝ)^3683 := by
    have hnat : (4222179373 : ℕ)^4707*20000000000000^3683 ≤ 6644358568543^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4222179373 10000000000 6644358568543 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3870992933/10000000000 : ℝ)^4707 ≤ (14865958048567/50000000000000 : ℝ)^3683 := by
    have hnat : (3870992933 : ℕ)^4707*50000000000000^3683 ≤ 14865958048567^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3870992933 10000000000 14865958048567 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4597943159/10000000000 : ℝ)^4707 ≤ (18523145519327/50000000000000 : ℝ)^3683 := by
    have hnat : (4597943159 : ℕ)^4707*50000000000000^3683 ≤ 18523145519327^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4597943159 10000000000 18523145519327 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4222179373/10000000000 : ℝ), (3870992933/10000000000 : ℝ), (4597943159/10000000000 : ℝ)] ![(6644358568543/20000000000000 : ℝ), (14865958048567/50000000000000 : ℝ), (18523145519327/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4222179373/10000000000 : ℝ)|^4707 ≤ (6644358568543/20000000000000 : ℝ)^3683
        have hw : |(4222179373/10000000000 : ℝ)|=(4222179373/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3870992933/10000000000 : ℝ)|^4707 ≤ (14865958048567/50000000000000 : ℝ)^3683
        have hw : |(3870992933/10000000000 : ℝ)|=(3870992933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4597943159/10000000000 : ℝ)|^4707 ≤ (18523145519327/50000000000000 : ℝ)^3683
        have hw : |(4597943159/10000000000 : ℝ)|=(4597943159/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s2_4 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-173581809/1000000000 : ℝ)*x 0 + (2586968197/5000000000 : ℝ)*x 1 + (5470172651/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (173581809/1000000000 : ℝ)^4707 ≤ (1066744378737/10000000000000 : ℝ)^3683 := by
    have hnat : (173581809 : ℕ)^4707*10000000000000^3683 ≤ 1066744378737^3683*1000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      173581809 1000000000 1066744378737 10000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2586968197/5000000000 : ℝ)^4707 ≤ (10769451016613/25000000000000 : ℝ)^3683 := by
    have hnat : (2586968197 : ℕ)^4707*25000000000000^3683 ≤ 10769451016613^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2586968197 5000000000 10769451016613 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470172651/10000000000 : ℝ)^4707 ≤ (46254752126583/100000000000000 : ℝ)^3683 := by
    have hnat : (5470172651 : ℕ)^4707*100000000000000^3683 ≤ 46254752126583^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470172651 10000000000 46254752126583 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-173581809/1000000000 : ℝ), (2586968197/5000000000 : ℝ), (5470172651/10000000000 : ℝ)] ![(1066744378737/10000000000000 : ℝ), (10769451016613/25000000000000 : ℝ), (46254752126583/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-173581809/1000000000 : ℝ)|^4707 ≤ (1066744378737/10000000000000 : ℝ)^3683
        have hw : |(-173581809/1000000000 : ℝ)|=(173581809/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2586968197/5000000000 : ℝ)|^4707 ≤ (10769451016613/25000000000000 : ℝ)^3683
        have hw : |(2586968197/5000000000 : ℝ)|=(2586968197/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470172651/10000000000 : ℝ)|^4707 ≤ (46254752126583/100000000000000 : ℝ)^3683
        have hw : |(5470172651/10000000000 : ℝ)|=(5470172651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s2_5 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278037557/10000000000 : ℝ)*x 0 + (-1592714947/10000000000 : ℝ)*x 1 + (5470172729/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278037557/10000000000 : ℝ)^4707 ≤ (44188608927133/100000000000000 : ℝ)^3683 := by
    have hnat : (5278037557 : ℕ)^4707*100000000000000^3683 ≤ 44188608927133^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278037557 10000000000 44188608927133 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1592714947/10000000000 : ℝ)^4707 ≤ (4778319043171/50000000000000 : ℝ)^3683 := by
    have hnat : (1592714947 : ℕ)^4707*50000000000000^3683 ≤ 4778319043171^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1592714947 10000000000 4778319043171 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5470172729/10000000000 : ℝ)^4707 ≤ (9250950593903/20000000000000 : ℝ)^3683 := by
    have hnat : (5470172729 : ℕ)^4707*20000000000000^3683 ≤ 9250950593903^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470172729 10000000000 9250950593903 20000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278037557/10000000000 : ℝ), (-1592714947/10000000000 : ℝ), (5470172729/10000000000 : ℝ)] ![(44188608927133/100000000000000 : ℝ), (4778319043171/50000000000000 : ℝ), (9250950593903/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278037557/10000000000 : ℝ)|^4707 ≤ (44188608927133/100000000000000 : ℝ)^3683
        have hw : |(5278037557/10000000000 : ℝ)|=(5278037557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1592714947/10000000000 : ℝ)|^4707 ≤ (4778319043171/50000000000000 : ℝ)^3683
        have hw : |(-1592714947/10000000000 : ℝ)|=(1592714947/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5470172729/10000000000 : ℝ)|^4707 ≤ (9250950593903/20000000000000 : ℝ)^3683
        have hw : |(5470172729/10000000000 : ℝ)|=(5470172729/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s2_6 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5278037641/10000000000 : ℝ)*x 0 + (5470172529/10000000000 : ℝ)*x 1 + (-199089389/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5278037641/10000000000 : ℝ)^4707 ≤ (22094304912963/50000000000000 : ℝ)^3683 := by
    have hnat : (5278037641 : ℕ)^4707*50000000000000^3683 ≤ 22094304912963^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5278037641 10000000000 22094304912963 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5470172529/10000000000 : ℝ)^4707 ≤ (5781843851019/12500000000000 : ℝ)^3683 := by
    have hnat : (5470172529 : ℕ)^4707*12500000000000^3683 ≤ 5781843851019^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5470172529 10000000000 5781843851019 12500000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (199089389/1250000000 : ℝ)^4707 ≤ (4778319675821/50000000000000 : ℝ)^3683 := by
    have hnat : (199089389 : ℕ)^4707*50000000000000^3683 ≤ 4778319675821^3683*1250000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      199089389 1250000000 4778319675821 50000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5278037641/10000000000 : ℝ), (5470172529/10000000000 : ℝ), (-199089389/1250000000 : ℝ)] ![(22094304912963/50000000000000 : ℝ), (5781843851019/12500000000000 : ℝ), (4778319675821/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5278037641/10000000000 : ℝ)|^4707 ≤ (22094304912963/50000000000000 : ℝ)^3683
        have hw : |(5278037641/10000000000 : ℝ)|=(5278037641/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5470172529/10000000000 : ℝ)|^4707 ≤ (5781843851019/12500000000000 : ℝ)^3683
        have hw : |(5470172529/10000000000 : ℝ)|=(5470172529/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-199089389/1250000000 : ℝ)|^4707 ≤ (4778319675821/50000000000000 : ℝ)^3683
        have hw : |(-199089389/1250000000 : ℝ)|=(199089389/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1597_s2_7 (p : ℝ) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1055596877/2500000000 : ℝ)*x 0 + (2296126973/5000000000 : ℝ)*x 1 + (3876745551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055596877/2500000000 : ℝ)^4707 ≤ (8305971469993/25000000000000 : ℝ)^3683 := by
    have hnat : (1055596877 : ℕ)^4707*25000000000000^3683 ≤ 8305971469993^3683*2500000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055596877 2500000000 8305971469993 25000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2296126973/5000000000 : ℝ)^4707 ≤ (36987717551939/100000000000000 : ℝ)^3683 := by
    have hnat : (2296126973 : ℕ)^4707*100000000000000^3683 ≤ 36987717551939^3683*5000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2296126973 5000000000 36987717551939 100000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3876745551/10000000000 : ℝ)^4707 ≤ (2978839655587/10000000000000 : ℝ)^3683 := by
    have hnat : (3876745551 : ℕ)^4707*10000000000000^3683 ≤ 2978839655587^3683*10000000000^4707 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3876745551 10000000000 2978839655587 10000000000000 4707 3683 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4707/1024 : ℝ)) 4707 3683 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1055596877/2500000000 : ℝ), (2296126973/5000000000 : ℝ), (3876745551/10000000000 : ℝ)] ![(8305971469993/25000000000000 : ℝ), (36987717551939/100000000000000 : ℝ), (2978839655587/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1055596877/2500000000 : ℝ)|^4707 ≤ (8305971469993/25000000000000 : ℝ)^3683
        have hw : |(1055596877/2500000000 : ℝ)|=(1055596877/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2296126973/5000000000 : ℝ)|^4707 ≤ (36987717551939/100000000000000 : ℝ)^3683
        have hw : |(2296126973/5000000000 : ℝ)|=(2296126973/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3876745551/10000000000 : ℝ)|^4707 ≤ (2978839655587/10000000000000 : ℝ)^3683
        have hw : |(3876745551/10000000000 : ℝ)|=(3876745551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1597_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8887/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (318/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2069/12500 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (18007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8887/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (18007/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8887/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (18007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8887/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (18007/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8887/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (18007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8887/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (18007/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8887/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8887/100000 : ℝ) ^ (4703/1024 : ℝ) ≤ (742746680469051/50000000000000000000 : ℝ) := by
    have hpowers : (8887/100000 : ℝ)^4703 ≤ (742746680469051/50000000000000000000 : ℝ)^1024 := by
      have hnat : (8887 : ℕ)^4703*50000000000000000000^1024 ≤ 742746680469051^1024*100000^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8887 100000 742746680469051 50000000000000000000 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8887/100000 : ℝ)) (X := (742746680469051/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (18007/100000 : ℝ) ^ (4703/1024 : ℝ) ≤ (9513731385410263/25000000000000000000 : ℝ) := by
    have hpowers : (18007/100000 : ℝ)^4703 ≤ (9513731385410263/25000000000000000000 : ℝ)^1024 := by
      have hnat : (18007 : ℕ)^4703*25000000000000000000^1024 ≤ 9513731385410263^1024*100000^4703 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        18007 100000 9513731385410263 25000000000000000000 4703 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (18007/100000 : ℝ)) (X := (9513731385410263/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000742746680469051/25000000000000000000 : ℝ) ≤ (200001293750819/200000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (25000742746680469051/25000000000000000000 : ℝ)^1024 ≤ (200001293750819/200000000000000 : ℝ)^4703 := by
      have hnat : (25000742746680469051 : ℕ)^1024*200000000000000^4703 ≤ 200001293750819^4703*25000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000742746680469051 25000000000000000000 200001293750819 200000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (200001293750819/200000000000000 : ℝ)) (X := (25000742746680469051/25000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50019770209451289577/50000000000000000000 : ℝ) ≤ (10000860793716987/10000000000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (50019770209451289577/50000000000000000000 : ℝ)^1024 ≤ (10000860793716987/10000000000000000 : ℝ)^4703 := by
      have hnat : (50019770209451289577 : ℕ)^1024*10000000000000000^4703 ≤ 10000860793716987^4703*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50019770209451289577 50000000000000000000 10000860793716987 10000000000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000860793716987/10000000000000000 : ℝ)) (X := (50019770209451289577/50000000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (12509513731385410263/12500000000000000000 : ℝ) ≤ (312551778121657/312500000000000 : ℝ) ^ (4703/1024 : ℝ) := by
    have hpowers : (12509513731385410263/12500000000000000000 : ℝ)^1024 ≤ (312551778121657/312500000000000 : ℝ)^4703 := by
      have hnat : (12509513731385410263 : ℕ)^1024*312500000000000^4703 ≤ 312551778121657^4703*12500000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12509513731385410263 12500000000000000000 312551778121657 312500000000000 1024 4703 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312551778121657/312500000000000 : ℝ)) (X := (12509513731385410263/12500000000000000000 : ℝ)) (by norm_num) 4703 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(742746680469051/50000000000000000000 : ℝ) ≤ ((45593219979600291181/45600000000000000000 : ℝ)+2*(796106176037/912000000000000 : ℝ)*(8887/100000 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (45593219979600291181/45600000000000000000 : ℝ)+2*(796106176037/912000000000000 : ℝ)*(8887/100000 : ℝ)=(200001293750819/200000000000000 : ℝ) by norm_num, show 1+2*(742746680469051/50000000000000000000 : ℝ)=(25000742746680469051/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(9513731385410263/25000000000000000000 : ℝ)+(742746680469051/50000000000000000000 : ℝ) ≤ ((45593219979600291181/45600000000000000000 : ℝ)+(796106176037/912000000000000 : ℝ)*((18007/100000 : ℝ)+(8887/100000 : ℝ)))^(4703/1024 : ℝ) := by
    rw [show (45593219979600291181/45600000000000000000 : ℝ)+(796106176037/912000000000000 : ℝ)*((18007/100000 : ℝ)+(8887/100000 : ℝ))=(10000860793716987/10000000000000000 : ℝ) by norm_num, show 1+(9513731385410263/25000000000000000000 : ℝ)+(742746680469051/50000000000000000000 : ℝ)=(50019770209451289577/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(9513731385410263/25000000000000000000 : ℝ) ≤ ((45593219979600291181/45600000000000000000 : ℝ)+2*(796106176037/912000000000000 : ℝ)*(18007/100000 : ℝ))^(4703/1024 : ℝ) := by
    rw [show (45593219979600291181/45600000000000000000 : ℝ)+2*(796106176037/912000000000000 : ℝ)*(18007/100000 : ℝ)=(312551778121657/312500000000000 : ℝ) by norm_num, show 1+2*(9513731385410263/25000000000000000000 : ℝ)=(12509513731385410263/12500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (45593219979600291181/45600000000000000000 : ℝ)*(X 1 0+X 2 0)+(796106176037/912000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (8887/100000 : ℝ)) (hi := (18007/100000 : ℝ)) (c := (45593219979600291181/45600000000000000000 : ℝ)) (alpha := (796106176037/912000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (45593219979600291181/45600000000000000000 : ℝ)*(X 0 1+X 2 1)+(796106176037/912000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (8887/100000 : ℝ)) (hi := (18007/100000 : ℝ)) (c := (45593219979600291181/45600000000000000000 : ℝ)) (alpha := (796106176037/912000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (45593219979600291181/45600000000000000000 : ℝ)*(X 0 2+X 1 2)+(796106176037/912000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4703/1024 : ℝ)) (lo := (8887/100000 : ℝ)) (hi := (18007/100000 : ℝ)) (c := (45593219979600291181/45600000000000000000 : ℝ)) (alpha := (796106176037/912000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-347146429/2000000000 : ℝ)*X 0 0+(5472554249/10000000000 : ℝ)*X 0 1+(323223799/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2678892979/5000000000 : ℝ)*X 1 0+(-472826711/2500000000 : ℝ)*X 1 1+(1034316119/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5357785549/10000000000 : ℝ)*X 2 0+(1292895269/2500000000 : ℝ)*X 2 1+(-378261351/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4222179373/10000000000 : ℝ)*X 0 0+(3870992933/10000000000 : ℝ)*X 0 1+(4597943159/10000000000 : ℝ)*X 0 2+(4222179373/10000000000 : ℝ)*X 1 0+(3870992933/10000000000 : ℝ)*X 1 1+(4597943159/10000000000 : ℝ)*X 1 2+(4222179373/10000000000 : ℝ)*X 2 0+(3870992933/10000000000 : ℝ)*X 2 1+(4597943159/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-173581809/1000000000 : ℝ)*X 0 0+(2586968197/5000000000 : ℝ)*X 0 1+(5470172651/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5278037557/10000000000 : ℝ)*X 1 0+(-1592714947/10000000000 : ℝ)*X 1 1+(5470172729/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5278037641/10000000000 : ℝ)*X 2 0+(5470172529/10000000000 : ℝ)*X 2 1+(-199089389/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1055596877/2500000000 : ℝ)*X 0 0+(2296126973/5000000000 : ℝ)*X 0 1+(3876745551/10000000000 : ℝ)*X 0 2+(1055596877/2500000000 : ℝ)*X 1 0+(2296126973/5000000000 : ℝ)*X 1 1+(3876745551/10000000000 : ℝ)*X 1 2+(1055596877/2500000000 : ℝ)*X 2 0+(2296126973/5000000000 : ℝ)*X 2 1+(3876745551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1597_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (4777169614547361010172432511/380000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2029986403/100000000000000 : ℝ)*(base19) + (85280949/5000000000000 : ℝ)*(base23) + (37895097/100000000000000 : ℝ)*(lower2) + (151248059/50000000000000 : ℝ)*(upper3) + (54349789/20000000000000 : ℝ)*(upper5) + (1174555454896069/50000000000000 : ℝ)*(major0) + (1174555454896069/50000000000000 : ℝ)*(major1) + (1174555454896069/50000000000000 : ℝ)*(major2) + (830643358911657/25000000000000 : ℝ)*(sp0) + (1661295998981759/50000000000000 : ℝ)*(sp1) + (3322592322330941/100000000000000 : ℝ)*(sp2) + (687809312129933/50000000000000 : ℝ)*(sp3) + (5148075823/25000000000000 : ℝ)*(sp4) + (4374162257/50000000000000 : ℝ)*(sp7) + (68781368629219/5000000000000 : ℝ)*(f.failure) + (20766212674687/625000000000 : ℝ)*(f.sum) + (100710441286553/22800000000000000000000000000 : ℝ)*base65 + (35693548105659917489/2280000000000000000000000000000000 : ℝ)*base67 + (16260044006859917489/2280000000000000000000000000000000 : ℝ)*base69 + (10748513316699917489/2280000000000000000000000000000000 : ℝ)*base71 + (79489655014553/22800000000000000000000000000 : ℝ)*base73 + (2508619059620082511/2280000000000000000000000000000000 : ℝ)*base76 + (23633497004499917489/2280000000000000000000000000000000 : ℝ)*base77 + (321653593220082511/2280000000000000000000000000000000 : ℝ)*base80 + (64538980629847/22800000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (1413717/250000000000000000000 : ℝ)*base90 + (1413717/250000000000000000000 : ℝ)*base92 + (1413717/250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1100068697142302468105768321/152000000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (12125243/2000000000000 : ℝ)*(base19) + (817155907/100000000000000 : ℝ)*(base23) + (114877723/100000000000000 : ℝ)*(upper3) + (83262801/100000000000000 : ℝ)*(lower4) + (11586981/10000000000000 : ℝ)*(upper5) + (477329064792059/20000000000000 : ℝ)*(major0) + (477329064792059/20000000000000 : ℝ)*(major1) + (477329064792059/20000000000000 : ℝ)*(major2) + (6231875069/100000000000000 : ℝ)*(sp1) + (1238658001/20000000000000 : ℝ)*(sp2) + (337568307251339/10000000000000 : ℝ)*(sp4) + (337567623437617/10000000000000 : ℝ)*(sp5) + (1687838031033739/50000000000000 : ℝ)*(sp6) + (1397607334164059/100000000000000 : ℝ)*(sp7) + (1397607334164059/100000000000000 : ℝ)*(f.failure) + (337568307251339/10000000000000 : ℝ)*(f.sum) + (4859289142457/9120000000000000000000000000 : ℝ)*base66 + (1661364759837681679/912000000000000000000000000000000 : ℝ)*base67 + (73264643762318321/912000000000000000000000000000000 : ℝ)*base70 + (4901581935357681679/912000000000000000000000000000000 : ℝ)*base71 + (6746141592377/9120000000000000000000000000 : ℝ)*base74 + (9998081685597681679/912000000000000000000000000000000 : ℝ)*base75 + (982919167245681679/912000000000000000000000000000000 : ℝ)*base77 + (3413497162946318321/912000000000000000000000000000000 : ℝ)*base80 + (18654112915577/9120000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (20239837/5000000000000000000000 : ℝ)*base90 + (20239837/5000000000000000000000 : ℝ)*base92 + (20239837/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1597_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (18007/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8887/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (318/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2069/12500 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1597_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1597_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (318/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2069/12500 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1597_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1597_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1597_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4703/1024 : ℝ) ≤ p) (hpb : p ≤ (4707/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (85383257/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (318/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2069/12500 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1597_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
