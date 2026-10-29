-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1440_b2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:56:43.608988+00:00
-- url     : https://prove2.me/submissions/cbb03279-fb38-45f4-a883-f7428da7ad5f

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
theorem support_rectangle_w1440_s6_0 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1962239633/10000000000 : ℝ)*x 0 + (5407654331/10000000000 : ℝ)*x 1 + (5247145003/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1962239633/10000000000 : ℝ)^275 ≤ (11973781699469/100000000000000 : ℝ)^211 := by
    have hnat : (1962239633 : ℕ)^275*100000000000000^211 ≤ 11973781699469^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962239633 10000000000 11973781699469 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407654331/10000000000 : ℝ)^275 ≤ (22438604899923/50000000000000 : ℝ)^211 := by
    have hnat : (5407654331 : ℕ)^275*50000000000000^211 ≤ 22438604899923^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407654331 10000000000 22438604899923 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247145003/10000000000 : ℝ)^275 ≤ (21574504240633/50000000000000 : ℝ)^211 := by
    have hnat : (5247145003 : ℕ)^275*50000000000000^211 ≤ 21574504240633^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247145003 10000000000 21574504240633 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1962239633/10000000000 : ℝ), (5407654331/10000000000 : ℝ), (5247145003/10000000000 : ℝ)] ![(11973781699469/100000000000000 : ℝ), (22438604899923/50000000000000 : ℝ), (21574504240633/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1962239633/10000000000 : ℝ)|^275 ≤ (11973781699469/100000000000000 : ℝ)^211
        have hw : |(-1962239633/10000000000 : ℝ)|=(1962239633/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407654331/10000000000 : ℝ)|^275 ≤ (22438604899923/50000000000000 : ℝ)^211
        have hw : |(5407654331/10000000000 : ℝ)|=(5407654331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247145003/10000000000 : ℝ)|^275 ≤ (21574504240633/50000000000000 : ℝ)^211
        have hw : |(5247145003/10000000000 : ℝ)|=(5247145003/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s6_1 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5347094041/10000000000 : ℝ)*x 0 + (-1021975007/5000000000 : ℝ)*x 1 + (1311786251/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347094041/10000000000 : ℝ)^275 ≤ (4422330438397/10000000000000 : ℝ)^211 := by
    have hnat : (5347094041 : ℕ)^275*10000000000000^211 ≤ 4422330438397^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347094041 10000000000 4422330438397 10000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021975007/5000000000 : ℝ)^275 ≤ (6313843556659/50000000000000 : ℝ)^211 := by
    have hnat : (1021975007 : ℕ)^275*50000000000000^211 ≤ 6313843556659^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021975007 5000000000 6313843556659 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1311786251/2500000000 : ℝ)^275 ≤ (2696813030749/6250000000000 : ℝ)^211 := by
    have hnat : (1311786251 : ℕ)^275*6250000000000^211 ≤ 2696813030749^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311786251 2500000000 2696813030749 6250000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347094041/10000000000 : ℝ), (-1021975007/5000000000 : ℝ), (1311786251/2500000000 : ℝ)] ![(4422330438397/10000000000000 : ℝ), (6313843556659/50000000000000 : ℝ), (2696813030749/6250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347094041/10000000000 : ℝ)|^275 ≤ (4422330438397/10000000000000 : ℝ)^211
        have hw : |(5347094041/10000000000 : ℝ)|=(5347094041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021975007/5000000000 : ℝ)|^275 ≤ (6313843556659/50000000000000 : ℝ)^211
        have hw : |(-1021975007/5000000000 : ℝ)|=(1021975007/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1311786251/2500000000 : ℝ)|^275 ≤ (2696813030749/6250000000000 : ℝ)^211
        have hw : |(1311786251/2500000000 : ℝ)|=(1311786251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s6_2 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (133677351/250000000 : ℝ)*x 0 + (1311786251/2500000000 : ℝ)*x 1 + (-408790003/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (133677351/250000000 : ℝ)^275 ≤ (44223304373191/100000000000000 : ℝ)^211 := by
    have hnat : (133677351 : ℕ)^275*100000000000000^211 ≤ 44223304373191^211*250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      133677351 250000000 44223304373191 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1311786251/2500000000 : ℝ)^275 ≤ (2696813030749/6250000000000 : ℝ)^211 := by
    have hnat : (1311786251 : ℕ)^275*6250000000000^211 ≤ 2696813030749^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1311786251 2500000000 2696813030749 6250000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (408790003/2000000000 : ℝ)^275 ≤ (1262768712137/10000000000000 : ℝ)^211 := by
    have hnat : (408790003 : ℕ)^275*10000000000000^211 ≤ 1262768712137^211*2000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      408790003 2000000000 1262768712137 10000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(133677351/250000000 : ℝ), (1311786251/2500000000 : ℝ), (-408790003/2000000000 : ℝ)] ![(44223304373191/100000000000000 : ℝ), (2696813030749/6250000000000 : ℝ), (1262768712137/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(133677351/250000000 : ℝ)|^275 ≤ (44223304373191/100000000000000 : ℝ)^211
        have hw : |(133677351/250000000 : ℝ)|=(133677351/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1311786251/2500000000 : ℝ)|^275 ≤ (2696813030749/6250000000000 : ℝ)^211
        have hw : |(1311786251/2500000000 : ℝ)|=(1311786251/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-408790003/2000000000 : ℝ)|^275 ≤ (1262768712137/10000000000000 : ℝ)^211
        have hw : |(-408790003/2000000000 : ℝ)|=(408790003/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s6_3 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4301630197/10000000000 : ℝ)*x 0 + (258154653/625000000 : ℝ)*x 1 + (4479109743/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301630197/10000000000 : ℝ)^275 ≤ (16652427934461/50000000000000 : ℝ)^211 := by
    have hnat : (4301630197 : ℕ)^275*50000000000000^211 ≤ 16652427934461^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301630197 10000000000 16652427934461 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (258154653/625000000 : ℝ)^275 ≤ (3158828065569/10000000000000 : ℝ)^211 := by
    have hnat : (258154653 : ℕ)^275*10000000000000^211 ≤ 3158828065569^211*625000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      258154653 625000000 3158828065569 10000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479109743/10000000000 : ℝ)^275 ≤ (35106863470437/100000000000000 : ℝ)^211 := by
    have hnat : (4479109743 : ℕ)^275*100000000000000^211 ≤ 35106863470437^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479109743 10000000000 35106863470437 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301630197/10000000000 : ℝ), (258154653/625000000 : ℝ), (4479109743/10000000000 : ℝ)] ![(16652427934461/50000000000000 : ℝ), (3158828065569/10000000000000 : ℝ), (35106863470437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301630197/10000000000 : ℝ)|^275 ≤ (16652427934461/50000000000000 : ℝ)^211
        have hw : |(4301630197/10000000000 : ℝ)|=(4301630197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(258154653/625000000 : ℝ)|^275 ≤ (3158828065569/10000000000000 : ℝ)^211
        have hw : |(258154653/625000000 : ℝ)|=(258154653/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479109743/10000000000 : ℝ)|^275 ≤ (35106863470437/100000000000000 : ℝ)^211
        have hw : |(4479109743/10000000000 : ℝ)|=(4479109743/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s6_4 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-490562699/2500000000 : ℝ)*x 0 + (2623862321/5000000000 : ℝ)*x 1 + (5407071739/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (490562699/2500000000 : ℝ)^275 ≤ (2993467619647/25000000000000 : ℝ)^211 := by
    have hnat : (490562699 : ℕ)^275*25000000000000^211 ≤ 2993467619647^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      490562699 2500000000 2993467619647 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2623862321/5000000000 : ℝ)^275 ≤ (43155220930707/100000000000000 : ℝ)^211 := by
    have hnat : (2623862321 : ℕ)^275*100000000000000^211 ≤ 43155220930707^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2623862321 5000000000 43155220930707 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407071739/10000000000 : ℝ)^275 ≤ (8974181716141/20000000000000 : ℝ)^211 := by
    have hnat : (5407071739 : ℕ)^275*20000000000000^211 ≤ 8974181716141^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407071739 10000000000 8974181716141 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-490562699/2500000000 : ℝ), (2623862321/5000000000 : ℝ), (5407071739/10000000000 : ℝ)] ![(2993467619647/25000000000000 : ℝ), (43155220930707/100000000000000 : ℝ), (8974181716141/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-490562699/2500000000 : ℝ)|^275 ≤ (2993467619647/25000000000000 : ℝ)^211
        have hw : |(-490562699/2500000000 : ℝ)|=(490562699/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2623862321/5000000000 : ℝ)|^275 ≤ (43155220930707/100000000000000 : ℝ)^211
        have hw : |(2623862321/5000000000 : ℝ)|=(2623862321/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407071739/10000000000 : ℝ)|^275 ≤ (8974181716141/20000000000000 : ℝ)^211
        have hw : |(5407071739/10000000000 : ℝ)|=(5407071739/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s6_5 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (165791293/312500000 : ℝ)*x 0 + (-7536093/40000000 : ℝ)*x 1 + (1351767951/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (165791293/312500000 : ℝ)^275 ≤ (21886782977529/50000000000000 : ℝ)^211 := by
    have hnat : (165791293 : ℕ)^275*50000000000000^211 ≤ 21886782977529^211*312500000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      165791293 312500000 21886782977529 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (7536093/40000000 : ℝ)^275 ≤ (5677762375423/50000000000000 : ℝ)^211 := by
    have hnat : (7536093 : ℕ)^275*50000000000000^211 ≤ 5677762375423^211*40000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      7536093 40000000 5677762375423 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1351767951/2500000000 : ℝ)^275 ≤ (44870909283723/100000000000000 : ℝ)^211 := by
    have hnat : (1351767951 : ℕ)^275*100000000000000^211 ≤ 44870909283723^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1351767951 2500000000 44870909283723 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(165791293/312500000 : ℝ), (-7536093/40000000 : ℝ), (1351767951/2500000000 : ℝ)] ![(21886782977529/50000000000000 : ℝ), (5677762375423/50000000000000 : ℝ), (44870909283723/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(165791293/312500000 : ℝ)|^275 ≤ (21886782977529/50000000000000 : ℝ)^211
        have hw : |(165791293/312500000 : ℝ)|=(165791293/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-7536093/40000000 : ℝ)|^275 ≤ (5677762375423/50000000000000 : ℝ)^211
        have hw : |(-7536093/40000000 : ℝ)|=(7536093/40000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1351767951/2500000000 : ℝ)|^275 ≤ (44870909283723/100000000000000 : ℝ)^211
        have hw : |(1351767951/2500000000 : ℝ)|=(1351767951/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s6_6 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5305321057/10000000000 : ℝ)*x 0 + (108141443/200000000 : ℝ)*x 1 + (-188402321/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5305321057/10000000000 : ℝ)^275 ≤ (43773562524687/100000000000000 : ℝ)^211 := by
    have hnat : (5305321057 : ℕ)^275*100000000000000^211 ≤ 43773562524687^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5305321057 10000000000 43773562524687 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (108141443/200000000 : ℝ)^275 ≤ (44870913025941/100000000000000 : ℝ)^211 := by
    have hnat : (108141443 : ℕ)^275*100000000000000^211 ≤ 44870913025941^211*200000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      108141443 200000000 44870913025941 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (188402321/1000000000 : ℝ)^275 ≤ (2838881109157/25000000000000 : ℝ)^211 := by
    have hnat : (188402321 : ℕ)^275*25000000000000^211 ≤ 2838881109157^211*1000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      188402321 1000000000 2838881109157 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5305321057/10000000000 : ℝ), (108141443/200000000 : ℝ), (-188402321/1000000000 : ℝ)] ![(43773562524687/100000000000000 : ℝ), (44870913025941/100000000000000 : ℝ), (2838881109157/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5305321057/10000000000 : ℝ)|^275 ≤ (43773562524687/100000000000000 : ℝ)^211
        have hw : |(5305321057/10000000000 : ℝ)|=(5305321057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(108141443/200000000 : ℝ)|^275 ≤ (44870913025941/100000000000000 : ℝ)^211
        have hw : |(108141443/200000000 : ℝ)|=(108141443/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-188402321/1000000000 : ℝ)|^275 ≤ (2838881109157/25000000000000 : ℝ)^211
        have hw : |(-188402321/1000000000 : ℝ)|=(188402321/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s6_7 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4301654441/10000000000 : ℝ)*x 0 + (1119462791/2500000000 : ℝ)*x 1 + (826347937/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4301654441/10000000000 : ℝ)^275 ≤ (16652550254997/50000000000000 : ℝ)^211 := by
    have hnat : (4301654441 : ℕ)^275*50000000000000^211 ≤ 16652550254997^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4301654441 10000000000 16652550254997 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1119462791/2500000000 : ℝ)^275 ≤ (35094007272869/100000000000000 : ℝ)^211 := by
    have hnat : (1119462791 : ℕ)^275*100000000000000^211 ≤ 35094007272869^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1119462791 2500000000 35094007272869 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (826347937/2000000000 : ℝ)^275 ≤ (6320178440429/20000000000000 : ℝ)^211 := by
    have hnat : (826347937 : ℕ)^275*20000000000000^211 ≤ 6320178440429^211*2000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      826347937 2000000000 6320178440429 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4301654441/10000000000 : ℝ), (1119462791/2500000000 : ℝ), (826347937/2000000000 : ℝ)] ![(16652550254997/50000000000000 : ℝ), (35094007272869/100000000000000 : ℝ), (6320178440429/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4301654441/10000000000 : ℝ)|^275 ≤ (16652550254997/50000000000000 : ℝ)^211
        have hw : |(4301654441/10000000000 : ℝ)|=(4301654441/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1119462791/2500000000 : ℝ)|^275 ≤ (35094007272869/100000000000000 : ℝ)^211
        have hw : |(1119462791/2500000000 : ℝ)|=(1119462791/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(826347937/2000000000 : ℝ)|^275 ≤ (6320178440429/20000000000000 : ℝ)^211
        have hw : |(826347937/2000000000 : ℝ)|=(826347937/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1440_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5681/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14763/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11359/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7383/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11359/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7383/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11359/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11359/100000 : ℝ) ^ (4399/1024 : ℝ) ≤ (8746554561989969/100000000000000000000 : ℝ) := by
    have hpowers : (11359/100000 : ℝ)^4399 ≤ (8746554561989969/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11359 : ℕ)^4399*100000000000000000000^1024 ≤ 8746554561989969^1024*100000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11359 100000 8746554561989969 100000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11359/100000 : ℝ)) (X := (8746554561989969/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7383/50000 : ℝ) ^ (4399/1024 : ℝ) ≤ (5398431953493289/20000000000000000000 : ℝ) := by
    have hpowers : (7383/50000 : ℝ)^4399 ≤ (5398431953493289/20000000000000000000 : ℝ)^1024 := by
      have hnat : (7383 : ℕ)^4399*20000000000000000000^1024 ≤ 5398431953493289^1024*50000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7383 50000 5398431953493289 20000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7383/50000 : ℝ)) (X := (5398431953493289/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008746554561989969/50000000000000000000 : ℝ) ≤ (2500101794395393/2500000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (50008746554561989969/50000000000000000000 : ℝ)^1024 ≤ (2500101794395393/2500000000000000 : ℝ)^4399 := by
      have hnat : (50008746554561989969 : ℕ)^1024*2500000000000000^4399 ≤ 2500101794395393^4399*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008746554561989969 50000000000000000000 2500101794395393 2500000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500101794395393/2500000000000000 : ℝ)) (X := (50008746554561989969/50000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (50017869357164728207/50000000000000000000 : ℝ) ≤ (2500207953098759/2500000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (50017869357164728207/50000000000000000000 : ℝ)^1024 ≤ (2500207953098759/2500000000000000 : ℝ)^4399 := by
      have hnat : (50017869357164728207 : ℕ)^1024*2500000000000000^4399 ≤ 2500207953098759^4399*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50017869357164728207 50000000000000000000 2500207953098759 2500000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500207953098759/2500000000000000 : ℝ)) (X := (50017869357164728207/50000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (10005398431953493289/10000000000000000000 : ℝ) ≤ (20002512894417/20000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (10005398431953493289/10000000000000000000 : ℝ)^1024 ≤ (20002512894417/20000000000000 : ℝ)^4399 := by
      have hnat : (10005398431953493289 : ℕ)^1024*20000000000000^4399 ≤ 20002512894417^4399*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10005398431953493289 10000000000000000000 20002512894417 20000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (20002512894417/20000000000000 : ℝ)) (X := (10005398431953493289/10000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8746554561989969/100000000000000000000 : ℝ) ≤ ((8515435100082035163/8517500000000000000 : ℝ)+2*(53079351683/42587500000000 : ℝ)*(11359/100000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (8515435100082035163/8517500000000000000 : ℝ)+2*(53079351683/42587500000000 : ℝ)*(11359/100000 : ℝ)=(2500101794395393/2500000000000000 : ℝ) by norm_num, show 1+2*(8746554561989969/100000000000000000000 : ℝ)=(50008746554561989969/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(5398431953493289/20000000000000000000 : ℝ)+(8746554561989969/100000000000000000000 : ℝ) ≤ ((8515435100082035163/8517500000000000000 : ℝ)+(53079351683/42587500000000 : ℝ)*((7383/50000 : ℝ)+(11359/100000 : ℝ)))^(4399/1024 : ℝ) := by
    rw [show (8515435100082035163/8517500000000000000 : ℝ)+(53079351683/42587500000000 : ℝ)*((7383/50000 : ℝ)+(11359/100000 : ℝ))=(2500207953098759/2500000000000000 : ℝ) by norm_num, show 1+(5398431953493289/20000000000000000000 : ℝ)+(8746554561989969/100000000000000000000 : ℝ)=(50017869357164728207/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(5398431953493289/20000000000000000000 : ℝ) ≤ ((8515435100082035163/8517500000000000000 : ℝ)+2*(53079351683/42587500000000 : ℝ)*(7383/50000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (8515435100082035163/8517500000000000000 : ℝ)+2*(53079351683/42587500000000 : ℝ)*(7383/50000 : ℝ)=(20002512894417/20000000000000 : ℝ) by norm_num, show 1+2*(5398431953493289/20000000000000000000 : ℝ)=(10005398431953493289/10000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (8515435100082035163/8517500000000000000 : ℝ)*(X 1 0+X 2 0)+(53079351683/42587500000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (8515435100082035163/8517500000000000000 : ℝ)) (alpha := (53079351683/42587500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (8515435100082035163/8517500000000000000 : ℝ)*(X 0 1+X 2 1)+(53079351683/42587500000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (8515435100082035163/8517500000000000000 : ℝ)) (alpha := (53079351683/42587500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (8515435100082035163/8517500000000000000 : ℝ)*(X 0 2+X 1 2)+(53079351683/42587500000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (11359/100000 : ℝ)) (hi := (7383/50000 : ℝ)) (c := (8515435100082035163/8517500000000000000 : ℝ)) (alpha := (53079351683/42587500000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1962239633/10000000000 : ℝ)*X 0 0+(5407654331/10000000000 : ℝ)*X 0 1+(5247145003/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s6_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347094041/10000000000 : ℝ)*X 1 0+(-1021975007/5000000000 : ℝ)*X 1 1+(1311786251/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s6_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((133677351/250000000 : ℝ)*X 2 0+(1311786251/2500000000 : ℝ)*X 2 1+(-408790003/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s6_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4301630197/10000000000 : ℝ)*X 0 0+(258154653/625000000 : ℝ)*X 0 1+(4479109743/10000000000 : ℝ)*X 0 2+(4301630197/10000000000 : ℝ)*X 1 0+(258154653/625000000 : ℝ)*X 1 1+(4479109743/10000000000 : ℝ)*X 1 2+(4301630197/10000000000 : ℝ)*X 2 0+(258154653/625000000 : ℝ)*X 2 1+(4479109743/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s6_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-490562699/2500000000 : ℝ)*X 0 0+(2623862321/5000000000 : ℝ)*X 0 1+(5407071739/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s6_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((165791293/312500000 : ℝ)*X 1 0+(-7536093/40000000 : ℝ)*X 1 1+(1351767951/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s6_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5305321057/10000000000 : ℝ)*X 2 0+(108141443/200000000 : ℝ)*X 2 1+(-188402321/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s6_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4301654441/10000000000 : ℝ)*X 0 0+(1119462791/2500000000 : ℝ)*X 0 1+(826347937/2000000000 : ℝ)*X 0 2+(4301654441/10000000000 : ℝ)*X 1 0+(1119462791/2500000000 : ℝ)*X 1 1+(826347937/2000000000 : ℝ)*X 1 2+(4301654441/10000000000 : ℝ)*X 2 0+(1119462791/2500000000 : ℝ)*X 2 1+(826347937/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s6_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (33560027849257123681293/3407000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1784596483/100000000000000 : ℝ)*(base19) + (830736181/50000000000000 : ℝ)*(base23) + (65212601/100000000000000 : ℝ)*(lower2) + (246438747/100000000000000 : ℝ)*(upper3) + (156215843/100000000000000 : ℝ)*(upper5) + (113732592308419/2500000000000 : ℝ)*(major0) + (113732592308419/2500000000000 : ℝ)*(major1) + (113732592308419/2500000000000 : ℝ)*(major2) + (623020687605423/10000000000000 : ℝ)*(sp0) + (6230242757274151/100000000000000 : ℝ)*(sp1) + (6230242880398271/100000000000000 : ℝ)*(sp2) + (286834372238239/10000000000000 : ℝ)*(sp3) + (37665816403/100000000000000 : ℝ)*(sp4) + (18792076613/100000000000000 : ℝ)*(sp7) + (2868362514459003/100000000000000 : ℝ)*(f.failure) + (6230244541870633/100000000000000 : ℝ)*(f.sum) + (7405882054833/3407000000000000000000000000 : ℝ)*base65 + (33475525253362297/21293750000000000000000000000000 : ℝ)*base67 + (131248140408874797/21293750000000000000000000000000 : ℝ)*base69 + (70603687947400203/21293750000000000000000000000000 : ℝ)*base72 + (4465605893581/1703500000000000000000000000 : ℝ)*base73 + (161595095456618953/21293750000000000000000000000000 : ℝ)*base76 + (25751155795456047/21293750000000000000000000000000 : ℝ)*base77 + (202600087757862703/21293750000000000000000000000000 : ℝ)*base80 + (569222033471/1703500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (15578689/2000000000000000000000 : ℝ)*base89 + (15578689/2000000000000000000000 : ℝ)*base91 + (15578689/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (5144616431887308698338342221/425875000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (158399653/10000000000000 : ℝ)*(base19) + (709292061/50000000000000 : ℝ)*(base23) + (486728511/100000000000000 : ℝ)*(lower1) + (70395227/25000000000000 : ℝ)*(upper3) + (79030013/100000000000000 : ℝ)*(lower4) + (129470829/100000000000000 : ℝ)*(upper5) + (4582398489029463/100000000000000 : ℝ)*(major0) + (4582398489029463/100000000000000 : ℝ)*(major1) + (4582398489029463/100000000000000 : ℝ)*(major2) + (7996541179/100000000000000 : ℝ)*(sp2) + (1255113519714067/20000000000000 : ℝ)*(sp4) + (1255113202914761/20000000000000 : ℝ)*(sp5) + (6275558183445033/100000000000000 : ℝ)*(sp6) + (361153622102283/12500000000000 : ℝ)*(sp7) + (361153622102283/12500000000000 : ℝ)*(f.failure) + (1255113519714067/20000000000000 : ℝ)*(f.sum) + (19118047744977/4258750000000000000000000000 : ℝ)*base66 + (50200941368285692531/851750000000000000000000000000000 : ℝ)*base68 + (1296365127753942531/851750000000000000000000000000000 : ℝ)*base70 + (107745862766127192531/851750000000000000000000000000000 : ℝ)*base72 + (54744026474389/8517500000000000000000000000 : ℝ)*base74 + (25920654939900192531/851750000000000000000000000000000 : ℝ)*base76 + (2151244508358942531/851750000000000000000000000000000 : ℝ)*base78 + (3108157097178692531/851750000000000000000000000000000 : ℝ)*base80 + (87297072548043/17035000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (2845329/250000000000000000000 : ℝ)*base89 + (2845329/250000000000000000000 : ℝ)*base91 + (2845329/250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1440_s6 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5681/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1440_s6 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1440_s7_0 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-196224197/1000000000 : ℝ)*x 0 + (5407633301/10000000000 : ℝ)*x 1 + (5247164493/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (196224197/1000000000 : ℝ)^275 ≤ (11973800285571/100000000000000 : ℝ)^211 := by
    have hnat : (196224197 : ℕ)^275*100000000000000^211 ≤ 11973800285571^211*1000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      196224197 1000000000 11973800285571 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407633301/10000000000 : ℝ)^275 ≤ (22438491169623/50000000000000 : ℝ)^211 := by
    have hnat : (5407633301 : ℕ)^275*50000000000000^211 ≤ 22438491169623^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407633301 10000000000 22438491169623 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5247164493/10000000000 : ℝ)^275 ≤ (5393652170953/12500000000000 : ℝ)^211 := by
    have hnat : (5247164493 : ℕ)^275*12500000000000^211 ≤ 5393652170953^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247164493 10000000000 5393652170953 12500000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-196224197/1000000000 : ℝ), (5407633301/10000000000 : ℝ), (5247164493/10000000000 : ℝ)] ![(11973800285571/100000000000000 : ℝ), (22438491169623/50000000000000 : ℝ), (5393652170953/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-196224197/1000000000 : ℝ)|^275 ≤ (11973800285571/100000000000000 : ℝ)^211
        have hw : |(-196224197/1000000000 : ℝ)|=(196224197/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407633301/10000000000 : ℝ)|^275 ≤ (22438491169623/50000000000000 : ℝ)^211
        have hw : |(5407633301/10000000000 : ℝ)|=(5407633301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5247164493/10000000000 : ℝ)|^275 ≤ (5393652170953/12500000000000 : ℝ)^211
        have hw : |(5247164493/10000000000 : ℝ)|=(5247164493/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s7_1 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5347088663/10000000000 : ℝ)*x 0 + (-1021965389/5000000000 : ℝ)*x 1 + (81986951/156250000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5347088663/10000000000 : ℝ)^275 ≤ (5527905801729/12500000000000 : ℝ)^211 := by
    have hnat : (5347088663 : ℕ)^275*12500000000000^211 ≤ 5527905801729^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5347088663 10000000000 5527905801729 12500000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1021965389/5000000000 : ℝ)^275 ≤ (6313766112631/50000000000000 : ℝ)^211 := by
    have hnat : (1021965389 : ℕ)^275*50000000000000^211 ≤ 6313766112631^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1021965389 5000000000 6313766112631 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (81986951/156250000 : ℝ)^275 ≤ (21574610671931/50000000000000 : ℝ)^211 := by
    have hnat : (81986951 : ℕ)^275*50000000000000^211 ≤ 21574610671931^211*156250000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      81986951 156250000 21574610671931 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5347088663/10000000000 : ℝ), (-1021965389/5000000000 : ℝ), (81986951/156250000 : ℝ)] ![(5527905801729/12500000000000 : ℝ), (6313766112631/50000000000000 : ℝ), (21574610671931/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5347088663/10000000000 : ℝ)|^275 ≤ (5527905801729/12500000000000 : ℝ)^211
        have hw : |(5347088663/10000000000 : ℝ)|=(5347088663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1021965389/5000000000 : ℝ)|^275 ≤ (6313766112631/50000000000000 : ℝ)^211
        have hw : |(-1021965389/5000000000 : ℝ)|=(1021965389/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(81986951/156250000 : ℝ)|^275 ≤ (21574610671931/50000000000000 : ℝ)^211
        have hw : |(81986951/156250000 : ℝ)|=(81986951/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s7_2 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2673544393/5000000000 : ℝ)*x 0 + (5247164697/10000000000 : ℝ)*x 1 + (-510982709/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2673544393/5000000000 : ℝ)^275 ≤ (2763952983729/6250000000000 : ℝ)^211 := by
    have hnat : (2673544393 : ℕ)^275*6250000000000^211 ≤ 2763952983729^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2673544393 5000000000 2763952983729 6250000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247164697/10000000000 : ℝ)^275 ≤ (43149219554019/100000000000000 : ℝ)^211 := by
    have hnat : (5247164697 : ℕ)^275*100000000000000^211 ≤ 43149219554019^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247164697 10000000000 43149219554019 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (510982709/2500000000 : ℝ)^275 ≤ (12627532692277/100000000000000 : ℝ)^211 := by
    have hnat : (510982709 : ℕ)^275*100000000000000^211 ≤ 12627532692277^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      510982709 2500000000 12627532692277 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2673544393/5000000000 : ℝ), (5247164697/10000000000 : ℝ), (-510982709/2500000000 : ℝ)] ![(2763952983729/6250000000000 : ℝ), (43149219554019/100000000000000 : ℝ), (12627532692277/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2673544393/5000000000 : ℝ)|^275 ≤ (2763952983729/6250000000000 : ℝ)^211
        have hw : |(2673544393/5000000000 : ℝ)|=(2673544393/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247164697/10000000000 : ℝ)|^275 ≤ (43149219554019/100000000000000 : ℝ)^211
        have hw : |(5247164697/10000000000 : ℝ)|=(5247164697/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-510982709/2500000000 : ℝ)|^275 ≤ (12627532692277/100000000000000 : ℝ)^211
        have hw : |(-510982709/2500000000 : ℝ)|=(510982709/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s7_3 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (860326301/2000000000 : ℝ)*x 0 + (4130519411/10000000000 : ℝ)*x 1 + (4479064579/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860326301/2000000000 : ℝ)^275 ≤ (16652434533831/50000000000000 : ℝ)^211 := by
    have hnat : (860326301 : ℕ)^275*50000000000000^211 ≤ 16652434533831^211*2000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860326301 2000000000 16652434533831 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4130519411/10000000000 : ℝ)^275 ≤ (31588728814857/100000000000000 : ℝ)^211 := by
    have hnat : (4130519411 : ℕ)^275*100000000000000^211 ≤ 31588728814857^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4130519411 10000000000 31588728814857 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4479064579/10000000000 : ℝ)^275 ≤ (4388300263491/12500000000000 : ℝ)^211 := by
    have hnat : (4479064579 : ℕ)^275*12500000000000^211 ≤ 4388300263491^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4479064579 10000000000 4388300263491 12500000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860326301/2000000000 : ℝ), (4130519411/10000000000 : ℝ), (4479064579/10000000000 : ℝ)] ![(16652434533831/50000000000000 : ℝ), (31588728814857/100000000000000 : ℝ), (4388300263491/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860326301/2000000000 : ℝ)|^275 ≤ (16652434533831/50000000000000 : ℝ)^211
        have hw : |(860326301/2000000000 : ℝ)|=(860326301/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4130519411/10000000000 : ℝ)|^275 ≤ (31588728814857/100000000000000 : ℝ)^211
        have hw : |(4130519411/10000000000 : ℝ)|=(4130519411/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4479064579/10000000000 : ℝ)|^275 ≤ (4388300263491/12500000000000 : ℝ)^211
        have hw : |(4479064579/10000000000 : ℝ)|=(4479064579/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s7_4 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-1962252877/10000000000 : ℝ)*x 0 + (5247744107/10000000000 : ℝ)*x 1 + (5407050919/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1962252877/10000000000 : ℝ)^275 ≤ (11973887028757/100000000000000 : ℝ)^211 := by
    have hnat : (1962252877 : ℕ)^275*100000000000000^211 ≤ 11973887028757^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1962252877 10000000000 11973887028757 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5247744107/10000000000 : ℝ)^275 ≤ (21577714778057/50000000000000 : ℝ)^211 := by
    have hnat : (5247744107 : ℕ)^275*50000000000000^211 ≤ 21577714778057^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5247744107 10000000000 21577714778057 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5407050919/10000000000 : ℝ)^275 ≤ (5608835424853/12500000000000 : ℝ)^211 := by
    have hnat : (5407050919 : ℕ)^275*12500000000000^211 ≤ 5608835424853^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407050919 10000000000 5608835424853 12500000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1962252877/10000000000 : ℝ), (5247744107/10000000000 : ℝ), (5407050919/10000000000 : ℝ)] ![(11973887028757/100000000000000 : ℝ), (21577714778057/50000000000000 : ℝ), (5608835424853/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1962252877/10000000000 : ℝ)|^275 ≤ (11973887028757/100000000000000 : ℝ)^211
        have hw : |(-1962252877/10000000000 : ℝ)|=(1962252877/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5247744107/10000000000 : ℝ)|^275 ≤ (21577714778057/50000000000000 : ℝ)^211
        have hw : |(5247744107/10000000000 : ℝ)|=(5247744107/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5407050919/10000000000 : ℝ)|^275 ≤ (5608835424853/12500000000000 : ℝ)^211
        have hw : |(5407050919/10000000000 : ℝ)|=(5407050919/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s7_5 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2652663347/5000000000 : ℝ)*x 0 + (-942022363/5000000000 : ℝ)*x 1 + (2703525459/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652663347/5000000000 : ℝ)^275 ≤ (43773623142263/100000000000000 : ℝ)^211 := by
    have hnat : (2652663347 : ℕ)^275*100000000000000^211 ≤ 43773623142263^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652663347 5000000000 43773623142263 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (942022363/5000000000 : ℝ)^275 ≤ (2838923363707/25000000000000 : ℝ)^211 := by
    have hnat : (942022363 : ℕ)^275*25000000000000^211 ≤ 2838923363707^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942022363 5000000000 2838923363707 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2703525459/5000000000 : ℝ)^275 ≤ (44870683388009/100000000000000 : ℝ)^211 := by
    have hnat : (2703525459 : ℕ)^275*100000000000000^211 ≤ 44870683388009^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2703525459 5000000000 44870683388009 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652663347/5000000000 : ℝ), (-942022363/5000000000 : ℝ), (2703525459/5000000000 : ℝ)] ![(43773623142263/100000000000000 : ℝ), (2838923363707/25000000000000 : ℝ), (44870683388009/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652663347/5000000000 : ℝ)|^275 ≤ (43773623142263/100000000000000 : ℝ)^211
        have hw : |(2652663347/5000000000 : ℝ)|=(2652663347/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-942022363/5000000000 : ℝ)|^275 ≤ (2838923363707/25000000000000 : ℝ)^211
        have hw : |(-942022363/5000000000 : ℝ)|=(942022363/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2703525459/5000000000 : ℝ)|^275 ≤ (44870683388009/100000000000000 : ℝ)^211
        have hw : |(2703525459/5000000000 : ℝ)|=(2703525459/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s7_6 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2652663351/5000000000 : ℝ)*x 0 + (5407050927/10000000000 : ℝ)*x 1 + (-942022351/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652663351/5000000000 : ℝ)^275 ≤ (43773623228291/100000000000000 : ℝ)^211 := by
    have hnat : (2652663351 : ℕ)^275*100000000000000^211 ≤ 43773623228291^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652663351 5000000000 43773623228291 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5407050927/10000000000 : ℝ)^275 ≤ (897413669707/2000000000000 : ℝ)^211 := by
    have hnat : (5407050927 : ℕ)^275*2000000000000^211 ≤ 897413669707^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5407050927 10000000000 897413669707 2000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (942022351/5000000000 : ℝ)^275 ≤ (11355693266297/100000000000000 : ℝ)^211 := by
    have hnat : (942022351 : ℕ)^275*100000000000000^211 ≤ 11355693266297^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      942022351 5000000000 11355693266297 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652663351/5000000000 : ℝ), (5407050927/10000000000 : ℝ), (-942022351/5000000000 : ℝ)] ![(43773623228291/100000000000000 : ℝ), (897413669707/2000000000000 : ℝ), (11355693266297/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652663351/5000000000 : ℝ)|^275 ≤ (43773623228291/100000000000000 : ℝ)^211
        have hw : |(2652663351/5000000000 : ℝ)|=(2652663351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5407050927/10000000000 : ℝ)|^275 ≤ (897413669707/2000000000000 : ℝ)^211
        have hw : |(5407050927/10000000000 : ℝ)|=(5407050927/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-942022351/5000000000 : ℝ)|^275 ≤ (11355693266297/100000000000000 : ℝ)^211
        have hw : |(-942022351/5000000000 : ℝ)|=(942022351/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_s7_7 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (860331197/2000000000 : ℝ)*x 0 + (2238903451/5000000000 : ℝ)*x 1 + (4131783477/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (860331197/2000000000 : ℝ)^275 ≤ (6661023218037/20000000000000 : ℝ)^211 := by
    have hnat : (860331197 : ℕ)^275*20000000000000^211 ≤ 6661023218037^211*2000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      860331197 2000000000 6661023218037 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2238903451/5000000000 : ℝ)^275 ≤ (35093555163061/100000000000000 : ℝ)^211 := by
    have hnat : (2238903451 : ℕ)^275*100000000000000^211 ≤ 35093555163061^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2238903451 5000000000 35093555163061 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4131783477/10000000000 : ℝ)^275 ≤ (31601328730149/100000000000000 : ℝ)^211 := by
    have hnat : (4131783477 : ℕ)^275*100000000000000^211 ≤ 31601328730149^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4131783477 10000000000 31601328730149 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(860331197/2000000000 : ℝ), (2238903451/5000000000 : ℝ), (4131783477/10000000000 : ℝ)] ![(6661023218037/20000000000000 : ℝ), (35093555163061/100000000000000 : ℝ), (31601328730149/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(860331197/2000000000 : ℝ)|^275 ≤ (6661023218037/20000000000000 : ℝ)^211
        have hw : |(860331197/2000000000 : ℝ)|=(860331197/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2238903451/5000000000 : ℝ)|^275 ≤ (35093555163061/100000000000000 : ℝ)^211
        have hw : |(2238903451/5000000000 : ℝ)|=(2238903451/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4131783477/10000000000 : ℝ)|^275 ≤ (31601328730149/100000000000000 : ℝ)^211
        have hw : |(4131783477/10000000000 : ℝ)|=(4131783477/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1440_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5681/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (11363/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (7381/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5681/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5681/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5681/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14763/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5681/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5681/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14763/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5681/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (5681/50000 : ℝ) ^ (4399/1024 : ℝ) ≤ (875648254871791/10000000000000000000 : ℝ) := by
    have hpowers : (5681/50000 : ℝ)^4399 ≤ (875648254871791/10000000000000000000 : ℝ)^1024 := by
      have hnat : (5681 : ℕ)^4399*10000000000000000000^1024 ≤ 875648254871791^1024*50000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5681 50000 875648254871791 10000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5681/50000 : ℝ)) (X := (875648254871791/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (14763/100000 : ℝ) ^ (4399/1024 : ℝ) ≤ (26968609023951623/100000000000000000000 : ℝ) := by
    have hpowers : (14763/100000 : ℝ)^4399 ≤ (26968609023951623/100000000000000000000 : ℝ)^1024 := by
      have hnat : (14763 : ℕ)^4399*100000000000000000000^1024 ≤ 26968609023951623^1024*100000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14763 100000 26968609023951623 100000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14763/100000 : ℝ)) (X := (26968609023951623/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (5000875648254871791/5000000000000000000 : ℝ) ≤ (625025477482951/625000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (5000875648254871791/5000000000000000000 : ℝ)^1024 ≤ (625025477482951/625000000000000 : ℝ)^4399 := by
      have hnat : (5000875648254871791 : ℕ)^1024*625000000000000^4399 ≤ 625025477482951^4399*5000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5000875648254871791 5000000000000000000 625025477482951 625000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625025477482951/625000000000000 : ℝ)) (X := (5000875648254871791/5000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (100035725091572669533/100000000000000000000 : ℝ) ≤ (312525984230349/312500000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (100035725091572669533/100000000000000000000 : ℝ)^1024 ≤ (312525984230349/312500000000000 : ℝ)^4399 := by
      have hnat : (100035725091572669533 : ℕ)^1024*312500000000000^4399 ≤ 312525984230349^4399*100000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100035725091572669533 100000000000000000000 312525984230349 312500000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312525984230349/312500000000000 : ℝ)) (X := (100035725091572669533/100000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026968609023951623/50000000000000000000 : ℝ) ≤ (125015691887689/125000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (50026968609023951623/50000000000000000000 : ℝ)^1024 ≤ (125015691887689/125000000000000 : ℝ)^4399 := by
      have hnat : (50026968609023951623 : ℕ)^1024*125000000000000^4399 ≤ 125015691887689^4399*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026968609023951623 50000000000000000000 125015691887689 125000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125015691887689/125000000000000 : ℝ)) (X := (50026968609023951623/50000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(875648254871791/10000000000000000000 : ℝ) ≤ ((111847877260062817/111875000000000000 : ℝ)+2*(26490977747/21256250000000 : ℝ)*(5681/50000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (111847877260062817/111875000000000000 : ℝ)+2*(26490977747/21256250000000 : ℝ)*(5681/50000 : ℝ)=(625025477482951/625000000000000 : ℝ) by norm_num, show 1+2*(875648254871791/10000000000000000000 : ℝ)=(5000875648254871791/5000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26968609023951623/100000000000000000000 : ℝ)+(875648254871791/10000000000000000000 : ℝ) ≤ ((111847877260062817/111875000000000000 : ℝ)+(26490977747/21256250000000 : ℝ)*((14763/100000 : ℝ)+(5681/50000 : ℝ)))^(4399/1024 : ℝ) := by
    rw [show (111847877260062817/111875000000000000 : ℝ)+(26490977747/21256250000000 : ℝ)*((14763/100000 : ℝ)+(5681/50000 : ℝ))=(312525984230349/312500000000000 : ℝ) by norm_num, show 1+(26968609023951623/100000000000000000000 : ℝ)+(875648254871791/10000000000000000000 : ℝ)=(100035725091572669533/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26968609023951623/100000000000000000000 : ℝ) ≤ ((111847877260062817/111875000000000000 : ℝ)+2*(26490977747/21256250000000 : ℝ)*(14763/100000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (111847877260062817/111875000000000000 : ℝ)+2*(26490977747/21256250000000 : ℝ)*(14763/100000 : ℝ)=(125015691887689/125000000000000 : ℝ) by norm_num, show 1+2*(26968609023951623/100000000000000000000 : ℝ)=(50026968609023951623/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (111847877260062817/111875000000000000 : ℝ)*(X 1 0+X 2 0)+(26490977747/21256250000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (5681/50000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (111847877260062817/111875000000000000 : ℝ)) (alpha := (26490977747/21256250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (111847877260062817/111875000000000000 : ℝ)*(X 0 1+X 2 1)+(26490977747/21256250000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (5681/50000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (111847877260062817/111875000000000000 : ℝ)) (alpha := (26490977747/21256250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (111847877260062817/111875000000000000 : ℝ)*(X 0 2+X 1 2)+(26490977747/21256250000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (5681/50000 : ℝ)) (hi := (14763/100000 : ℝ)) (c := (111847877260062817/111875000000000000 : ℝ)) (alpha := (26490977747/21256250000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-196224197/1000000000 : ℝ)*X 0 0+(5407633301/10000000000 : ℝ)*X 0 1+(5247164493/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s7_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5347088663/10000000000 : ℝ)*X 1 0+(-1021965389/5000000000 : ℝ)*X 1 1+(81986951/156250000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s7_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2673544393/5000000000 : ℝ)*X 2 0+(5247164697/10000000000 : ℝ)*X 2 1+(-510982709/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s7_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((860326301/2000000000 : ℝ)*X 0 0+(4130519411/10000000000 : ℝ)*X 0 1+(4479064579/10000000000 : ℝ)*X 0 2+(860326301/2000000000 : ℝ)*X 1 0+(4130519411/10000000000 : ℝ)*X 1 1+(4479064579/10000000000 : ℝ)*X 1 2+(860326301/2000000000 : ℝ)*X 2 0+(4130519411/10000000000 : ℝ)*X 2 1+(4479064579/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s7_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1962252877/10000000000 : ℝ)*X 0 0+(5247744107/10000000000 : ℝ)*X 0 1+(5407050919/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s7_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652663347/5000000000 : ℝ)*X 1 0+(-942022363/5000000000 : ℝ)*X 1 1+(2703525459/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s7_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2652663351/5000000000 : ℝ)*X 2 0+(5407050927/10000000000 : ℝ)*X 2 1+(-942022351/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s7_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((860331197/2000000000 : ℝ)*X 0 0+(2238903451/5000000000 : ℝ)*X 0 1+(4131783477/10000000000 : ℝ)*X 0 2+(860331197/2000000000 : ℝ)*X 1 0+(2238903451/5000000000 : ℝ)*X 1 1+(4131783477/10000000000 : ℝ)*X 1 2+(860331197/2000000000 : ℝ)*X 2 0+(2238903451/5000000000 : ℝ)*X 2 1+(4131783477/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_s7_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (9759048643337951219763/3401000000000000000000000000 : ℝ) := by norm_num
    linear_combination (283451801/25000000000000 : ℝ)*(base19) + (941266683/100000000000000 : ℝ)*(base23) + (21474581/100000000000000 : ℝ)*(upper2) + (71731151/25000000000000 : ℝ)*(upper3) + (100539457/50000000000000 : ℝ)*(upper4) + (182017765246681/4000000000000 : ℝ)*(major0) + (182017765246681/4000000000000 : ℝ)*(major1) + (182017765246681/4000000000000 : ℝ)*(major2) + (6231776380235351/100000000000000 : ℝ)*(sp0) + (3115902732542133/50000000000000 : ℝ)*(sp1) + (6231805657624787/100000000000000 : ℝ)*(sp2) + (1434536010204067/50000000000000 : ℝ)*(sp3) + (755466403/2500000000000 : ℝ)*(sp4) + (9547385619/100000000000000 : ℝ)*(sp7) + (358635195974219/12500000000000 : ℝ)*(f.failure) + (623180659889147/10000000000000 : ℝ)*(f.sum) + (5609426776223/680200000000000000000000000 : ℝ)*base66 + (48215095850110337/8502500000000000000000000000000 : ℝ)*base68 + (81398465790217163/8502500000000000000000000000000 : ℝ)*base69 + (7515140434710337/8502500000000000000000000000000 : ℝ)*base72 + (135796685211/53140625000000000000000000 : ℝ)*base74 + (132304093872964663/8502500000000000000000000000000 : ℝ)*base75 + (32130406994270337/8502500000000000000000000000000 : ℝ)*base78 + (90001237651769663/8502500000000000000000000000000 : ℝ)*base79 + (5643620227843/3401000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (2334703/250000000000000000000 : ℝ)*base90 + (2334703/250000000000000000000 : ℝ)*base92 + (2334703/250000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43095197940192730560849/8502500000000000000000000000 : ℝ) := by norm_num
    linear_combination (3381231/390625000000 : ℝ)*(base19) + (927085819/100000000000000 : ℝ)*(base23) + (28367517/10000000000000 : ℝ)*(lower1) + (22652111/20000000000000 : ℝ)*(upper3) + (18212089/100000000000000 : ℝ)*(lower4) + (97517833/100000000000000 : ℝ)*(upper5) + (4583573360931209/100000000000000 : ℝ)*(major0) + (4583573360931209/100000000000000 : ℝ)*(major1) + (4583573360931209/100000000000000 : ℝ)*(major2) + (140513079/6250000000000 : ℝ)*(sp2) + (1569294203126469/25000000000000 : ℝ)*(sp4) + (6277175946910739/100000000000000 : ℝ)*(sp5) + (784646704651349/12500000000000 : ℝ)*(sp6) + (361246217550679/12500000000000 : ℝ)*(sp7) + (361246217550679/12500000000000 : ℝ)*(f.failure) + (1569294203126469/25000000000000 : ℝ)*(f.sum) + (25969258703907/4251250000000000000000000000 : ℝ)*base65 + (8494299759403090693/212562500000000000000000000000000 : ℝ)*base68 + (72144709622590693/212562500000000000000000000000000 : ℝ)*base70 + (10110867979410034307/212562500000000000000000000000000 : ℝ)*base71 + (54036306226109/8502500000000000000000000000 : ℝ)*base73 + (9906536307530034307/212562500000000000000000000000000 : ℝ)*base75 + (1764832127571159307/212562500000000000000000000000000 : ℝ)*base77 + (294761787431840693/212562500000000000000000000000000 : ℝ)*base80 + (8957732464261/2125625000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (3587723/250000000000000000000 : ℝ)*base90 + (3587723/250000000000000000000 : ℝ)*base92 + (3587723/250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1440_s7 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14763/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5681/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1440_s7 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1440_box_0 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-90118741/500000000 : ℝ)*x 0 + (1346445919/2500000000 : ℝ)*x 1 + (5385783521/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (90118741/500000000 : ℝ)^275 ≤ (41868742689/390625000000 : ℝ)^211 := by
    have hnat : (90118741 : ℕ)^275*390625000000^211 ≤ 41868742689^211*500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      90118741 500000000 41868742689 390625000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1346445919/2500000000 : ℝ)^275 ≤ (8928160352401/20000000000000 : ℝ)^211 := by
    have hnat : (1346445919 : ℕ)^275*20000000000000^211 ≤ 8928160352401^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1346445919 2500000000 8928160352401 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5385783521/10000000000 : ℝ)^275 ≤ (22320400043791/50000000000000 : ℝ)^211 := by
    have hnat : (5385783521 : ℕ)^275*50000000000000^211 ≤ 22320400043791^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385783521 10000000000 22320400043791 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-90118741/500000000 : ℝ), (1346445919/2500000000 : ℝ), (5385783521/10000000000 : ℝ)] ![(41868742689/390625000000 : ℝ), (8928160352401/20000000000000 : ℝ), (22320400043791/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-90118741/500000000 : ℝ)|^275 ≤ (41868742689/390625000000 : ℝ)^211
        have hw : |(-90118741/500000000 : ℝ)|=(90118741/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1346445919/2500000000 : ℝ)|^275 ≤ (8928160352401/20000000000000 : ℝ)^211
        have hw : |(1346445919/2500000000 : ℝ)|=(1346445919/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5385783521/10000000000 : ℝ)|^275 ≤ (22320400043791/50000000000000 : ℝ)^211
        have hw : |(5385783521/10000000000 : ℝ)|=(5385783521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_1 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1057227991/2000000000 : ℝ)*x 0 + (-969657803/5000000000 : ℝ)*x 1 + (2692891623/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1057227991/2000000000 : ℝ)^275 ≤ (21783705720929/50000000000000 : ℝ)^211 := by
    have hnat : (1057227991 : ℕ)^275*50000000000000^211 ≤ 21783705720929^211*2000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057227991 2000000000 21783705720929 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (969657803/5000000000 : ℝ)^275 ≤ (5895895710369/50000000000000 : ℝ)^211 := by
    have hnat : (969657803 : ℕ)^275*50000000000000^211 ≤ 5895895710369^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      969657803 5000000000 5895895710369 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2692891623/5000000000 : ℝ)^275 ≤ (44640797116833/100000000000000 : ℝ)^211 := by
    have hnat : (2692891623 : ℕ)^275*100000000000000^211 ≤ 44640797116833^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2692891623 5000000000 44640797116833 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1057227991/2000000000 : ℝ), (-969657803/5000000000 : ℝ), (2692891623/5000000000 : ℝ)] ![(21783705720929/50000000000000 : ℝ), (5895895710369/50000000000000 : ℝ), (44640797116833/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1057227991/2000000000 : ℝ)|^275 ≤ (21783705720929/50000000000000 : ℝ)^211
        have hw : |(1057227991/2000000000 : ℝ)|=(1057227991/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-969657803/5000000000 : ℝ)|^275 ≤ (5895895710369/50000000000000 : ℝ)^211
        have hw : |(-969657803/5000000000 : ℝ)|=(969657803/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2692891623/5000000000 : ℝ)|^275 ≤ (44640797116833/100000000000000 : ℝ)^211
        have hw : |(2692891623/5000000000 : ℝ)|=(2692891623/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_2 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (211445583/400000000 : ℝ)*x 0 + (5385783339/10000000000 : ℝ)*x 1 + (-387863199/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (211445583/400000000 : ℝ)^275 ≤ (43567407360009/100000000000000 : ℝ)^211 := by
    have hnat : (211445583 : ℕ)^275*100000000000000^211 ≤ 43567407360009^211*400000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      211445583 400000000 43567407360009 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5385783339/10000000000 : ℝ)^275 ≤ (44640798121487/100000000000000 : ℝ)^211 := by
    have hnat : (5385783339 : ℕ)^275*100000000000000^211 ≤ 44640798121487^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5385783339 10000000000 44640798121487 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (387863199/2000000000 : ℝ)^275 ≤ (11791794503437/100000000000000 : ℝ)^211 := by
    have hnat : (387863199 : ℕ)^275*100000000000000^211 ≤ 11791794503437^211*2000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      387863199 2000000000 11791794503437 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(211445583/400000000 : ℝ), (5385783339/10000000000 : ℝ), (-387863199/2000000000 : ℝ)] ![(43567407360009/100000000000000 : ℝ), (44640798121487/100000000000000 : ℝ), (11791794503437/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(211445583/400000000 : ℝ)|^275 ≤ (43567407360009/100000000000000 : ℝ)^211
        have hw : |(211445583/400000000 : ℝ)|=(211445583/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5385783339/10000000000 : ℝ)|^275 ≤ (44640798121487/100000000000000 : ℝ)^211
        have hw : |(5385783339/10000000000 : ℝ)|=(5385783339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-387863199/2000000000 : ℝ)|^275 ≤ (11791794503437/100000000000000 : ℝ)^211
        have hw : |(-387863199/2000000000 : ℝ)|=(387863199/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_3 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4447708637/10000000000 : ℝ)*x 0 + (1058070113/2500000000 : ℝ)*x 1 + (264517563/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4447708637/10000000000 : ℝ)^275 ≤ (34786433771293/100000000000000 : ℝ)^211 := by
    have hnat : (4447708637 : ℕ)^275*100000000000000^211 ≤ 34786433771293^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4447708637 10000000000 34786433771293 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1058070113/2500000000 : ℝ)^275 ≤ (6521356063099/20000000000000 : ℝ)^211 := by
    have hnat : (1058070113 : ℕ)^275*20000000000000^211 ≤ 6521356063099^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1058070113 2500000000 6521356063099 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (264517563/625000000 : ℝ)^275 ≤ (32606785898377/100000000000000 : ℝ)^211 := by
    have hnat : (264517563 : ℕ)^275*100000000000000^211 ≤ 32606785898377^211*625000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      264517563 625000000 32606785898377 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4447708637/10000000000 : ℝ), (1058070113/2500000000 : ℝ), (264517563/625000000 : ℝ)] ![(34786433771293/100000000000000 : ℝ), (6521356063099/20000000000000 : ℝ), (32606785898377/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4447708637/10000000000 : ℝ)|^275 ≤ (34786433771293/100000000000000 : ℝ)^211
        have hw : |(4447708637/10000000000 : ℝ)|=(4447708637/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1058070113/2500000000 : ℝ)|^275 ≤ (6521356063099/20000000000000 : ℝ)^211
        have hw : |(1058070113/2500000000 : ℝ)|=(1058070113/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(264517563/625000000 : ℝ)|^275 ≤ (32606785898377/100000000000000 : ℝ)^211
        have hw : |(264517563/625000000 : ℝ)|=(264517563/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_4 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-531210433/2500000000 : ℝ)*x 0 + (5266684989/10000000000 : ℝ)*x 1 + (5266685123/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (531210433/2500000000 : ℝ)^275 ≤ (3320725324967/25000000000000 : ℝ)^211 := by
    have hnat : (531210433 : ℕ)^275*25000000000000^211 ≤ 3320725324967^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      531210433 2500000000 3320725324967 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5266684989/10000000000 : ℝ)^275 ≤ (43358548623951/100000000000000 : ℝ)^211 := by
    have hnat : (5266684989 : ℕ)^275*100000000000000^211 ≤ 43358548623951^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266684989 10000000000 43358548623951 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266685123/10000000000 : ℝ)^275 ≤ (43358550061731/100000000000000 : ℝ)^211 := by
    have hnat : (5266685123 : ℕ)^275*100000000000000^211 ≤ 43358550061731^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266685123 10000000000 43358550061731 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-531210433/2500000000 : ℝ), (5266684989/10000000000 : ℝ), (5266685123/10000000000 : ℝ)] ![(3320725324967/25000000000000 : ℝ), (43358548623951/100000000000000 : ℝ), (43358550061731/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-531210433/2500000000 : ℝ)|^275 ≤ (3320725324967/25000000000000 : ℝ)^211
        have hw : |(-531210433/2500000000 : ℝ)|=(531210433/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5266684989/10000000000 : ℝ)|^275 ≤ (43358548623951/100000000000000 : ℝ)^211
        have hw : |(5266684989/10000000000 : ℝ)|=(5266684989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266685123/10000000000 : ℝ)|^275 ≤ (43358550061731/100000000000000 : ℝ)^211
        have hw : |(5266685123/10000000000 : ℝ)|=(5266685123/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_5 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (134236333/250000000 : ℝ)*x 0 + (-1987739521/10000000000 : ℝ)*x 1 + (5266685049/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134236333/250000000 : ℝ)^275 ≤ (22232235298859/50000000000000 : ℝ)^211 := by
    have hnat : (134236333 : ℕ)^275*50000000000000^211 ≤ 22232235298859^211*250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134236333 250000000 22232235298859 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1987739521/10000000000 : ℝ)^275 ≤ (2435396023979/20000000000000 : ℝ)^211 := by
    have hnat : (1987739521 : ℕ)^275*20000000000000^211 ≤ 2435396023979^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987739521 10000000000 2435396023979 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5266685049/10000000000 : ℝ)^275 ≤ (43358549267733/100000000000000 : ℝ)^211 := by
    have hnat : (5266685049 : ℕ)^275*100000000000000^211 ≤ 43358549267733^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5266685049 10000000000 43358549267733 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134236333/250000000 : ℝ), (-1987739521/10000000000 : ℝ), (5266685049/10000000000 : ℝ)] ![(22232235298859/50000000000000 : ℝ), (2435396023979/20000000000000 : ℝ), (43358549267733/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134236333/250000000 : ℝ)|^275 ≤ (22232235298859/50000000000000 : ℝ)^211
        have hw : |(134236333/250000000 : ℝ)|=(134236333/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1987739521/10000000000 : ℝ)|^275 ≤ (2435396023979/20000000000000 : ℝ)^211
        have hw : |(-1987739521/10000000000 : ℝ)|=(1987739521/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5266685049/10000000000 : ℝ)|^275 ≤ (43358549267733/100000000000000 : ℝ)^211
        have hw : |(5266685049/10000000000 : ℝ)|=(5266685049/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_6 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (2684726587/5000000000 : ℝ)*x 0 + (210667403/400000000 : ℝ)*x 1 + (-1987739683/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2684726587/5000000000 : ℝ)^275 ≤ (11116117255493/25000000000000 : ℝ)^211 := by
    have hnat : (2684726587 : ℕ)^275*25000000000000^211 ≤ 11116117255493^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2684726587 5000000000 11116117255493 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (210667403/400000000 : ℝ)^275 ≤ (8671709909341/20000000000000 : ℝ)^211 := by
    have hnat : (210667403 : ℕ)^275*20000000000000^211 ≤ 8671709909341^211*400000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      210667403 400000000 8671709909341 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1987739683/10000000000 : ℝ)^275 ≤ (3044245353333/25000000000000 : ℝ)^211 := by
    have hnat : (1987739683 : ℕ)^275*25000000000000^211 ≤ 3044245353333^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1987739683 10000000000 3044245353333 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2684726587/5000000000 : ℝ), (210667403/400000000 : ℝ), (-1987739683/10000000000 : ℝ)] ![(11116117255493/25000000000000 : ℝ), (8671709909341/20000000000000 : ℝ), (3044245353333/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2684726587/5000000000 : ℝ)|^275 ≤ (11116117255493/25000000000000 : ℝ)^211
        have hw : |(2684726587/5000000000 : ℝ)|=(2684726587/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(210667403/400000000 : ℝ)|^275 ≤ (8671709909341/20000000000000 : ℝ)^211
        have hw : |(210667403/400000000 : ℝ)|=(210667403/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1987739683/10000000000 : ℝ)|^275 ≤ (3044245353333/25000000000000 : ℝ)^211
        have hw : |(-1987739683/10000000000 : ℝ)|=(1987739683/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_7 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4154491893/10000000000 : ℝ)*x 0 + (1094709589/2500000000 : ℝ)*x 1 + (4378838693/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4154491893/10000000000 : ℝ)^275 ≤ (31827879869999/100000000000000 : ℝ)^211 := by
    have hnat : (4154491893 : ℕ)^275*100000000000000^211 ≤ 31827879869999^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4154491893 10000000000 31827879869999 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1094709589/2500000000 : ℝ)^275 ≤ (34086058350551/100000000000000 : ℝ)^211 := by
    have hnat : (1094709589 : ℕ)^275*100000000000000^211 ≤ 34086058350551^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1094709589 2500000000 34086058350551 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4378838693/10000000000 : ℝ)^275 ≤ (34086061769543/100000000000000 : ℝ)^211 := by
    have hnat : (4378838693 : ℕ)^275*100000000000000^211 ≤ 34086061769543^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4378838693 10000000000 34086061769543 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4154491893/10000000000 : ℝ), (1094709589/2500000000 : ℝ), (4378838693/10000000000 : ℝ)] ![(31827879869999/100000000000000 : ℝ), (34086058350551/100000000000000 : ℝ), (34086061769543/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4154491893/10000000000 : ℝ)|^275 ≤ (31827879869999/100000000000000 : ℝ)^211
        have hw : |(4154491893/10000000000 : ℝ)|=(4154491893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1094709589/2500000000 : ℝ)|^275 ≤ (34086058350551/100000000000000 : ℝ)^211
        have hw : |(1094709589/2500000000 : ℝ)|=(1094709589/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4378838693/10000000000 : ℝ)|^275 ≤ (34086061769543/100000000000000 : ℝ)^211
        have hw : |(4378838693/10000000000 : ℝ)|=(4378838693/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_8 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-514224221/2500000000 : ℝ)*x 0 + (5184256629/10000000000 : ℝ)*x 1 + (1079950099/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (514224221/2500000000 : ℝ)^275 ≤ (636601765617/5000000000000 : ℝ)^211 := by
    have hnat : (514224221 : ℕ)^275*5000000000000^211 ≤ 636601765617^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      514224221 2500000000 636601765617 5000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5184256629/10000000000 : ℝ)^275 ≤ (2123811195391/5000000000000 : ℝ)^211 := by
    have hnat : (5184256629 : ℕ)^275*5000000000000^211 ≤ 2123811195391^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5184256629 10000000000 2123811195391 5000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1079950099/2000000000 : ℝ)^275 ≤ (44791740770427/100000000000000 : ℝ)^211 := by
    have hnat : (1079950099 : ℕ)^275*100000000000000^211 ≤ 44791740770427^211*2000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1079950099 2000000000 44791740770427 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-514224221/2500000000 : ℝ), (5184256629/10000000000 : ℝ), (1079950099/2000000000 : ℝ)] ![(636601765617/5000000000000 : ℝ), (2123811195391/5000000000000 : ℝ), (44791740770427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-514224221/2500000000 : ℝ)|^275 ≤ (636601765617/5000000000000 : ℝ)^211
        have hw : |(-514224221/2500000000 : ℝ)|=(514224221/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5184256629/10000000000 : ℝ)|^275 ≤ (2123811195391/5000000000000 : ℝ)^211
        have hw : |(5184256629/10000000000 : ℝ)|=(5184256629/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1079950099/2000000000 : ℝ)|^275 ≤ (44791740770427/100000000000000 : ℝ)^211
        have hw : |(1079950099/2000000000 : ℝ)|=(1079950099/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_9 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (5276365127/10000000000 : ℝ)*x 0 + (-483377881/2500000000 : ℝ)*x 1 + (5399750479/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5276365127/10000000000 : ℝ)^275 ≤ (2716402659561/6250000000000 : ℝ)^211 := by
    have hnat : (5276365127 : ℕ)^275*6250000000000^211 ≤ 2716402659561^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5276365127 10000000000 2716402659561 6250000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (483377881/2500000000 : ℝ)^275 ≤ (5872908420419/50000000000000 : ℝ)^211 := by
    have hnat : (483377881 : ℕ)^275*50000000000000^211 ≤ 5872908420419^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      483377881 2500000000 5872908420419 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5399750479/10000000000 : ℝ)^275 ≤ (5598967574681/12500000000000 : ℝ)^211 := by
    have hnat : (5399750479 : ℕ)^275*12500000000000^211 ≤ 5598967574681^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399750479 10000000000 5598967574681 12500000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5276365127/10000000000 : ℝ), (-483377881/2500000000 : ℝ), (5399750479/10000000000 : ℝ)] ![(2716402659561/6250000000000 : ℝ), (5872908420419/50000000000000 : ℝ), (5598967574681/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5276365127/10000000000 : ℝ)|^275 ≤ (2716402659561/6250000000000 : ℝ)^211
        have hw : |(5276365127/10000000000 : ℝ)|=(5276365127/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-483377881/2500000000 : ℝ)|^275 ≤ (5872908420419/50000000000000 : ℝ)^211
        have hw : |(-483377881/2500000000 : ℝ)|=(483377881/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5399750479/10000000000 : ℝ)|^275 ≤ (5598967574681/12500000000000 : ℝ)^211
        have hw : |(5399750479/10000000000 : ℝ)|=(5399750479/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_10 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (1319091277/2500000000 : ℝ)*x 0 + (539975049/1000000000 : ℝ)*x 1 + (-966755767/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1319091277/2500000000 : ℝ)^275 ≤ (21731221174499/50000000000000 : ℝ)^211 := by
    have hnat : (1319091277 : ℕ)^275*50000000000000^211 ≤ 21731221174499^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1319091277 2500000000 21731221174499 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (539975049/1000000000 : ℝ)^275 ≤ (44791740716371/100000000000000 : ℝ)^211 := by
    have hnat : (539975049 : ℕ)^275*100000000000000^211 ≤ 44791740716371^211*1000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      539975049 1000000000 44791740716371 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (966755767/5000000000 : ℝ)^275 ≤ (11745816920013/100000000000000 : ℝ)^211 := by
    have hnat : (966755767 : ℕ)^275*100000000000000^211 ≤ 11745816920013^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      966755767 5000000000 11745816920013 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1319091277/2500000000 : ℝ), (539975049/1000000000 : ℝ), (-966755767/5000000000 : ℝ)] ![(21731221174499/50000000000000 : ℝ), (44791740716371/100000000000000 : ℝ), (11745816920013/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1319091277/2500000000 : ℝ)|^275 ≤ (21731221174499/50000000000000 : ℝ)^211
        have hw : |(1319091277/2500000000 : ℝ)|=(1319091277/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(539975049/1000000000 : ℝ)|^275 ≤ (44791740716371/100000000000000 : ℝ)^211
        have hw : |(539975049/1000000000 : ℝ)|=(539975049/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-966755767/5000000000 : ℝ)|^275 ≤ (11745816920013/100000000000000 : ℝ)^211
        have hw : |(-966755767/5000000000 : ℝ)|=(966755767/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_11 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4481537989/10000000000 : ℝ)*x 0 + (4215079037/10000000000 : ℝ)*x 1 + (1053769751/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4481537989/10000000000 : ℝ)^275 ≤ (17565835369507/50000000000000 : ℝ)^211 := by
    have hnat : (4481537989 : ℕ)^275*50000000000000^211 ≤ 17565835369507^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4481537989 10000000000 17565835369507 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4215079037/10000000000 : ℝ)^275 ≤ (16217082394023/50000000000000 : ℝ)^211 := by
    have hnat : (4215079037 : ℕ)^275*50000000000000^211 ≤ 16217082394023^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4215079037 10000000000 16217082394023 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1053769751/2500000000 : ℝ)^275 ≤ (32434164457097/100000000000000 : ℝ)^211 := by
    have hnat : (1053769751 : ℕ)^275*100000000000000^211 ≤ 32434164457097^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1053769751 2500000000 32434164457097 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4481537989/10000000000 : ℝ), (4215079037/10000000000 : ℝ), (1053769751/2500000000 : ℝ)] ![(17565835369507/50000000000000 : ℝ), (16217082394023/50000000000000 : ℝ), (32434164457097/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4481537989/10000000000 : ℝ)|^275 ≤ (17565835369507/50000000000000 : ℝ)^211
        have hw : |(4481537989/10000000000 : ℝ)|=(4481537989/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4215079037/10000000000 : ℝ)|^275 ≤ (16217082394023/50000000000000 : ℝ)^211
        have hw : |(4215079037/10000000000 : ℝ)|=(4215079037/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1053769751/2500000000 : ℝ)|^275 ≤ (32434164457097/100000000000000 : ℝ)^211
        have hw : |(1053769751/2500000000 : ℝ)|=(1053769751/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_12 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (-233810203/1250000000 : ℝ)*x 0 + (2733104777/5000000000 : ℝ)*x 1 + (2627776939/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (233810203/1250000000 : ℝ)^275 ≤ (1124926530583/10000000000000 : ℝ)^211 := by
    have hnat : (233810203 : ℕ)^275*10000000000000^211 ≤ 1124926530583^211*1250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      233810203 1250000000 1124926530583 10000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2733104777/5000000000 : ℝ)^275 ≤ (22755790625777/50000000000000 : ℝ)^211 := by
    have hnat : (2733104777 : ℕ)^275*50000000000000^211 ≤ 22755790625777^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2733104777 5000000000 22755790625777 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2627776939/5000000000 : ℝ)^275 ≤ (8647830685737/20000000000000 : ℝ)^211 := by
    have hnat : (2627776939 : ℕ)^275*20000000000000^211 ≤ 8647830685737^211*5000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2627776939 5000000000 8647830685737 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-233810203/1250000000 : ℝ), (2733104777/5000000000 : ℝ), (2627776939/5000000000 : ℝ)] ![(1124926530583/10000000000000 : ℝ), (22755790625777/50000000000000 : ℝ), (8647830685737/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-233810203/1250000000 : ℝ)|^275 ≤ (1124926530583/10000000000000 : ℝ)^211
        have hw : |(-233810203/1250000000 : ℝ)|=(233810203/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2733104777/5000000000 : ℝ)|^275 ≤ (22755790625777/50000000000000 : ℝ)^211
        have hw : |(2733104777/5000000000 : ℝ)|=(2733104777/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2627776939/5000000000 : ℝ)|^275 ≤ (8647830685737/20000000000000 : ℝ)^211
        have hw : |(2627776939/5000000000 : ℝ)|=(2627776939/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_13 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (168038701/312500000 : ℝ)*x 0 + (-1992165981/10000000000 : ℝ)*x 1 + (5255553951/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (168038701/312500000 : ℝ)^275 ≤ (11137128015559/25000000000000 : ℝ)^211 := by
    have hnat : (168038701 : ℕ)^275*25000000000000^211 ≤ 11137128015559^211*312500000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168038701 312500000 11137128015559 25000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1992165981/10000000000 : ℝ)^275 ≤ (6106166853237/50000000000000 : ℝ)^211 := by
    have hnat : (1992165981 : ℕ)^275*50000000000000^211 ≤ 6106166853237^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992165981 10000000000 6106166853237 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5255553951/10000000000 : ℝ)^275 ≤ (864783084229/2000000000000 : ℝ)^211 := by
    have hnat : (5255553951 : ℕ)^275*2000000000000^211 ≤ 864783084229^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5255553951 10000000000 864783084229 2000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(168038701/312500000 : ℝ), (-1992165981/10000000000 : ℝ), (5255553951/10000000000 : ℝ)] ![(11137128015559/25000000000000 : ℝ), (6106166853237/50000000000000 : ℝ), (864783084229/2000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(168038701/312500000 : ℝ)|^275 ≤ (11137128015559/25000000000000 : ℝ)^211
        have hw : |(168038701/312500000 : ℝ)|=(168038701/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1992165981/10000000000 : ℝ)|^275 ≤ (6106166853237/50000000000000 : ℝ)^211
        have hw : |(-1992165981/10000000000 : ℝ)|=(1992165981/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5255553951/10000000000 : ℝ)|^275 ≤ (864783084229/2000000000000 : ℝ)^211
        have hw : |(5255553951/10000000000 : ℝ)|=(5255553951/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_14 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (215089533/400000000 : ℝ)*x 0 + (131388851/250000000 : ℝ)*x 1 + (-1992166007/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (215089533/400000000 : ℝ)^275 ≤ (44548510906901/100000000000000 : ℝ)^211 := by
    have hnat : (215089533 : ℕ)^275*100000000000000^211 ≤ 44548510906901^211*400000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      215089533 400000000 44548510906901 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (131388851/250000000 : ℝ)^275 ≤ (43239155165781/100000000000000 : ℝ)^211 := by
    have hnat : (131388851 : ℕ)^275*100000000000000^211 ≤ 43239155165781^211*250000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131388851 250000000 43239155165781 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1992166007/10000000000 : ℝ)^275 ≤ (12212333914203/100000000000000 : ℝ)^211 := by
    have hnat : (1992166007 : ℕ)^275*100000000000000^211 ≤ 12212333914203^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1992166007 10000000000 12212333914203 100000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(215089533/400000000 : ℝ), (131388851/250000000 : ℝ), (-1992166007/10000000000 : ℝ)] ![(44548510906901/100000000000000 : ℝ), (43239155165781/100000000000000 : ℝ), (12212333914203/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(215089533/400000000 : ℝ)|^275 ≤ (44548510906901/100000000000000 : ℝ)^211
        have hw : |(215089533/400000000 : ℝ)|=(215089533/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(131388851/250000000 : ℝ)|^275 ≤ (43239155165781/100000000000000 : ℝ)^211
        have hw : |(131388851/250000000 : ℝ)|=(131388851/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1992166007/10000000000 : ℝ)|^275 ≤ (12212333914203/100000000000000 : ℝ)^211
        have hw : |(-1992166007/10000000000 : ℝ)|=(1992166007/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1440_box_15 (p : ℝ) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ)) (x : Fin 3 → ℝ) :
    (4126637553/10000000000 : ℝ)*x 0 + (4392524759/10000000000 : ℝ)*x 1 + (1098131231/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4126637553/10000000000 : ℝ)^275 ≤ (6310008534103/20000000000000 : ℝ)^211 := by
    have hnat : (4126637553 : ℕ)^275*20000000000000^211 ≤ 6310008534103^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4126637553 10000000000 6310008534103 20000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4392524759/10000000000 : ℝ)^275 ≤ (17112488907241/50000000000000 : ℝ)^211 := by
    have hnat : (4392524759 : ℕ)^275*50000000000000^211 ≤ 17112488907241^211*10000000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4392524759 10000000000 17112488907241 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1098131231/2500000000 : ℝ)^275 ≤ (17112489745027/50000000000000 : ℝ)^211 := by
    have hnat : (1098131231 : ℕ)^275*50000000000000^211 ≤ 17112489745027^211*2500000000^275 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1098131231 2500000000 17112489745027 50000000000000 275 211 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (275/64 : ℝ)) 275 211 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4126637553/10000000000 : ℝ), (4392524759/10000000000 : ℝ), (1098131231/2500000000 : ℝ)] ![(6310008534103/20000000000000 : ℝ), (17112488907241/50000000000000 : ℝ), (17112489745027/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4126637553/10000000000 : ℝ)|^275 ≤ (6310008534103/20000000000000 : ℝ)^211
        have hw : |(4126637553/10000000000 : ℝ)|=(4126637553/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4392524759/10000000000 : ℝ)|^275 ≤ (17112488907241/50000000000000 : ℝ)^211
        have hw : |(4392524759/10000000000 : ℝ)|=(4392524759/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1098131231/2500000000 : ℝ)|^275 ≤ (17112489745027/50000000000000 : ℝ)^211
        have hw : |(1098131231/2500000000 : ℝ)|=(1098131231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1440_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    -(31453/50000 : ℝ) ≤ X 0 0 ∧ X 0 0 ≤ -(11827/20000 : ℝ) ∧ (80509/100000 : ℝ) ≤ X 0 1 ∧ X 0 1 ≤ (42363/50000 : ℝ) := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (11363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (11363/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (11363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (7381/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (11363/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (11363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (7381/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (11363/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (11363/100000 : ℝ) ^ (4399/1024 : ℝ) ≤ (8759793798149881/100000000000000000000 : ℝ) := by
    have hpowers : (11363/100000 : ℝ)^4399 ≤ (8759793798149881/100000000000000000000 : ℝ)^1024 := by
      have hnat : (11363 : ℕ)^4399*100000000000000000000^1024 ≤ 8759793798149881^1024*100000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        11363 100000 8759793798149881 100000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (11363/100000 : ℝ)) (X := (8759793798149881/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hpowhi : (7381/50000 : ℝ) ^ (4399/1024 : ℝ) ≤ (26960762280501129/100000000000000000000 : ℝ) := by
    have hpowers : (7381/50000 : ℝ)^4399 ≤ (26960762280501129/100000000000000000000 : ℝ)^1024 := by
      have hnat : (7381 : ℕ)^4399*100000000000000000000^1024 ≤ 26960762280501129^1024*50000^4399 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        7381 50000 26960762280501129 100000000000000000000 4399 1024 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (7381/50000 : ℝ)) (X := (26960762280501129/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner00 : (50008759793798149881/50000000000000000000 : ℝ) ≤ (2500101948466287/2500000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (50008759793798149881/50000000000000000000 : ℝ)^1024 ≤ (2500101948466287/2500000000000000 : ℝ)^4399 := by
      have hnat : (50008759793798149881 : ℕ)^1024*2500000000000000^4399 ≤ 2500101948466287^4399*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50008759793798149881 50000000000000000000 2500101948466287 2500000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500101948466287/2500000000000000 : ℝ)) (X := (50008759793798149881/50000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner10 : (10003572055607865101/10000000000000000000 : ℝ) ≤ (156262990465981/156250000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (10003572055607865101/10000000000000000000 : ℝ)^1024 ≤ (156262990465981/156250000000000 : ℝ)^4399 := by
      have hnat : (10003572055607865101 : ℕ)^1024*156250000000000^4399 ≤ 156262990465981^4399*10000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10003572055607865101 10000000000000000000 156262990465981 156250000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (156262990465981/156250000000000 : ℝ)) (X := (10003572055607865101/10000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have hcorner11 : (50026960762280501129/50000000000000000000 : ℝ) ≤ (500062749289021/500000000000000 : ℝ) ^ (4399/1024 : ℝ) := by
    have hpowers : (50026960762280501129/50000000000000000000 : ℝ)^1024 ≤ (500062749289021/500000000000000 : ℝ)^4399 := by
      have hnat : (50026960762280501129 : ℕ)^1024*500000000000000^4399 ≤ 500062749289021^4399*50000000000000000000^1024 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50026960762280501129 50000000000000000000 500062749289021 500000000000000 1024 4399 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (500062749289021/500000000000000 : ℝ)) (X := (50026960762280501129/50000000000000000000 : ℝ)) (by norm_num) 4399 1024 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(8759793798149881/100000000000000000000 : ℝ) ≤ ((772312714763963689/772500000000000000 : ℝ)+2*(105898989409/84975000000000 : ℝ)*(11363/100000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (772312714763963689/772500000000000000 : ℝ)+2*(105898989409/84975000000000 : ℝ)*(11363/100000 : ℝ)=(2500101948466287/2500000000000000 : ℝ) by norm_num, show 1+2*(8759793798149881/100000000000000000000 : ℝ)=(50008759793798149881/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(26960762280501129/100000000000000000000 : ℝ)+(8759793798149881/100000000000000000000 : ℝ) ≤ ((772312714763963689/772500000000000000 : ℝ)+(105898989409/84975000000000 : ℝ)*((7381/50000 : ℝ)+(11363/100000 : ℝ)))^(4399/1024 : ℝ) := by
    rw [show (772312714763963689/772500000000000000 : ℝ)+(105898989409/84975000000000 : ℝ)*((7381/50000 : ℝ)+(11363/100000 : ℝ))=(156262990465981/156250000000000 : ℝ) by norm_num, show 1+(26960762280501129/100000000000000000000 : ℝ)+(8759793798149881/100000000000000000000 : ℝ)=(10003572055607865101/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(26960762280501129/100000000000000000000 : ℝ) ≤ ((772312714763963689/772500000000000000 : ℝ)+2*(105898989409/84975000000000 : ℝ)*(7381/50000 : ℝ))^(4399/1024 : ℝ) := by
    rw [show (772312714763963689/772500000000000000 : ℝ)+2*(105898989409/84975000000000 : ℝ)*(7381/50000 : ℝ)=(500062749289021/500000000000000 : ℝ) by norm_num, show 1+2*(26960762280501129/100000000000000000000 : ℝ)=(50026960762280501129/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (772312714763963689/772500000000000000 : ℝ)*(X 1 0+X 2 0)+(105898989409/84975000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (772312714763963689/772500000000000000 : ℝ)) (alpha := (105898989409/84975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (772312714763963689/772500000000000000 : ℝ)*(X 0 1+X 2 1)+(105898989409/84975000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (772312714763963689/772500000000000000 : ℝ)) (alpha := (105898989409/84975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (772312714763963689/772500000000000000 : ℝ)*(X 0 2+X 1 2)+(105898989409/84975000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (4399/1024 : ℝ)) (lo := (11363/100000 : ℝ)) (hi := (7381/50000 : ℝ)) (c := (772312714763963689/772500000000000000 : ℝ)) (alpha := (105898989409/84975000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-90118741/500000000 : ℝ)*X 0 0+(1346445919/2500000000 : ℝ)*X 0 1+(5385783521/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((1057227991/2000000000 : ℝ)*X 1 0+(-969657803/5000000000 : ℝ)*X 1 1+(2692891623/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((211445583/400000000 : ℝ)*X 2 0+(5385783339/10000000000 : ℝ)*X 2 1+(-387863199/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4447708637/10000000000 : ℝ)*X 0 0+(1058070113/2500000000 : ℝ)*X 0 1+(264517563/625000000 : ℝ)*X 0 2+(4447708637/10000000000 : ℝ)*X 1 0+(1058070113/2500000000 : ℝ)*X 1 1+(264517563/625000000 : ℝ)*X 1 2+(4447708637/10000000000 : ℝ)*X 2 0+(1058070113/2500000000 : ℝ)*X 2 1+(264517563/625000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-531210433/2500000000 : ℝ)*X 0 0+(5266684989/10000000000 : ℝ)*X 0 1+(5266685123/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((134236333/250000000 : ℝ)*X 1 0+(-1987739521/10000000000 : ℝ)*X 1 1+(5266685049/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2684726587/5000000000 : ℝ)*X 2 0+(210667403/400000000 : ℝ)*X 2 1+(-1987739683/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4154491893/10000000000 : ℝ)*X 0 0+(1094709589/2500000000 : ℝ)*X 0 1+(4378838693/10000000000 : ℝ)*X 0 2+(4154491893/10000000000 : ℝ)*X 1 0+(1094709589/2500000000 : ℝ)*X 1 1+(4378838693/10000000000 : ℝ)*X 1 2+(4154491893/10000000000 : ℝ)*X 2 0+(1094709589/2500000000 : ℝ)*X 2 1+(4378838693/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp8 : ((-514224221/2500000000 : ℝ)*X 0 0+(5184256629/10000000000 : ℝ)*X 0 1+(1079950099/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_8 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp9 : ((5276365127/10000000000 : ℝ)*X 1 0+(-483377881/2500000000 : ℝ)*X 1 1+(5399750479/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_9 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp10 : ((1319091277/2500000000 : ℝ)*X 2 0+(539975049/1000000000 : ℝ)*X 2 1+(-966755767/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_10 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp11 : ((4481537989/10000000000 : ℝ)*X 0 0+(4215079037/10000000000 : ℝ)*X 0 1+(1053769751/2500000000 : ℝ)*X 0 2+(4481537989/10000000000 : ℝ)*X 1 0+(4215079037/10000000000 : ℝ)*X 1 1+(1053769751/2500000000 : ℝ)*X 1 2+(4481537989/10000000000 : ℝ)*X 2 0+(4215079037/10000000000 : ℝ)*X 2 1+(1053769751/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_11 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp12 : ((-233810203/1250000000 : ℝ)*X 0 0+(2733104777/5000000000 : ℝ)*X 0 1+(2627776939/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_12 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp13 : ((168038701/312500000 : ℝ)*X 1 0+(-1992165981/10000000000 : ℝ)*X 1 1+(5255553951/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_13 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp14 : ((215089533/400000000 : ℝ)*X 2 0+(131388851/250000000 : ℝ)*X 2 1+(-1992166007/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_14 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp15 : ((4126637553/10000000000 : ℝ)*X 0 0+(4392524759/10000000000 : ℝ)*X 0 1+(1098131231/2500000000 : ℝ)*X 0 2+(4126637553/10000000000 : ℝ)*X 1 0+(4392524759/10000000000 : ℝ)*X 1 1+(1098131231/2500000000 : ℝ)*X 1 2+(4126637553/10000000000 : ℝ)*X 2 0+(4392524759/10000000000 : ℝ)*X 2 1+(1098131231/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1440_box_15 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  refine ⟨?_,?_,?_,?_⟩
  ·
    have hcertificate_margin : (-31453/50000 : ℝ) ≤ (-8908754060378572207601330222049/14162500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (25880559/100000000000000 : ℝ)*(upper1) + (120054301/100000000000000 : ℝ)*(lower4) + (57102031/100000000000000 : ℝ)*(upper5) + (302882179924023/10000000000000 : ℝ)*(major0) + (302882179924023/10000000000000 : ℝ)*(major1) + (302882179924023/10000000000000 : ℝ)*(major2) + (114091981/100000000000000 : ℝ)*(sp1) + (7218339241/100000000000000 : ℝ)*(sp2) + (1697589377/50000000000000 : ℝ)*(sp3) + (2084459242152339/50000000000000 : ℝ)*(sp4) + (416892161391671/10000000000000 : ℝ)*(sp5) + (4168914509669451/100000000000000 : ℝ)*(sp6) + (1909686416594279/100000000000000 : ℝ)*(sp7) + (3243704013/100000000000000 : ℝ)*(sp12) + (238711226471629/12500000000000 : ℝ)*(f.failure) + (1042230432002173/25000000000000 : ℝ)*(f.sum) + (507882750831/1133000000000000000000000000 : ℝ)*base65 + (288096578612863561/28325000000000000000000000000000 : ℝ)*base68 + (273088812771938561/28325000000000000000000000000000 : ℝ)*base70 + (135641674162663561/28325000000000000000000000000000 : ℝ)*base72 + (469255745517/141625000000000000000000000 : ℝ)*base74 + (143722909821038561/28325000000000000000000000000000 : ℝ)*base76 + (389608495892713561/28325000000000000000000000000000 : ℝ)*base78 + (408733625456363561/28325000000000000000000000000000 : ℝ)*base80 + (1819490554469/1133000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (407127/250000000000000000000 : ℝ)*base89 + (407127/250000000000000000000 : ℝ)*base91 + (407127/250000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (11827/20000 : ℝ) ≤ (41876978173998187369630555205661/70812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31244837/100000000000000 : ℝ)*(lower1) + (25106761/100000000000000 : ℝ)*(upper2) + (92030249/50000000000000 : ℝ)*(lower4) + (1816667/3125000000000 : ℝ)*(lower5) + (3100801969003941/100000000000000 : ℝ)*(major0) + (3100801969003941/100000000000000 : ℝ)*(major1) + (3100801969003941/100000000000000 : ℝ)*(major2) + (1056702826537469/25000000000000 : ℝ)*(sp0) + (6604329177717/156250000000 : ℝ)*(sp1) + (211336050181537/5000000000000 : ℝ)*(sp2) + (391014745734991/20000000000000 : ℝ)*(sp3) + (469245089/1000000000000 : ℝ)*(sp9) + (96594617039/100000000000000 : ℝ)*(sp10) + (393256119/6250000000000 : ℝ)*(sp12) + (391014745734991/20000000000000 : ℝ)*(f.failure) + (211340879912389/5000000000000 : ℝ)*(f.sum) + (6271695553357/5665000000000000000000000000 : ℝ)*base65 + (2644485704730260613/283250000000000000000000000000000 : ℝ)*base67 + (798392189288260613/283250000000000000000000000000000 : ℝ)*base69 + (1758029795245510613/283250000000000000000000000000000 : ℝ)*base71 + (546299721653/88515625000000000000000000 : ℝ)*base73 + (181002035905739387/283250000000000000000000000000000 : ℝ)*base76 + (558089319346510613/283250000000000000000000000000000 : ℝ)*base77 + (496192797711760613/283250000000000000000000000000000 : ℝ)*base79 + (8893758748659/2832500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (680067/400000000000000000000 : ℝ)*base90 + (680067/400000000000000000000 : ℝ)*base92 + (680067/400000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (80509/100000 : ℝ) ≤ (114024350342972541735942986918103/141625000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (9263717/100000000000000 : ℝ)*(upper1) + (7816379/100000000000000 : ℝ)*(upper2) + (612441/20000000000000 : ℝ)*(lower5) + (3408076546283043/100000000000000 : ℝ)*(major0) + (3408076546283043/100000000000000 : ℝ)*(major1) + (3408076546283043/100000000000000 : ℝ)*(major2) + (1195998071/25000000000000 : ℝ)*(sp1) + (362989667/6250000000000 : ℝ)*(sp2) + (1092314569/50000000000000 : ℝ)*(sp3) + (181978303/50000000000000 : ℝ)*(sp4) + (4640503434419361/100000000000000 : ℝ)*(sp8) + (4640499014383683/100000000000000 : ℝ)*(sp9) + (928099598108259/20000000000000 : ℝ)*(sp10) + (2148809957376691/100000000000000 : ℝ)*(sp11) + (214881214200583/10000000000000 : ℝ)*(f.failure) + (4640503798375967/100000000000000 : ℝ)*(f.sum) + (21726572904569/5665000000000000000000000000 : ℝ)*base66 + (1655540279032627299/283250000000000000000000000000000 : ℝ)*base67 + (1918789985321122701/283250000000000000000000000000000 : ℝ)*base70 + (2153977875942627299/283250000000000000000000000000000 : ℝ)*base71 + (29130039172361/5665000000000000000000000000 : ℝ)*base73 + (642579291772122701/283250000000000000000000000000000 : ℝ)*base76 + (895115937000877299/283250000000000000000000000000000 : ℝ)*base77 + (899876594528877299/283250000000000000000000000000000 : ℝ)*base79 + (9658444826473/2832500000000000000000000000 : ℝ)*base81 + (1688229/200000000000000000000 : ℝ)*base89 + (1688229/200000000000000000000 : ℝ)*base91 + (1688229/200000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (-42363/50000 : ℝ) ≤ (-59994752634151285683082413181389/70812500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (13488989/50000000000000 : ℝ)*(lower0) + (4320141/10000000000000 : ℝ)*(lower1) + (18994249/50000000000000 : ℝ)*(lower4) + (1722842392892109/50000000000000 : ℝ)*(major0) + (1722842392892109/50000000000000 : ℝ)*(major1) + (1722842392892109/50000000000000 : ℝ)*(major2) + (267401633/20000000000000 : ℝ)*(sp0) + (23321589057/100000000000000 : ℝ)*(sp5) + (6873074281/100000000000000 : ℝ)*(sp6) + (9718325767/100000000000000 : ℝ)*(sp7) + (4747085009161177/100000000000000 : ℝ)*(sp12) + (1186765756145071/25000000000000 : ℝ)*(sp13) + (237353973654753/5000000000000 : ℝ)*(sp14) + (1086257319028663/50000000000000 : ℝ)*(sp15) + (2172524356383093/100000000000000 : ℝ)*(f.failure) + (4747086346169341/100000000000000 : ℝ)*(f.sum) + (24214068439651/5665000000000000000000000000 : ℝ)*base65 + (1152507426009822963/141625000000000000000000000000000 : ℝ)*base68 + (1076382011708072963/141625000000000000000000000000000 : ℝ)*base70 + (1198777583609052037/141625000000000000000000000000000 : ℝ)*base71 + (32669101396809/5665000000000000000000000000 : ℝ)*base74 + (411872909745322963/141625000000000000000000000000000 : ℝ)*base76 + (819959250861802037/141625000000000000000000000000000 : ℝ)*base77 + (3420929054464947963/141625000000000000000000000000000 : ℝ)*base80 + (5195082435691/1416250000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (6358641/2000000000000000000000 : ℝ)*base90 + (6358641/2000000000000000000000 : ℝ)*base92 + (6358641/2000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1440_box (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7381/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11363/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31453/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11827/20000 : ℝ) else (80509/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42363/50000 : ℝ) := by
  exact frame_box_of_interval_base (base_rectangle_w1440_box p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1440_b2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31453/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11827/20000 : ℝ) else (80509/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42363/50000 : ℝ) := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1440_s6 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1440_s7 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1440_box p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (4399/1024 : ℝ) ≤ p) (hpb : p ≤ (275/64 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (31720563/20000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (7383/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (11359/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ j i, if j=i then -(31453/50000 : ℝ) ≤ X j i ∧ X j i ≤ -(11827/20000 : ℝ) else (80509/100000 : ℝ) ≤ X j i ∧ X j i ≤ (42363/50000 : ℝ) := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1440_b2 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
