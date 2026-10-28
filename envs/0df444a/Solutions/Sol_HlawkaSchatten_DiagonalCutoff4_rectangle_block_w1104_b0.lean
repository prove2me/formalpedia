-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1104_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:02:26.634365+00:00
-- url     : https://prove2.me/submissions/285453c1-0b35-4e52-bbd2-4cbf6a615fbd

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
theorem support_rectangle_w1104_s0_0 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-951948089/5000000000 : ℝ)*x 0 + (3031577409/5000000000 : ℝ)*x 1 + (4775647501/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (951948089/5000000000 : ℝ)^8297 ≤ (11055006255399/100000000000000 : ℝ)^6249 := by
    have hnat : (951948089 : ℕ)^8297*100000000000000^6249 ≤ 11055006255399^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      951948089 5000000000 11055006255399 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3031577409/5000000000 : ℝ)^8297 ≤ (12865360732591/25000000000000 : ℝ)^6249 := by
    have hnat : (3031577409 : ℕ)^8297*25000000000000^6249 ≤ 12865360732591^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3031577409 5000000000 12865360732591 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4775647501/10000000000 : ℝ)^8297 ≤ (37483550795827/100000000000000 : ℝ)^6249 := by
    have hnat : (4775647501 : ℕ)^8297*100000000000000^6249 ≤ 37483550795827^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775647501 10000000000 37483550795827 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-951948089/5000000000 : ℝ), (3031577409/5000000000 : ℝ), (4775647501/10000000000 : ℝ)] ![(11055006255399/100000000000000 : ℝ), (12865360732591/25000000000000 : ℝ), (37483550795827/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-951948089/5000000000 : ℝ)|^8297 ≤ (11055006255399/100000000000000 : ℝ)^6249
        have hw : |(-951948089/5000000000 : ℝ)|=(951948089/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3031577409/5000000000 : ℝ)|^8297 ≤ (12865360732591/25000000000000 : ℝ)^6249
        have hw : |(3031577409/5000000000 : ℝ)|=(3031577409/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4775647501/10000000000 : ℝ)|^8297 ≤ (37483550795827/100000000000000 : ℝ)^6249
        have hw : |(4775647501/10000000000 : ℝ)|=(4775647501/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s0_1 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (551893437/1000000000 : ℝ)*x 0 + (-660969231/2500000000 : ℝ)*x 1 + (1193911753/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (551893437/1000000000 : ℝ)^8297 ≤ (45420594551121/100000000000000 : ℝ)^6249 := by
    have hnat : (551893437 : ℕ)^8297*100000000000000^6249 ≤ 45420594551121^6249*1000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      551893437 1000000000 45420594551121 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660969231/2500000000 : ℝ)^8297 ≤ (8547929866597/50000000000000 : ℝ)^6249 := by
    have hnat : (660969231 : ℕ)^8297*50000000000000^6249 ≤ 8547929866597^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660969231 2500000000 8547929866597 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1193911753/2500000000 : ℝ)^8297 ≤ (7496709139969/20000000000000 : ℝ)^6249 := by
    have hnat : (1193911753 : ℕ)^8297*20000000000000^6249 ≤ 7496709139969^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1193911753 2500000000 7496709139969 20000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(551893437/1000000000 : ℝ), (-660969231/2500000000 : ℝ), (1193911753/2500000000 : ℝ)] ![(45420594551121/100000000000000 : ℝ), (8547929866597/50000000000000 : ℝ), (7496709139969/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(551893437/1000000000 : ℝ)|^8297 ≤ (45420594551121/100000000000000 : ℝ)^6249
        have hw : |(551893437/1000000000 : ℝ)|=(551893437/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-660969231/2500000000 : ℝ)|^8297 ≤ (8547929866597/50000000000000 : ℝ)^6249
        have hw : |(-660969231/2500000000 : ℝ)|=(660969231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1193911753/2500000000 : ℝ)|^8297 ≤ (7496709139969/20000000000000 : ℝ)^6249
        have hw : |(1193911753/2500000000 : ℝ)|=(1193911753/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s0_2 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5518933399/10000000000 : ℝ)*x 0 + (4775648047/10000000000 : ℝ)*x 1 + (-2643876903/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5518933399/10000000000 : ℝ)^8297 ≤ (11355145985207/25000000000000 : ℝ)^6249 := by
    have hnat : (5518933399 : ℕ)^8297*25000000000000^6249 ≤ 11355145985207^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518933399 10000000000 11355145985207 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4775648047/10000000000 : ℝ)^8297 ≤ (37483556485819/100000000000000 : ℝ)^6249 := by
    have hnat : (4775648047 : ℕ)^8297*100000000000000^6249 ≤ 37483556485819^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4775648047 10000000000 37483556485819 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2643876903/10000000000 : ℝ)^8297 ≤ (170958595529/1000000000000 : ℝ)^6249 := by
    have hnat : (2643876903 : ℕ)^8297*1000000000000^6249 ≤ 170958595529^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2643876903 10000000000 170958595529 1000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5518933399/10000000000 : ℝ), (4775648047/10000000000 : ℝ), (-2643876903/10000000000 : ℝ)] ![(11355145985207/25000000000000 : ℝ), (37483556485819/100000000000000 : ℝ), (170958595529/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5518933399/10000000000 : ℝ)|^8297 ≤ (11355145985207/25000000000000 : ℝ)^6249
        have hw : |(5518933399/10000000000 : ℝ)|=(5518933399/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4775648047/10000000000 : ℝ)|^8297 ≤ (37483556485819/100000000000000 : ℝ)^6249
        have hw : |(4775648047/10000000000 : ℝ)|=(4775648047/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2643876903/10000000000 : ℝ)|^8297 ≤ (170958595529/1000000000000 : ℝ)^6249
        have hw : |(-2643876903/10000000000 : ℝ)|=(2643876903/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s0_3 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (840816457/2000000000 : ℝ)*x 0 + (3122904969/10000000000 : ℝ)*x 1 + (5665289321/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (840816457/2000000000 : ℝ)^8297 ≤ (15823627829137/50000000000000 : ℝ)^6249 := by
    have hnat : (840816457 : ℕ)^8297*50000000000000^6249 ≤ 15823627829137^6249*2000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      840816457 2000000000 15823627829137 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3122904969/10000000000 : ℝ)^8297 ≤ (21325993972519/100000000000000 : ℝ)^6249 := by
    have hnat : (3122904969 : ℕ)^8297*100000000000000^6249 ≤ 21325993972519^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3122904969 10000000000 21325993972519 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5665289321/10000000000 : ℝ)^8297 ≤ (47026750353151/100000000000000 : ℝ)^6249 := by
    have hnat : (5665289321 : ℕ)^8297*100000000000000^6249 ≤ 47026750353151^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5665289321 10000000000 47026750353151 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(840816457/2000000000 : ℝ), (3122904969/10000000000 : ℝ), (5665289321/10000000000 : ℝ)] ![(15823627829137/50000000000000 : ℝ), (21325993972519/100000000000000 : ℝ), (47026750353151/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(840816457/2000000000 : ℝ)|^8297 ≤ (15823627829137/50000000000000 : ℝ)^6249
        have hw : |(840816457/2000000000 : ℝ)|=(840816457/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3122904969/10000000000 : ℝ)|^8297 ≤ (21325993972519/100000000000000 : ℝ)^6249
        have hw : |(3122904969/10000000000 : ℝ)|=(3122904969/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5665289321/10000000000 : ℝ)|^8297 ≤ (47026750353151/100000000000000 : ℝ)^6249
        have hw : |(5665289321/10000000000 : ℝ)|=(5665289321/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s0_4 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-954577743/5000000000 : ℝ)*x 0 + (4808878993/10000000000 : ℝ)*x 1 + (3014378653/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (954577743/5000000000 : ℝ)^8297 ≤ (5547785620403/50000000000000 : ℝ)^6249 := by
    have hnat : (954577743 : ℕ)^8297*50000000000000^6249 ≤ 5547785620403^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      954577743 5000000000 5547785620403 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4808878993/10000000000 : ℝ)^8297 ≤ (37830258129489/100000000000000 : ℝ)^6249 := by
    have hnat : (4808878993 : ℕ)^8297*100000000000000^6249 ≤ 37830258129489^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4808878993 10000000000 37830258129489 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3014378653/5000000000 : ℝ)^8297 ≤ (25537085306313/50000000000000 : ℝ)^6249 := by
    have hnat : (3014378653 : ℕ)^8297*50000000000000^6249 ≤ 25537085306313^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3014378653 5000000000 25537085306313 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-954577743/5000000000 : ℝ), (4808878993/10000000000 : ℝ), (3014378653/5000000000 : ℝ)] ![(5547785620403/50000000000000 : ℝ), (37830258129489/100000000000000 : ℝ), (25537085306313/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-954577743/5000000000 : ℝ)|^8297 ≤ (5547785620403/50000000000000 : ℝ)^6249
        have hw : |(-954577743/5000000000 : ℝ)|=(954577743/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4808878993/10000000000 : ℝ)|^8297 ≤ (37830258129489/100000000000000 : ℝ)^6249
        have hw : |(4808878993/10000000000 : ℝ)|=(4808878993/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3014378653/5000000000 : ℝ)|^8297 ≤ (25537085306313/50000000000000 : ℝ)^6249
        have hw : |(3014378653/5000000000 : ℝ)|=(3014378653/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s0_5 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (323080047/625000000 : ℝ)*x 0 + (-1390768297/10000000000 : ℝ)*x 1 + (241150341/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323080047/625000000 : ℝ)^8297 ≤ (2602506915463/6250000000000 : ℝ)^6249 := by
    have hnat : (323080047 : ℕ)^8297*6250000000000^6249 ≤ 2602506915463^6249*625000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323080047 625000000 2602506915463 6250000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1390768297/10000000000 : ℝ)^8297 ≤ (728570502363/10000000000000 : ℝ)^6249 := by
    have hnat : (1390768297 : ℕ)^8297*10000000000000^6249 ≤ 728570502363^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390768297 10000000000 728570502363 10000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (241150341/400000000 : ℝ)^8297 ≤ (6384273040527/12500000000000 : ℝ)^6249 := by
    have hnat : (241150341 : ℕ)^8297*12500000000000^6249 ≤ 6384273040527^6249*400000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      241150341 400000000 6384273040527 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(323080047/625000000 : ℝ), (-1390768297/10000000000 : ℝ), (241150341/400000000 : ℝ)] ![(2602506915463/6250000000000 : ℝ), (728570502363/10000000000000 : ℝ), (6384273040527/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(323080047/625000000 : ℝ)|^8297 ≤ (2602506915463/6250000000000 : ℝ)^6249
        have hw : |(323080047/625000000 : ℝ)|=(323080047/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1390768297/10000000000 : ℝ)|^8297 ≤ (728570502363/10000000000000 : ℝ)^6249
        have hw : |(-1390768297/10000000000 : ℝ)|=(1390768297/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(241150341/400000000 : ℝ)|^8297 ≤ (6384273040527/12500000000000 : ℝ)^6249
        have hw : |(241150341/400000000 : ℝ)|=(241150341/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s0_6 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5169282649/10000000000 : ℝ)*x 0 + (753594723/1250000000 : ℝ)*x 1 + (-1390766577/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5169282649/10000000000 : ℝ)^8297 ≤ (41640130936363/100000000000000 : ℝ)^6249 := by
    have hnat : (5169282649 : ℕ)^8297*100000000000000^6249 ≤ 41640130936363^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5169282649 10000000000 41640130936363 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (753594723/1250000000 : ℝ)^8297 ≤ (51074175989279/100000000000000 : ℝ)^6249 := by
    have hnat : (753594723 : ℕ)^8297*100000000000000^6249 ≤ 51074175989279^6249*1250000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      753594723 1250000000 51074175989279 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1390766577/10000000000 : ℝ)^8297 ≤ (36428465301/500000000000 : ℝ)^6249 := by
    have hnat : (1390766577 : ℕ)^8297*500000000000^6249 ≤ 36428465301^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1390766577 10000000000 36428465301 500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5169282649/10000000000 : ℝ), (753594723/1250000000 : ℝ), (-1390766577/10000000000 : ℝ)] ![(41640130936363/100000000000000 : ℝ), (51074175989279/100000000000000 : ℝ), (36428465301/500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5169282649/10000000000 : ℝ)|^8297 ≤ (41640130936363/100000000000000 : ℝ)^6249
        have hw : |(5169282649/10000000000 : ℝ)|=(5169282649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(753594723/1250000000 : ℝ)|^8297 ≤ (51074175989279/100000000000000 : ℝ)^6249
        have hw : |(753594723/1250000000 : ℝ)|=(753594723/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1390766577/10000000000 : ℝ)|^8297 ≤ (36428465301/500000000000 : ℝ)^6249
        have hw : |(-1390766577/10000000000 : ℝ)|=(1390766577/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s0_7 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (842892843/2000000000 : ℝ)*x 0 + (2799835193/5000000000 : ℝ)*x 1 + (79770657/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (842892843/2000000000 : ℝ)^8297 ≤ (15875531625607/50000000000000 : ℝ)^6249 := by
    have hnat : (842892843 : ℕ)^8297*50000000000000^6249 ≤ 15875531625607^6249*2000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      842892843 2000000000 15875531625607 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2799835193/5000000000 : ℝ)^8297 ≤ (1447028737057/3125000000000 : ℝ)^6249 := by
    have hnat : (2799835193 : ℕ)^8297*3125000000000^6249 ≤ 1447028737057^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2799835193 5000000000 1447028737057 3125000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (79770657/250000000 : ℝ)^8297 ≤ (2743002143239/12500000000000 : ℝ)^6249 := by
    have hnat : (79770657 : ℕ)^8297*12500000000000^6249 ≤ 2743002143239^6249*250000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      79770657 250000000 2743002143239 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(842892843/2000000000 : ℝ), (2799835193/5000000000 : ℝ), (79770657/250000000 : ℝ)] ![(15875531625607/50000000000000 : ℝ), (1447028737057/3125000000000 : ℝ), (2743002143239/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(842892843/2000000000 : ℝ)|^8297 ≤ (15875531625607/50000000000000 : ℝ)^6249
        have hw : |(842892843/2000000000 : ℝ)|=(842892843/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2799835193/5000000000 : ℝ)|^8297 ≤ (1447028737057/3125000000000 : ℝ)^6249
        have hw : |(2799835193/5000000000 : ℝ)|=(2799835193/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(79770657/250000000 : ℝ)|^8297 ≤ (2743002143239/12500000000000 : ℝ)^6249
        have hw : |(79770657/250000000 : ℝ)|=(79770657/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1104_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (8/3125 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27961/100000 : ℝ)*pair X 0 0 := by
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
  have base13 : ((1 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    linarith only [(f.coord 0 2).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (1037/256 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^1037 ≤ (0 : ℝ)^256 := by
      have hnat : (0 : ℕ)^1037*1^256 ≤ 0^256*1^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (1037/256 : ℝ) ≤ (38181422120317971/1562500000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^1037 ≤ (38181422120317971/1562500000000000000 : ℝ)^256 := by
      have hnat : (2 : ℕ)^1037*1562500000000000000^256 ≤ 38181422120317971^256*5^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 38181422120317971 1562500000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (38181422120317971/1562500000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (1 : ℝ)^256 ≤ (1 : ℝ)^1037 := by
      have hnat : (1 : ℕ)^256*1^1037 ≤ 1^1037*1^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (1600681422120317971/1562500000000000000 : ℝ) ≤ (10059777138190217/10000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (1600681422120317971/1562500000000000000 : ℝ)^256 ≤ (10059777138190217/10000000000000000 : ℝ)^1037 := by
      have hnat : (1600681422120317971 : ℕ)^256*10000000000000000^1037 ≤ 10059777138190217^1037*1562500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1600681422120317971 1562500000000000000 10059777138190217 10000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10059777138190217/10000000000000000 : ℝ)) (X := (1600681422120317971/1562500000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (819431422120317971/781250000000000000 : ℝ) ≤ (5059777138190217/5000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (819431422120317971/781250000000000000 : ℝ)^256 ≤ (5059777138190217/5000000000000000 : ℝ)^1037 := by
      have hnat : (819431422120317971 : ℕ)^256*5000000000000000^1037 ≤ 5059777138190217^1037*781250000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        819431422120317971 781250000000000000 5059777138190217 5000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5059777138190217/5000000000000000 : ℝ)) (X := (819431422120317971/781250000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(59777138190217/4000000000000000 : ℝ)*(0 : ℝ))^(1037/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(59777138190217/4000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(38181422120317971/1562500000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(59777138190217/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(1037/256 : ℝ) := by
    rw [show (1 : ℝ)+(59777138190217/4000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(10059777138190217/10000000000000000 : ℝ) by norm_num, show 1+(38181422120317971/1562500000000000000 : ℝ)+(0 : ℝ)=(1600681422120317971/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(38181422120317971/1562500000000000000 : ℝ) ≤ ((1 : ℝ)+2*(59777138190217/4000000000000000 : ℝ)*(2/5 : ℝ))^(1037/256 : ℝ) := by
    rw [show (1 : ℝ)+2*(59777138190217/4000000000000000 : ℝ)*(2/5 : ℝ)=(5059777138190217/5000000000000000 : ℝ) by norm_num, show 1+2*(38181422120317971/1562500000000000000 : ℝ)=(819431422120317971/781250000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(59777138190217/4000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59777138190217/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(59777138190217/4000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59777138190217/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(59777138190217/4000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (59777138190217/4000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-951948089/5000000000 : ℝ)*X 0 0+(3031577409/5000000000 : ℝ)*X 0 1+(4775647501/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((551893437/1000000000 : ℝ)*X 1 0+(-660969231/2500000000 : ℝ)*X 1 1+(1193911753/2500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5518933399/10000000000 : ℝ)*X 2 0+(4775648047/10000000000 : ℝ)*X 2 1+(-2643876903/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((840816457/2000000000 : ℝ)*X 0 0+(3122904969/10000000000 : ℝ)*X 0 1+(5665289321/10000000000 : ℝ)*X 0 2+(840816457/2000000000 : ℝ)*X 1 0+(3122904969/10000000000 : ℝ)*X 1 1+(5665289321/10000000000 : ℝ)*X 1 2+(840816457/2000000000 : ℝ)*X 2 0+(3122904969/10000000000 : ℝ)*X 2 1+(5665289321/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-954577743/5000000000 : ℝ)*X 0 0+(4808878993/10000000000 : ℝ)*X 0 1+(3014378653/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((323080047/625000000 : ℝ)*X 1 0+(-1390768297/10000000000 : ℝ)*X 1 1+(241150341/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5169282649/10000000000 : ℝ)*X 2 0+(753594723/1250000000 : ℝ)*X 2 1+(-1390766577/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((842892843/2000000000 : ℝ)*X 0 0+(2799835193/5000000000 : ℝ)*X 0 1+(79770657/250000000 : ℝ)*X 0 2+(842892843/2000000000 : ℝ)*X 1 0+(2799835193/5000000000 : ℝ)*X 1 1+(79770657/250000000 : ℝ)*X 1 2+(842892843/2000000000 : ℝ)*X 2 0+(2799835193/5000000000 : ℝ)*X 2 1+(79770657/250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (28973552934478223451849/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (64356317/100000000000000 : ℝ)*(base1) + (1253163277/100000000000000 : ℝ)*(base19) + (1044258873/100000000000000 : ℝ)*(base23) + (36126009/50000000000000 : ℝ)*(base24) + (35417869/12500000000000 : ℝ)*(upper3) + (73127245077501/12500000000000 : ℝ)*(major0) + (73127245077501/12500000000000 : ℝ)*(major1) + (73127245077501/12500000000000 : ℝ)*(major2) + (776698612737963/100000000000000 : ℝ)*(sp0) + (776699710320323/100000000000000 : ℝ)*(sp1) + (776699846972709/100000000000000 : ℝ)*(sp2) + (3146661993911/800000000000 : ℝ)*(sp3) + (1207550977/50000000000000 : ℝ)*(sp4) + (397927121/20000000000000 : ℝ)*(sp7) + (393334803230797/100000000000000 : ℝ)*(f.failure) + (1941752408709/250000000000 : ℝ)*(f.sum) + (13559560207717/25000000000000000000000000000 : ℝ)*base65 + (91450471957717/50000000000000000000000000000 : ℝ)*base67 + (114571438092283/50000000000000000000000000000 : ℝ)*base70 + (61721252992283/50000000000000000000000000000 : ℝ)*base72 + (59968121182717/25000000000000000000000000000 : ℝ)*base73 + (64595137457717/50000000000000000000000000000 : ℝ)*base75 + (16908427957717/50000000000000000000000000000 : ℝ)*base77 + (215483408607717/50000000000000000000000000000 : ℝ)*base79 + (1228718807717/25000000000000000000000000000 : ℝ)*base81 + (4802409/1250000000000000000000 : ℝ)*base90 + (4802409/1250000000000000000000 : ℝ)*base92 + (4802409/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (70780218673482785536611/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (19161793/25000000000000 : ℝ)*(base13) + (55830047/12500000000000 : ℝ)*(base23) + (221974281/100000000000000 : ℝ)*(base39) + (69489387/100000000000000 : ℝ)*(upper3) + (62071721/100000000000000 : ℝ)*(upper4) + (16131777/12500000000000 : ℝ)*(upper5) + (308722444091961/50000000000000 : ℝ)*(major0) + (308722444091961/50000000000000 : ℝ)*(major1) + (308722333104821/50000000000000 : ℝ)*(major2) + (2906713/390625000000 : ℝ)*(sp2) + (20493812367283/2500000000000 : ℝ)*(sp4) + (204938142834623/25000000000000 : ℝ)*(sp5) + (204937900638467/25000000000000 : ℝ)*(sp6) + (207568467934127/50000000000000 : ℝ)*(sp7) + (207568467934127/50000000000000 : ℝ)*(f.failure) + (819752793312773/100000000000000 : ℝ)*(f.sum) + (193682069140847/100000000000000000000000000000 : ℝ)*base65 + (488334863063843/200000000000000000000000000000 : ℝ)*base68 + (1934604349454463/200000000000000000000000000000 : ℝ)*base70 + (912548821063843/200000000000000000000000000000 : ℝ)*base72 + (132783186140847/100000000000000000000000000000 : ℝ)*base73 + (462776425454463/200000000000000000000000000000 : ℝ)*base76 + (779801264254463/200000000000000000000000000000 : ℝ)*base78 + (522534415854463/200000000000000000000000000000 : ℝ)*base80 + (580553191454463/100000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (6835581/625000000000000000000 : ℝ)*base89 + (6835581/625000000000000000000 : ℝ)*base91 + (585581/625000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1104_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (8/3125 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27961/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1104_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1104_s1_0 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-1055653397/5000000000 : ℝ)*x 0 + (571177811/1000000000 : ℝ)*x 1 + (2497110977/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1055653397/5000000000 : ℝ)^8297 ≤ (3170479285699/25000000000000 : ℝ)^6249 := by
    have hnat : (1055653397 : ℕ)^8297*25000000000000^6249 ≤ 3170479285699^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1055653397 5000000000 3170479285699 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (571177811/1000000000 : ℝ)^8297 ≤ (23769902836749/50000000000000 : ℝ)^6249 := by
    have hnat : (571177811 : ℕ)^8297*50000000000000^6249 ≤ 23769902836749^6249*1000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      571177811 1000000000 23769902836749 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2497110977/5000000000 : ℝ)^8297 ≤ (39778277170851/100000000000000 : ℝ)^6249 := by
    have hnat : (2497110977 : ℕ)^8297*100000000000000^6249 ≤ 39778277170851^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497110977 5000000000 39778277170851 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1055653397/5000000000 : ℝ), (571177811/1000000000 : ℝ), (2497110977/5000000000 : ℝ)] ![(3170479285699/25000000000000 : ℝ), (23769902836749/50000000000000 : ℝ), (39778277170851/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1055653397/5000000000 : ℝ)|^8297 ≤ (3170479285699/25000000000000 : ℝ)^6249
        have hw : |(-1055653397/5000000000 : ℝ)|=(1055653397/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(571177811/1000000000 : ℝ)|^8297 ≤ (23769902836749/50000000000000 : ℝ)^6249
        have hw : |(571177811/1000000000 : ℝ)|=(571177811/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2497110977/5000000000 : ℝ)|^8297 ≤ (39778277170851/100000000000000 : ℝ)^6249
        have hw : |(2497110977/5000000000 : ℝ)|=(2497110977/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s1_1 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5421211143/10000000000 : ℝ)*x 0 + (-1249649071/5000000000 : ℝ)*x 1 + (249711101/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5421211143/10000000000 : ℝ)^8297 ≤ (11088966479339/25000000000000 : ℝ)^6249 := by
    have hnat : (5421211143 : ℕ)^8297*25000000000000^6249 ≤ 11088966479339^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5421211143 10000000000 11088966479339 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1249649071/5000000000 : ℝ)^8297 ≤ (1983232024239/12500000000000 : ℝ)^6249 := by
    have hnat : (1249649071 : ℕ)^8297*12500000000000^6249 ≤ 1983232024239^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1249649071 5000000000 1983232024239 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (249711101/500000000 : ℝ)^8297 ≤ (7955655573763/20000000000000 : ℝ)^6249 := by
    have hnat : (249711101 : ℕ)^8297*20000000000000^6249 ≤ 7955655573763^6249*500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      249711101 500000000 7955655573763 20000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5421211143/10000000000 : ℝ), (-1249649071/5000000000 : ℝ), (249711101/500000000 : ℝ)] ![(11088966479339/25000000000000 : ℝ), (1983232024239/12500000000000 : ℝ), (7955655573763/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5421211143/10000000000 : ℝ)|^8297 ≤ (11088966479339/25000000000000 : ℝ)^6249
        have hw : |(5421211143/10000000000 : ℝ)|=(5421211143/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1249649071/5000000000 : ℝ)|^8297 ≤ (1983232024239/12500000000000 : ℝ)^6249
        have hw : |(-1249649071/5000000000 : ℝ)|=(1249649071/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(249711101/500000000 : ℝ)|^8297 ≤ (7955655573763/20000000000000 : ℝ)^6249
        have hw : |(249711101/500000000 : ℝ)|=(249711101/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s1_2 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2710606151/5000000000 : ℝ)*x 0 + (2497110449/5000000000 : ℝ)*x 1 + (-2499298057/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2710606151/5000000000 : ℝ)^8297 ≤ (44355878508023/100000000000000 : ℝ)^6249 := by
    have hnat : (2710606151 : ℕ)^8297*100000000000000^6249 ≤ 44355878508023^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2710606151 5000000000 44355878508023 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2497110449/5000000000 : ℝ)^8297 ≤ (19889133001719/50000000000000 : ℝ)^6249 := by
    have hnat : (2497110449 : ℕ)^8297*50000000000000^6249 ≤ 19889133001719^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2497110449 5000000000 19889133001719 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2499298057/10000000000 : ℝ)^8297 ≤ (396646386937/2500000000000 : ℝ)^6249 := by
    have hnat : (2499298057 : ℕ)^8297*2500000000000^6249 ≤ 396646386937^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2499298057 10000000000 396646386937 2500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2710606151/5000000000 : ℝ), (2497110449/5000000000 : ℝ), (-2499298057/10000000000 : ℝ)] ![(44355878508023/100000000000000 : ℝ), (19889133001719/50000000000000 : ℝ), (396646386937/2500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2710606151/5000000000 : ℝ)|^8297 ≤ (44355878508023/100000000000000 : ℝ)^6249
        have hw : |(2710606151/5000000000 : ℝ)|=(2710606151/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2497110449/5000000000 : ℝ)|^8297 ≤ (19889133001719/50000000000000 : ℝ)^6249
        have hw : |(2497110449/5000000000 : ℝ)|=(2497110449/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2499298057/10000000000 : ℝ)|^8297 ≤ (396646386937/2500000000000 : ℝ)^6249
        have hw : |(-2499298057/10000000000 : ℝ)|=(2499298057/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s1_3 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2160320669/5000000000 : ℝ)*x 0 + (3669862843/10000000000 : ℝ)*x 1 + (5086788197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2160320669/5000000000 : ℝ)^8297 ≤ (16408751937927/50000000000000 : ℝ)^6249 := by
    have hnat : (2160320669 : ℕ)^8297*50000000000000^6249 ≤ 16408751937927^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2160320669 5000000000 16408751937927 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3669862843/10000000000 : ℝ)^8297 ≤ (1056894051189/4000000000000 : ℝ)^6249 := by
    have hnat : (3669862843 : ℕ)^8297*4000000000000^6249 ≤ 1056894051189^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3669862843 10000000000 1056894051189 4000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5086788197/10000000000 : ℝ)^8297 ≤ (326081158641/800000000000 : ℝ)^6249 := by
    have hnat : (5086788197 : ℕ)^8297*800000000000^6249 ≤ 326081158641^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5086788197 10000000000 326081158641 800000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2160320669/5000000000 : ℝ), (3669862843/10000000000 : ℝ), (5086788197/10000000000 : ℝ)] ![(16408751937927/50000000000000 : ℝ), (1056894051189/4000000000000 : ℝ), (326081158641/800000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2160320669/5000000000 : ℝ)|^8297 ≤ (16408751937927/50000000000000 : ℝ)^6249
        have hw : |(2160320669/5000000000 : ℝ)|=(2160320669/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3669862843/10000000000 : ℝ)|^8297 ≤ (1056894051189/4000000000000 : ℝ)^6249
        have hw : |(3669862843/10000000000 : ℝ)|=(3669862843/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5086788197/10000000000 : ℝ)|^8297 ≤ (326081158641/800000000000 : ℝ)^6249
        have hw : |(5086788197/10000000000 : ℝ)|=(5086788197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s1_4 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2112167409/10000000000 : ℝ)*x 0 + (500416249/1000000000 : ℝ)*x 1 + (2850819133/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2112167409/10000000000 : ℝ)^8297 ≤ (12688781218239/100000000000000 : ℝ)^6249 := by
    have hnat : (2112167409 : ℕ)^8297*100000000000000^6249 ≤ 12688781218239^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2112167409 10000000000 12688781218239 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (500416249/1000000000 : ℝ)^8297 ≤ (39883434624561/100000000000000 : ℝ)^6249 := by
    have hnat : (500416249 : ℕ)^8297*100000000000000^6249 ≤ 39883434624561^6249*1000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      500416249 1000000000 39883434624561 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2850819133/5000000000 : ℝ)^8297 ≤ (23713892070879/50000000000000 : ℝ)^6249 := by
    have hnat : (2850819133 : ℕ)^8297*50000000000000^6249 ≤ 23713892070879^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850819133 5000000000 23713892070879 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2112167409/10000000000 : ℝ), (500416249/1000000000 : ℝ), (2850819133/5000000000 : ℝ)] ![(12688781218239/100000000000000 : ℝ), (39883434624561/100000000000000 : ℝ), (23713892070879/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2112167409/10000000000 : ℝ)|^8297 ≤ (12688781218239/100000000000000 : ℝ)^6249
        have hw : |(-2112167409/10000000000 : ℝ)|=(2112167409/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(500416249/1000000000 : ℝ)|^8297 ≤ (39883434624561/100000000000000 : ℝ)^6249
        have hw : |(500416249/1000000000 : ℝ)|=(500416249/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2850819133/5000000000 : ℝ)|^8297 ≤ (23713892070879/50000000000000 : ℝ)^6249
        have hw : |(2850819133/5000000000 : ℝ)|=(2850819133/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s1_5 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (327349813/625000000 : ℝ)*x 0 + (-179188157/1000000000 : ℝ)*x 1 + (2850819043/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (327349813/625000000 : ℝ)^8297 ≤ (42372350084869/100000000000000 : ℝ)^6249 := by
    have hnat : (327349813 : ℕ)^8297*100000000000000^6249 ≤ 42372350084869^6249*625000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      327349813 625000000 42372350084869 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (179188157/1000000000 : ℝ)^8297 ≤ (2039973548973/20000000000000 : ℝ)^6249 := by
    have hnat : (179188157 : ℕ)^8297*20000000000000^6249 ≤ 2039973548973^6249*1000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      179188157 1000000000 2039973548973 20000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2850819043/5000000000 : ℝ)^8297 ≤ (47427782153759/100000000000000 : ℝ)^6249 := by
    have hnat : (2850819043 : ℕ)^8297*100000000000000^6249 ≤ 47427782153759^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2850819043 5000000000 47427782153759 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(327349813/625000000 : ℝ), (-179188157/1000000000 : ℝ), (2850819043/5000000000 : ℝ)] ![(42372350084869/100000000000000 : ℝ), (2039973548973/20000000000000 : ℝ), (47427782153759/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(327349813/625000000 : ℝ)|^8297 ≤ (42372350084869/100000000000000 : ℝ)^6249
        have hw : |(327349813/625000000 : ℝ)|=(327349813/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-179188157/1000000000 : ℝ)|^8297 ≤ (2039973548973/20000000000000 : ℝ)^6249
        have hw : |(-179188157/1000000000 : ℝ)|=(179188157/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2850819043/5000000000 : ℝ)|^8297 ≤ (47427782153759/100000000000000 : ℝ)^6249
        have hw : |(2850819043/5000000000 : ℝ)|=(2850819043/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s1_6 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5237597033/10000000000 : ℝ)*x 0 + (285081911/500000000 : ℝ)*x 1 + (-1791881339/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5237597033/10000000000 : ℝ)^8297 ≤ (10593087588351/25000000000000 : ℝ)^6249 := by
    have hnat : (5237597033 : ℕ)^8297*25000000000000^6249 ≤ 10593087588351^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237597033 10000000000 10593087588351 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285081911/500000000 : ℝ)^8297 ≤ (23713891816857/50000000000000 : ℝ)^6249 := by
    have hnat : (285081911 : ℕ)^8297*50000000000000^6249 ≤ 23713891816857^6249*500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285081911 500000000 23713891816857 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1791881339/10000000000 : ℝ)^8297 ≤ (2549966499753/25000000000000 : ℝ)^6249 := by
    have hnat : (1791881339 : ℕ)^8297*25000000000000^6249 ≤ 2549966499753^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1791881339 10000000000 2549966499753 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5237597033/10000000000 : ℝ), (285081911/500000000 : ℝ), (-1791881339/10000000000 : ℝ)] ![(10593087588351/25000000000000 : ℝ), (23713891816857/50000000000000 : ℝ), (2549966499753/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5237597033/10000000000 : ℝ)|^8297 ≤ (10593087588351/25000000000000 : ℝ)^6249
        have hw : |(5237597033/10000000000 : ℝ)|=(5237597033/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(285081911/500000000 : ℝ)|^8297 ≤ (23713891816857/50000000000000 : ℝ)^6249
        have hw : |(285081911/500000000 : ℝ)|=(285081911/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1791881339/10000000000 : ℝ)|^8297 ≤ (2549966499753/25000000000000 : ℝ)^6249
        have hw : |(-1791881339/10000000000 : ℝ)|=(1791881339/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s1_7 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (864467891/2000000000 : ℝ)*x 0 + (1266789949/2500000000 : ℝ)*x 1 + (1844942373/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (864467891/2000000000 : ℝ)^8297 ≤ (32834630172831/100000000000000 : ℝ)^6249 := by
    have hnat : (864467891 : ℕ)^8297*100000000000000^6249 ≤ 32834630172831^6249*2000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      864467891 2000000000 32834630172831 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1266789949/2500000000 : ℝ)^8297 ≤ (40551449554937/100000000000000 : ℝ)^6249 := by
    have hnat : (1266789949 : ℕ)^8297*100000000000000^6249 ≤ 40551449554937^6249*2500000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1266789949 2500000000 40551449554937 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1844942373/5000000000 : ℝ)^8297 ≤ (6653480062691/25000000000000 : ℝ)^6249 := by
    have hnat : (1844942373 : ℕ)^8297*25000000000000^6249 ≤ 6653480062691^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1844942373 5000000000 6653480062691 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(864467891/2000000000 : ℝ), (1266789949/2500000000 : ℝ), (1844942373/5000000000 : ℝ)] ![(32834630172831/100000000000000 : ℝ), (40551449554937/100000000000000 : ℝ), (6653480062691/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(864467891/2000000000 : ℝ)|^8297 ≤ (32834630172831/100000000000000 : ℝ)^6249
        have hw : |(864467891/2000000000 : ℝ)|=(864467891/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1266789949/2500000000 : ℝ)|^8297 ≤ (40551449554937/100000000000000 : ℝ)^6249
        have hw : |(1266789949/2500000000 : ℝ)|=(1266789949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1844942373/5000000000 : ℝ)|^8297 ≤ (6653480062691/25000000000000 : ℝ)^6249
        have hw : |(1844942373/5000000000 : ℝ)|=(1844942373/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1104_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27961/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8/3125 : ℝ)*pair X i i ≤ pair X i h) :
    (2717/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (5153/25000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27961/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (8/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27961/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (8/3125 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27961/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (8/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27961/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (8/3125 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27961/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (8/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27961/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (8/3125 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (8/3125 : ℝ) ^ (1037/256 : ℝ) ≤ (1586050647/50000000000000000000 : ℝ) := by
    have hpowers : (8/3125 : ℝ)^1037 ≤ (1586050647/50000000000000000000 : ℝ)^256 := by
      have hnat : (8 : ℕ)^1037*50000000000000000000^256 ≤ 1586050647^256*3125^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        8 3125 1586050647 50000000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (8/3125 : ℝ)) (X := (1586050647/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hpowhi : (27961/100000 : ℝ) ^ (1037/256 : ℝ) ≤ (57293592165099701/10000000000000000000 : ℝ) := by
    have hpowers : (27961/100000 : ℝ)^1037 ≤ (57293592165099701/10000000000000000000 : ℝ)^256 := by
      have hnat : (27961 : ℕ)^1037*10000000000000000000^256 ≤ 57293592165099701^256*100000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27961 100000 57293592165099701 10000000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27961/100000 : ℝ)) (X := (57293592165099701/10000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000000001586050647/25000000000000000000 : ℝ) ≤ (10000000000156617/10000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (25000000001586050647/25000000000000000000 : ℝ)^256 ≤ (10000000000156617/10000000000000000 : ℝ)^1037 := by
      have hnat : (25000000001586050647 : ℕ)^256*10000000000000000^1037 ≤ 10000000000156617^1037*25000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000000001586050647 25000000000000000000 10000000000156617 10000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000000000156617/10000000000000000 : ℝ)) (X := (25000000001586050647/25000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (1571452123825360911/1562500000000000000 : ℝ) ≤ (10014113424291851/10000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (1571452123825360911/1562500000000000000 : ℝ)^256 ≤ (10014113424291851/10000000000000000 : ℝ)^1037 := by
      have hnat : (1571452123825360911 : ℕ)^256*10000000000000000^1037 ≤ 10014113424291851^1037*1562500000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1571452123825360911 1562500000000000000 10014113424291851 10000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10014113424291851/10000000000000000 : ℝ)) (X := (1571452123825360911/1562500000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (5057293592165099701/5000000000000000000 : ℝ) ≤ (2005645369685417/2000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (5057293592165099701/5000000000000000000 : ℝ)^256 ≤ (2005645369685417/2000000000000000 : ℝ)^1037 := by
      have hnat : (5057293592165099701 : ℕ)^256*2000000000000000^1037 ≤ 2005645369685417^1037*5000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5057293592165099701 5000000000000000000 2005645369685417 2000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2005645369685417/2000000000000000 : ℝ)) (X := (5057293592165099701/5000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1586050647/50000000000000000000 : ℝ) ≤ ((277042773931181834177/277050000000000000000 : ℝ)+2*(7056712067617/1385250000000000 : ℝ)*(8/3125 : ℝ))^(1037/256 : ℝ) := by
    rw [show (277042773931181834177/277050000000000000000 : ℝ)+2*(7056712067617/1385250000000000 : ℝ)*(8/3125 : ℝ)=(10000000000156617/10000000000000000 : ℝ) by norm_num, show 1+2*(1586050647/50000000000000000000 : ℝ)=(25000000001586050647/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(57293592165099701/10000000000000000000 : ℝ)+(1586050647/50000000000000000000 : ℝ) ≤ ((277042773931181834177/277050000000000000000 : ℝ)+(7056712067617/1385250000000000 : ℝ)*((27961/100000 : ℝ)+(8/3125 : ℝ)))^(1037/256 : ℝ) := by
    rw [show (277042773931181834177/277050000000000000000 : ℝ)+(7056712067617/1385250000000000 : ℝ)*((27961/100000 : ℝ)+(8/3125 : ℝ))=(10014113424291851/10000000000000000 : ℝ) by norm_num, show 1+(57293592165099701/10000000000000000000 : ℝ)+(1586050647/50000000000000000000 : ℝ)=(1571452123825360911/1562500000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(57293592165099701/10000000000000000000 : ℝ) ≤ ((277042773931181834177/277050000000000000000 : ℝ)+2*(7056712067617/1385250000000000 : ℝ)*(27961/100000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (277042773931181834177/277050000000000000000 : ℝ)+2*(7056712067617/1385250000000000 : ℝ)*(27961/100000 : ℝ)=(2005645369685417/2000000000000000 : ℝ) by norm_num, show 1+2*(57293592165099701/10000000000000000000 : ℝ)=(5057293592165099701/5000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (277042773931181834177/277050000000000000000 : ℝ)*(X 1 0+X 2 0)+(7056712067617/1385250000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (8/3125 : ℝ)) (hi := (27961/100000 : ℝ)) (c := (277042773931181834177/277050000000000000000 : ℝ)) (alpha := (7056712067617/1385250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (277042773931181834177/277050000000000000000 : ℝ)*(X 0 1+X 2 1)+(7056712067617/1385250000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (8/3125 : ℝ)) (hi := (27961/100000 : ℝ)) (c := (277042773931181834177/277050000000000000000 : ℝ)) (alpha := (7056712067617/1385250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (277042773931181834177/277050000000000000000 : ℝ)*(X 0 2+X 1 2)+(7056712067617/1385250000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (8/3125 : ℝ)) (hi := (27961/100000 : ℝ)) (c := (277042773931181834177/277050000000000000000 : ℝ)) (alpha := (7056712067617/1385250000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1055653397/5000000000 : ℝ)*X 0 0+(571177811/1000000000 : ℝ)*X 0 1+(2497110977/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5421211143/10000000000 : ℝ)*X 1 0+(-1249649071/5000000000 : ℝ)*X 1 1+(249711101/500000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2710606151/5000000000 : ℝ)*X 2 0+(2497110449/5000000000 : ℝ)*X 2 1+(-2499298057/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2160320669/5000000000 : ℝ)*X 0 0+(3669862843/10000000000 : ℝ)*X 0 1+(5086788197/10000000000 : ℝ)*X 0 2+(2160320669/5000000000 : ℝ)*X 1 0+(3669862843/10000000000 : ℝ)*X 1 1+(5086788197/10000000000 : ℝ)*X 1 2+(2160320669/5000000000 : ℝ)*X 2 0+(3669862843/10000000000 : ℝ)*X 2 1+(5086788197/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2112167409/10000000000 : ℝ)*X 0 0+(500416249/1000000000 : ℝ)*X 0 1+(2850819133/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((327349813/625000000 : ℝ)*X 1 0+(-179188157/1000000000 : ℝ)*X 1 1+(2850819043/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5237597033/10000000000 : ℝ)*X 2 0+(285081911/500000000 : ℝ)*X 2 1+(-1791881339/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((864467891/2000000000 : ℝ)*X 0 0+(1266789949/2500000000 : ℝ)*X 0 1+(1844942373/5000000000 : ℝ)*X 0 2+(864467891/2000000000 : ℝ)*X 1 0+(1266789949/2500000000 : ℝ)*X 1 1+(1844942373/5000000000 : ℝ)*X 1 2+(864467891/2000000000 : ℝ)*X 2 0+(1266789949/2500000000 : ℝ)*X 2 1+(1844942373/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (34350326946791953477694769767/4617500000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (230050051/100000000000000 : ℝ)*(base1) + (179129179/12500000000000 : ℝ)*(base19) + (1730977421/100000000000000 : ℝ)*(base23) + (45268957/50000000000000 : ℝ)*(upper3) + (100162689/50000000000000 : ℝ)*(upper5) + (1049695653639443/100000000000000 : ℝ)*(major0) + (1049695653639443/100000000000000 : ℝ)*(major1) + (1049695653639443/100000000000000 : ℝ)*(major2) + (696812339670333/50000000000000 : ℝ)*(sp0) + (13936303826787/1000000000000 : ℝ)*(sp1) + (174203760591839/12500000000000 : ℝ)*(sp2) + (352878145857017/50000000000000 : ℝ)*(sp3) + (3683210759/50000000000000 : ℝ)*(sp4) + (2721830619/100000000000000 : ℝ)*(sp7) + (44109952724669/6250000000000 : ℝ)*(f.failure) + (1393631815712133/100000000000000 : ℝ)*(f.sum) + (328640507239387/138525000000000000000000000000 : ℝ)*base65 + (277209940706108843411/27705000000000000000000000000000000 : ℝ)*base67 + (38177568478718843411/27705000000000000000000000000000000 : ℝ)*base69 + (194173878595553843411/27705000000000000000000000000000000 : ℝ)*base71 + (195745829862253/34631250000000000000000000000 : ℝ)*base73 + (170380707264878843411/27705000000000000000000000000000000 : ℝ)*base75 + (181095098236133843411/27705000000000000000000000000000000 : ℝ)*base77 + (48357489855428843411/27705000000000000000000000000000000 : ℝ)*base79 + (13581961025269/69262500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (489343/78125000000000000000 : ℝ)*base90 + (489343/78125000000000000000 : ℝ)*base92 + (489343/78125000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (22724374361841217759411807803/2308750000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (113925891/100000000000000 : ℝ)*(base1) + (545955157/25000000000000 : ℝ)*(base19) + (2206902023/100000000000000 : ℝ)*(base23) + (111497367/50000000000000 : ℝ)*(upper3) + (224191749/100000000000000 : ℝ)*(upper5) + (539953338437913/50000000000000 : ℝ)*(major0) + (539953338437913/50000000000000 : ℝ)*(major1) + (539953338437913/50000000000000 : ℝ)*(major2) + (4416966677/50000000000000 : ℝ)*(sp1) + (9297062297/100000000000000 : ℝ)*(sp2) + (716870809484161/50000000000000 : ℝ)*(sp4) + (11201019431941/781250000000 : ℝ)*(sp5) + (1433730001078111/100000000000000 : ℝ)*(sp6) + (5672432864787/781250000000 : ℝ)*(sp7) + (726071520618627/100000000000000 : ℝ)*(f.failure) + (1433741505042431/100000000000000 : ℝ)*(f.sum) + (84551461047211/23087500000000000000000000000 : ℝ)*base66 + (36771453610549949133/4617500000000000000000000000000000 : ℝ)*base68 + (12556503585509949133/4617500000000000000000000000000000 : ℝ)*base70 + (15895470373424949133/4617500000000000000000000000000000 : ℝ)*base72 + (7870885415421/1442968750000000000000000000 : ℝ)*base74 + (1413903312339949133/4617500000000000000000000000000000 : ℝ)*base76 + (40967087733167449133/4617500000000000000000000000000000 : ℝ)*base78 + (51167171760704949133/4617500000000000000000000000000000 : ℝ)*base80 + (67240368492861/23087500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (2589081/1250000000000000000000 : ℝ)*base89 + (2589081/1250000000000000000000 : ℝ)*base91 + (2589081/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1104_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27961/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (8/3125 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2717/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (5153/25000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1104_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1104_s2_0 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-216660073/1000000000 : ℝ)*x 0 + (5518201961/10000000000 : ℝ)*x 1 + (2576338717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (216660073/1000000000 : ℝ)^8297 ≤ (205074710127/1562500000000 : ℝ)^6249 := by
    have hnat : (216660073 : ℕ)^8297*1562500000000^6249 ≤ 205074710127^6249*1000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      216660073 1000000000 205074710127 1562500000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5518201961/10000000000 : ℝ)^8297 ≤ (45412591559203/100000000000000 : ℝ)^6249 := by
    have hnat : (5518201961 : ℕ)^8297*100000000000000^6249 ≤ 45412591559203^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5518201961 10000000000 45412591559203 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2576338717/5000000000 : ℝ)^8297 ≤ (41462626977177/100000000000000 : ℝ)^6249 := by
    have hnat : (2576338717 : ℕ)^8297*100000000000000^6249 ≤ 41462626977177^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2576338717 5000000000 41462626977177 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-216660073/1000000000 : ℝ), (5518201961/10000000000 : ℝ), (2576338717/5000000000 : ℝ)] ![(205074710127/1562500000000 : ℝ), (45412591559203/100000000000000 : ℝ), (41462626977177/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-216660073/1000000000 : ℝ)|^8297 ≤ (205074710127/1562500000000 : ℝ)^6249
        have hw : |(-216660073/1000000000 : ℝ)|=(216660073/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5518201961/10000000000 : ℝ)|^8297 ≤ (45412591559203/100000000000000 : ℝ)^6249
        have hw : |(5518201961/10000000000 : ℝ)|=(5518201961/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2576338717/5000000000 : ℝ)|^8297 ≤ (41462626977177/100000000000000 : ℝ)^6249
        have hw : |(2576338717/5000000000 : ℝ)|=(2576338717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s2_1 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5375516809/10000000000 : ℝ)*x 0 + (-1178462891/5000000000 : ℝ)*x 1 + (5152678599/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375516809/10000000000 : ℝ)^8297 ≤ (10965039385217/25000000000000 : ℝ)^6249 := by
    have hnat : (5375516809 : ℕ)^8297*25000000000000^6249 ≤ 10965039385217^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375516809 10000000000 10965039385217 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1178462891/5000000000 : ℝ)^8297 ≤ (14677203018009/100000000000000 : ℝ)^6249 := by
    have hnat : (1178462891 : ℕ)^8297*100000000000000^6249 ≤ 14677203018009^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1178462891 5000000000 14677203018009 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5152678599/10000000000 : ℝ)^8297 ≤ (41462639424053/100000000000000 : ℝ)^6249 := by
    have hnat : (5152678599 : ℕ)^8297*100000000000000^6249 ≤ 41462639424053^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152678599 10000000000 41462639424053 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375516809/10000000000 : ℝ), (-1178462891/5000000000 : ℝ), (5152678599/10000000000 : ℝ)] ![(10965039385217/25000000000000 : ℝ), (14677203018009/100000000000000 : ℝ), (41462639424053/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375516809/10000000000 : ℝ)|^8297 ≤ (10965039385217/25000000000000 : ℝ)^6249
        have hw : |(5375516809/10000000000 : ℝ)|=(5375516809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1178462891/5000000000 : ℝ)|^8297 ≤ (14677203018009/100000000000000 : ℝ)^6249
        have hw : |(-1178462891/5000000000 : ℝ)|=(1178462891/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5152678599/10000000000 : ℝ)|^8297 ≤ (41462639424053/100000000000000 : ℝ)^6249
        have hw : |(5152678599/10000000000 : ℝ)|=(5152678599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s2_2 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5375516763/10000000000 : ℝ)*x 0 + (5152678651/10000000000 : ℝ)*x 1 + (-94277031/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5375516763/10000000000 : ℝ)^8297 ≤ (43860157042537/100000000000000 : ℝ)^6249 := by
    have hnat : (5375516763 : ℕ)^8297*100000000000000^6249 ≤ 43860157042537^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5375516763 10000000000 43860157042537 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5152678651/10000000000 : ℝ)^8297 ≤ (20731319989811/50000000000000 : ℝ)^6249 := by
    have hnat : (5152678651 : ℕ)^8297*50000000000000^6249 ≤ 20731319989811^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5152678651 10000000000 20731319989811 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (94277031/400000000 : ℝ)^8297 ≤ (3669300740033/25000000000000 : ℝ)^6249 := by
    have hnat : (94277031 : ℕ)^8297*25000000000000^6249 ≤ 3669300740033^6249*400000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      94277031 400000000 3669300740033 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5375516763/10000000000 : ℝ), (5152678651/10000000000 : ℝ), (-94277031/400000000 : ℝ)] ![(43860157042537/100000000000000 : ℝ), (20731319989811/50000000000000 : ℝ), (3669300740033/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5375516763/10000000000 : ℝ)|^8297 ≤ (43860157042537/100000000000000 : ℝ)^6249
        have hw : |(5375516763/10000000000 : ℝ)|=(5375516763/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5152678651/10000000000 : ℝ)|^8297 ≤ (20731319989811/50000000000000 : ℝ)^6249
        have hw : |(5152678651/10000000000 : ℝ)|=(5152678651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-94277031/400000000 : ℝ)|^8297 ≤ (3669300740033/25000000000000 : ℝ)^6249
        have hw : |(-94277031/400000000 : ℝ)|=(94277031/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s2_3 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (4358475849/10000000000 : ℝ)*x 0 + (4012521249/10000000000 : ℝ)*x 1 + (473430423/1000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4358475849/10000000000 : ℝ)^8297 ≤ (16599802157249/50000000000000 : ℝ)^6249 := by
    have hnat : (4358475849 : ℕ)^8297*50000000000000^6249 ≤ 16599802157249^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4358475849 10000000000 16599802157249 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4012521249/10000000000 : ℝ)^8297 ≤ (29747080267607/100000000000000 : ℝ)^6249 := by
    have hnat : (4012521249 : ℕ)^8297*100000000000000^6249 ≤ 29747080267607^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4012521249 10000000000 29747080267607 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (473430423/1000000000 : ℝ)^8297 ≤ (37053315407937/100000000000000 : ℝ)^6249 := by
    have hnat : (473430423 : ℕ)^8297*100000000000000^6249 ≤ 37053315407937^6249*1000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      473430423 1000000000 37053315407937 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4358475849/10000000000 : ℝ), (4012521249/10000000000 : ℝ), (473430423/1000000000 : ℝ)] ![(16599802157249/50000000000000 : ℝ), (29747080267607/100000000000000 : ℝ), (37053315407937/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4358475849/10000000000 : ℝ)|^8297 ≤ (16599802157249/50000000000000 : ℝ)^6249
        have hw : |(4358475849/10000000000 : ℝ)|=(4358475849/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4012521249/10000000000 : ℝ)|^8297 ≤ (29747080267607/100000000000000 : ℝ)^6249
        have hw : |(4012521249/10000000000 : ℝ)|=(4012521249/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(473430423/1000000000 : ℝ)|^8297 ≤ (37053315407937/100000000000000 : ℝ)^6249
        have hw : |(473430423/1000000000 : ℝ)|=(473430423/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s2_4 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (-2166714163/10000000000 : ℝ)*x 0 + (5155266393/10000000000 : ℝ)*x 1 + (1103117319/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2166714163/10000000000 : ℝ)^8297 ≤ (3281423452383/25000000000000 : ℝ)^6249 := by
    have hnat : (2166714163 : ℕ)^8297*25000000000000^6249 ≤ 3281423452383^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2166714163 10000000000 3281423452383 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5155266393/10000000000 : ℝ)^8297 ≤ (10372572431747/25000000000000 : ℝ)^6249 := by
    have hnat : (5155266393 : ℕ)^8297*25000000000000^6249 ≤ 10372572431747^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5155266393 10000000000 10372572431747 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1103117319/2000000000 : ℝ)^8297 ≤ (22692008221671/50000000000000 : ℝ)^6249 := by
    have hnat : (1103117319 : ℕ)^8297*50000000000000^6249 ≤ 22692008221671^6249*2000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103117319 2000000000 22692008221671 50000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2166714163/10000000000 : ℝ), (5155266393/10000000000 : ℝ), (1103117319/2000000000 : ℝ)] ![(3281423452383/25000000000000 : ℝ), (10372572431747/25000000000000 : ℝ), (22692008221671/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2166714163/10000000000 : ℝ)|^8297 ≤ (3281423452383/25000000000000 : ℝ)^6249
        have hw : |(-2166714163/10000000000 : ℝ)|=(2166714163/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5155266393/10000000000 : ℝ)|^8297 ≤ (10372572431747/25000000000000 : ℝ)^6249
        have hw : |(5155266393/10000000000 : ℝ)|=(5155266393/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1103117319/2000000000 : ℝ)|^8297 ≤ (22692008221671/50000000000000 : ℝ)^6249
        have hw : |(1103117319/2000000000 : ℝ)|=(1103117319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s2_5 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (66037641/125000000 : ℝ)*x 0 + (-1994017221/10000000000 : ℝ)*x 1 + (5515586681/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (66037641/125000000 : ℝ)^8297 ≤ (10715213720439/25000000000000 : ℝ)^6249 := by
    have hnat : (66037641 : ℕ)^8297*25000000000000^6249 ≤ 10715213720439^6249*125000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      66037641 125000000 10715213720439 25000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1994017221/10000000000 : ℝ)^8297 ≤ (11755127715491/100000000000000 : ℝ)^6249 := by
    have hnat : (1994017221 : ℕ)^8297*100000000000000^6249 ≤ 11755127715491^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1994017221 10000000000 11755127715491 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5515586681/10000000000 : ℝ)^8297 ≤ (45384017382893/100000000000000 : ℝ)^6249 := by
    have hnat : (5515586681 : ℕ)^8297*100000000000000^6249 ≤ 45384017382893^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5515586681 10000000000 45384017382893 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(66037641/125000000 : ℝ), (-1994017221/10000000000 : ℝ), (5515586681/10000000000 : ℝ)] ![(10715213720439/25000000000000 : ℝ), (11755127715491/100000000000000 : ℝ), (45384017382893/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(66037641/125000000 : ℝ)|^8297 ≤ (10715213720439/25000000000000 : ℝ)^6249
        have hw : |(66037641/125000000 : ℝ)|=(66037641/125000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1994017221/10000000000 : ℝ)|^8297 ≤ (11755127715491/100000000000000 : ℝ)^6249
        have hw : |(-1994017221/10000000000 : ℝ)|=(1994017221/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5515586681/10000000000 : ℝ)|^8297 ≤ (45384017382893/100000000000000 : ℝ)^6249
        have hw : |(5515586681/10000000000 : ℝ)|=(5515586681/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s2_6 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (5283011431/10000000000 : ℝ)*x 0 + (2757793309/5000000000 : ℝ)*x 1 + (-997008551/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5283011431/10000000000 : ℝ)^8297 ≤ (2678803531769/6250000000000 : ℝ)^6249 := by
    have hnat : (5283011431 : ℕ)^8297*6250000000000^6249 ≤ 2678803531769^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5283011431 10000000000 2678803531769 6250000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2757793309/5000000000 : ℝ)^8297 ≤ (45384016694617/100000000000000 : ℝ)^6249 := by
    have hnat : (2757793309 : ℕ)^8297*100000000000000^6249 ≤ 45384016694617^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2757793309 5000000000 45384016694617 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (997008551/5000000000 : ℝ)^8297 ≤ (11755126784049/100000000000000 : ℝ)^6249 := by
    have hnat : (997008551 : ℕ)^8297*100000000000000^6249 ≤ 11755126784049^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      997008551 5000000000 11755126784049 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5283011431/10000000000 : ℝ), (2757793309/5000000000 : ℝ), (-997008551/5000000000 : ℝ)] ![(2678803531769/6250000000000 : ℝ), (45384016694617/100000000000000 : ℝ), (11755126784049/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5283011431/10000000000 : ℝ)|^8297 ≤ (2678803531769/6250000000000 : ℝ)^6249
        have hw : |(5283011431/10000000000 : ℝ)|=(5283011431/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2757793309/5000000000 : ℝ)|^8297 ≤ (45384016694617/100000000000000 : ℝ)^6249
        have hw : |(2757793309/5000000000 : ℝ)|=(2757793309/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-997008551/5000000000 : ℝ)|^8297 ≤ (11755126784049/100000000000000 : ℝ)^6249
        have hw : |(-997008551/5000000000 : ℝ)|=(997008551/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1104_s2_7 (p : ℝ) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ)) (x : Fin 3 → ℝ) :
    (2179350579/5000000000 : ℝ)*x 0 + (472919287/1000000000 : ℝ)*x 1 + (4017683809/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2179350579/5000000000 : ℝ)^8297 ≤ (33201883034939/100000000000000 : ℝ)^6249 := by
    have hnat : (2179350579 : ℕ)^8297*100000000000000^6249 ≤ 33201883034939^6249*5000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2179350579 5000000000 33201883034939 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (472919287/1000000000 : ℝ)^8297 ≤ (37000209714193/100000000000000 : ℝ)^6249 := by
    have hnat : (472919287 : ℕ)^8297*100000000000000^6249 ≤ 37000209714193^6249*1000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      472919287 1000000000 37000209714193 100000000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4017683809/10000000000 : ℝ)^8297 ≤ (3724738404473/12500000000000 : ℝ)^6249 := by
    have hnat : (4017683809 : ℕ)^8297*12500000000000^6249 ≤ 3724738404473^6249*10000000000^8297 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4017683809 10000000000 3724738404473 12500000000000 8297 6249 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (8297/2048 : ℝ)) 8297 6249 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2179350579/5000000000 : ℝ), (472919287/1000000000 : ℝ), (4017683809/10000000000 : ℝ)] ![(33201883034939/100000000000000 : ℝ), (37000209714193/100000000000000 : ℝ), (3724738404473/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2179350579/5000000000 : ℝ)|^8297 ≤ (33201883034939/100000000000000 : ℝ)^6249
        have hw : |(2179350579/5000000000 : ℝ)|=(2179350579/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(472919287/1000000000 : ℝ)|^8297 ≤ (37000209714193/100000000000000 : ℝ)^6249
        have hw : |(472919287/1000000000 : ℝ)|=(472919287/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4017683809/10000000000 : ℝ)|^8297 ≤ (3724738404473/12500000000000 : ℝ)^6249
        have hw : |(4017683809/10000000000 : ℝ)|=(4017683809/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1104_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5153/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (1779/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16619/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (5153/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2717/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (5153/25000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2717/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (5153/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2717/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (5153/25000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2717/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (5153/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2717/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (5153/25000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2717/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base29 : ((-1 : ℝ)*N 1+(-1 : ℝ)*N 2+(1 : ℝ)*P 0) ≤ (0 : ℝ) := by
    linarith only [f.Ptriangle 0, f.sum]
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
  have hpowlo : (2717/50000 : ℝ) ^ (1037/256 : ℝ) ≤ (150409866541473/20000000000000000000 : ℝ) := by
    have hpowers : (2717/50000 : ℝ)^1037 ≤ (150409866541473/20000000000000000000 : ℝ)^256 := by
      have hnat : (2717 : ℕ)^1037*20000000000000000000^256 ≤ 150409866541473^256*50000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2717 50000 150409866541473 20000000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2717/50000 : ℝ)) (X := (150409866541473/20000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hpowhi : (5153/25000 : ℝ) ^ (1037/256 : ℝ) ≤ (166590678954553289/100000000000000000000 : ℝ) := by
    have hpowers : (5153/25000 : ℝ)^1037 ≤ (166590678954553289/100000000000000000000 : ℝ)^256 := by
      have hnat : (5153 : ℕ)^1037*100000000000000000000^256 ≤ 166590678954553289^256*25000^1037 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5153 25000 166590678954553289 100000000000000000000 1037 256 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5153/25000 : ℝ)) (X := (166590678954553289/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner00 : (10000150409866541473/10000000000000000000 : ℝ) ≤ (2500009282716429/2500000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (10000150409866541473/10000000000000000000 : ℝ)^256 ≤ (2500009282716429/2500000000000000 : ℝ)^1037 := by
      have hnat : (10000150409866541473 : ℕ)^256*2500000000000000^1037 ≤ 2500009282716429^1037*10000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10000150409866541473 10000000000000000000 2500009282716429 2500000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500009282716429/2500000000000000 : ℝ)) (X := (10000150409866541473/10000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner10 : (50083671364143630327/50000000000000000000 : ℝ) ≤ (10004128521603391/10000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (50083671364143630327/50000000000000000000 : ℝ)^256 ≤ (10004128521603391/10000000000000000 : ℝ)^1037 := by
      have hnat : (50083671364143630327 : ℕ)^256*10000000000000000^1037 ≤ 10004128521603391^1037*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50083671364143630327 50000000000000000000 10004128521603391 10000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10004128521603391/10000000000000000 : ℝ)) (X := (50083671364143630327/50000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have hcorner11 : (50166590678954553289/50000000000000000000 : ℝ) ≤ (5004109956170533/5000000000000000 : ℝ) ^ (1037/256 : ℝ) := by
    have hpowers : (50166590678954553289/50000000000000000000 : ℝ)^256 ≤ (5004109956170533/5000000000000000 : ℝ)^1037 := by
      have hnat : (50166590678954553289 : ℕ)^256*5000000000000000^1037 ≤ 5004109956170533^1037*50000000000000000000^256 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50166590678954553289 50000000000000000000 5004109956170533 5000000000000000 256 1037 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5004109956170533/5000000000000000 : ℝ)) (X := (50166590678954553289/50000000000000000000 : ℝ)) (by norm_num) 1037 256 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(150409866541473/20000000000000000000 : ℝ) ≤ ((37934024584435696387/37945000000000000000 : ℝ)+2*(163655629507/60712000000000 : ℝ)*(2717/50000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (37934024584435696387/37945000000000000000 : ℝ)+2*(163655629507/60712000000000 : ℝ)*(2717/50000 : ℝ)=(2500009282716429/2500000000000000 : ℝ) by norm_num, show 1+2*(150409866541473/20000000000000000000 : ℝ)=(10000150409866541473/10000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(166590678954553289/100000000000000000000 : ℝ)+(150409866541473/20000000000000000000 : ℝ) ≤ ((37934024584435696387/37945000000000000000 : ℝ)+(163655629507/60712000000000 : ℝ)*((5153/25000 : ℝ)+(2717/50000 : ℝ)))^(1037/256 : ℝ) := by
    rw [show (37934024584435696387/37945000000000000000 : ℝ)+(163655629507/60712000000000 : ℝ)*((5153/25000 : ℝ)+(2717/50000 : ℝ))=(10004128521603391/10000000000000000 : ℝ) by norm_num, show 1+(166590678954553289/100000000000000000000 : ℝ)+(150409866541473/20000000000000000000 : ℝ)=(50083671364143630327/50000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(166590678954553289/100000000000000000000 : ℝ) ≤ ((37934024584435696387/37945000000000000000 : ℝ)+2*(163655629507/60712000000000 : ℝ)*(5153/25000 : ℝ))^(1037/256 : ℝ) := by
    rw [show (37934024584435696387/37945000000000000000 : ℝ)+2*(163655629507/60712000000000 : ℝ)*(5153/25000 : ℝ)=(5004109956170533/5000000000000000 : ℝ) by norm_num, show 1+2*(166590678954553289/100000000000000000000 : ℝ)=(50166590678954553289/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (37934024584435696387/37945000000000000000 : ℝ)*(X 1 0+X 2 0)+(163655629507/60712000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (2717/50000 : ℝ)) (hi := (5153/25000 : ℝ)) (c := (37934024584435696387/37945000000000000000 : ℝ)) (alpha := (163655629507/60712000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (37934024584435696387/37945000000000000000 : ℝ)*(X 0 1+X 2 1)+(163655629507/60712000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (2717/50000 : ℝ)) (hi := (5153/25000 : ℝ)) (c := (37934024584435696387/37945000000000000000 : ℝ)) (alpha := (163655629507/60712000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (37934024584435696387/37945000000000000000 : ℝ)*(X 0 2+X 1 2)+(163655629507/60712000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (1037/256 : ℝ)) (lo := (2717/50000 : ℝ)) (hi := (5153/25000 : ℝ)) (c := (37934024584435696387/37945000000000000000 : ℝ)) (alpha := (163655629507/60712000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-216660073/1000000000 : ℝ)*X 0 0+(5518201961/10000000000 : ℝ)*X 0 1+(2576338717/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5375516809/10000000000 : ℝ)*X 1 0+(-1178462891/5000000000 : ℝ)*X 1 1+(5152678599/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5375516763/10000000000 : ℝ)*X 2 0+(5152678651/10000000000 : ℝ)*X 2 1+(-94277031/400000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4358475849/10000000000 : ℝ)*X 0 0+(4012521249/10000000000 : ℝ)*X 0 1+(473430423/1000000000 : ℝ)*X 0 2+(4358475849/10000000000 : ℝ)*X 1 0+(4012521249/10000000000 : ℝ)*X 1 1+(473430423/1000000000 : ℝ)*X 1 2+(4358475849/10000000000 : ℝ)*X 2 0+(4012521249/10000000000 : ℝ)*X 2 1+(473430423/1000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2166714163/10000000000 : ℝ)*X 0 0+(5155266393/10000000000 : ℝ)*X 0 1+(1103117319/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((66037641/125000000 : ℝ)*X 1 0+(-1994017221/10000000000 : ℝ)*X 1 1+(5515586681/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5283011431/10000000000 : ℝ)*X 2 0+(2757793309/5000000000 : ℝ)*X 2 1+(-997008551/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2179350579/5000000000 : ℝ)*X 0 0+(472919287/1000000000 : ℝ)*X 0 1+(4017683809/10000000000 : ℝ)*X 0 2+(2179350579/5000000000 : ℝ)*X 1 0+(472919287/1000000000 : ℝ)*X 1 1+(4017683809/10000000000 : ℝ)*X 1 2+(2179350579/5000000000 : ℝ)*X 2 0+(472919287/1000000000 : ℝ)*X 2 1+(4017683809/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1104_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11352380901851934270669/3794500000000000000000000000 : ℝ) := by norm_num
    linear_combination (66028703/100000000000000 : ℝ)*(base29) + (44159089/50000000000000 : ℝ)*(upper2) + (2281331/50000000000000 : ℝ)*(upper3) + (75733453/100000000000000 : ℝ)*(upper4) + (432547/2000000000000 : ℝ)*(upper5) + (2060635464266157/100000000000000 : ℝ)*(major0) + (103031776514743/5000000000000 : ℝ)*(major1) + (103031776514743/5000000000000 : ℝ)*(major2) + (683950515559261/25000000000000 : ℝ)*(sp0) + (1367904860154603/50000000000000 : ℝ)*(sp1) + (2735809720309207/100000000000000 : ℝ)*(sp2) + (1385459677892071/100000000000000 : ℝ)*(sp3) + (30172269/390625000000 : ℝ)*(sp4) + (1496633103/100000000000000 : ℝ)*(sp7) + (692730587262587/50000000000000 : ℝ)*(f.failure) + (683952446584477/25000000000000 : ℝ)*(f.sum) + (28406833658939/7589000000000000000000000000 : ℝ)*base66 + (1577450789049833541/189725000000000000000000000000000 : ℝ)*base67 + (93053875200466459/189725000000000000000000000000000 : ℝ)*base70 + (4597901991012274759/3794500000000000000000000000000000 : ℝ)*base71 + (166916291554963/30356000000000000000000000000 : ℝ)*base73 + (2178761246192422709/189725000000000000000000000000000 : ℝ)*base76 + (26673685386509225241/3794500000000000000000000000000000 : ℝ)*base78 + (606637013756202291/189725000000000000000000000000000 : ℝ)*base79 + (158221847123497/30356000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/50000000000000 : ℝ)*base87 + (743039/625000000000000000000 : ℝ)*base90 + (743039/625000000000000000000 : ℝ)*base92 + (743039/625000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1506664401447611700697329531/189725000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (198025253/12500000000000 : ℝ)*(base19) + (908229811/50000000000000 : ℝ)*(base23) + (211678173/100000000000000 : ℝ)*(upper3) + (54281781/100000000000000 : ℝ)*(lower4) + (155031419/100000000000000 : ℝ)*(upper5) + (209038619046829/10000000000000 : ℝ)*(major0) + (209038619046829/10000000000000 : ℝ)*(major1) + (209038619046829/10000000000000 : ℝ)*(major2) + (14400647659/100000000000000 : ℝ)*(sp1) + (17266788149/100000000000000 : ℝ)*(sp2) + (693827047047753/25000000000000 : ℝ)*(sp4) + (173455762708833/6250000000000 : ℝ)*(sp5) + (69382227623581/2500000000000 : ℝ)*(sp6) + (1405463928035341/100000000000000 : ℝ)*(sp7) + (1405463928035341/100000000000000 : ℝ)*(f.failure) + (693827047047753/25000000000000 : ℝ)*(f.sum) + (5706175883483/7589000000000000000000000000 : ℝ)*base66 + (2827572255224218177/379450000000000000000000000000000 : ℝ)*base68 + (379197782828431823/379450000000000000000000000000000 : ℝ)*base69 + (1258752698390431823/379450000000000000000000000000000 : ℝ)*base71 + (55529804418541/7589000000000000000000000000 : ℝ)*base74 + (985197400508618177/379450000000000000000000000000000 : ℝ)*base76 + (237941830096231823/379450000000000000000000000000000 : ℝ)*base77 + (2766503670917431823/379450000000000000000000000000000 : ℝ)*base79 + (29548089371771/7589000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base86 + (1/100000000000000 : ℝ)*base88 + (4841623/1250000000000000000000 : ℝ)*base89 + (4841623/1250000000000000000000 : ℝ)*base91 + (4841623/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1104_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (5153/25000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2717/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1779/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16619/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1104_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1104_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1779/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16619/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1104_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1104_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1104_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (1037/256 : ℝ) ≤ p) (hpb : p ≤ (8297/2048 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (18591603/12500000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1779/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16619/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1104_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
