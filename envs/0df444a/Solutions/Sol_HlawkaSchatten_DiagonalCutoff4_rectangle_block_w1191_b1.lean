-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1191_b1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:53:16.82195+00:00
-- url     : https://prove2.me/submissions/4b51adef-9af4-47c0-b358-7bfa3d167a15

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
theorem support_rectangle_w1191_s3_0 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070185111/5000000000 : ℝ)*x 0 + (5424316247/10000000000 : ℝ)*x 1 + (5236485197/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070185111/5000000000 : ℝ)^131 ≤ (1300412908893/10000000000000 : ℝ)^99 := by
    have hnat : (1070185111 : ℕ)^131*10000000000000^99 ≤ 1300412908893^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070185111 5000000000 1300412908893 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5424316247/10000000000 : ℝ)^131 ≤ (44511960143611/100000000000000 : ℝ)^99 := by
    have hnat : (5424316247 : ℕ)^131*100000000000000^99 ≤ 44511960143611^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5424316247 10000000000 44511960143611 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236485197/10000000000 : ℝ)^131 ≤ (4248391075903/10000000000000 : ℝ)^99 := by
    have hnat : (5236485197 : ℕ)^131*10000000000000^99 ≤ 4248391075903^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236485197 10000000000 4248391075903 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070185111/5000000000 : ℝ), (5424316247/10000000000 : ℝ), (5236485197/10000000000 : ℝ)] ![(1300412908893/10000000000000 : ℝ), (44511960143611/100000000000000 : ℝ), (4248391075903/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070185111/5000000000 : ℝ)|^131 ≤ (1300412908893/10000000000000 : ℝ)^99
        have hw : |(-1070185111/5000000000 : ℝ)|=(1070185111/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5424316247/10000000000 : ℝ)|^131 ≤ (44511960143611/100000000000000 : ℝ)^99
        have hw : |(5424316247/10000000000 : ℝ)|=(5424316247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236485197/10000000000 : ℝ)|^131 ≤ (4248391075903/10000000000000 : ℝ)^99
        have hw : |(5236485197/10000000000 : ℝ)|=(5236485197/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s3_1 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (669079959/1250000000 : ℝ)*x 0 + (-1118141923/5000000000 : ℝ)*x 1 + (5236485541/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (669079959/1250000000 : ℝ)^131 ≤ (43735330769669/100000000000000 : ℝ)^99 := by
    have hnat : (669079959 : ℕ)^131*100000000000000^99 ≤ 43735330769669^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      669079959 1250000000 43735330769669 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118141923/5000000000 : ℝ)^131 ≤ (861297172073/6250000000000 : ℝ)^99 := by
    have hnat : (1118141923 : ℕ)^131*6250000000000^99 ≤ 861297172073^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118141923 5000000000 861297172073 6250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5236485541/10000000000 : ℝ)^131 ≤ (10620978613007/25000000000000 : ℝ)^99 := by
    have hnat : (5236485541 : ℕ)^131*25000000000000^99 ≤ 10620978613007^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236485541 10000000000 10620978613007 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(669079959/1250000000 : ℝ), (-1118141923/5000000000 : ℝ), (5236485541/10000000000 : ℝ)] ![(43735330769669/100000000000000 : ℝ), (861297172073/6250000000000 : ℝ), (10620978613007/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(669079959/1250000000 : ℝ)|^131 ≤ (43735330769669/100000000000000 : ℝ)^99
        have hw : |(669079959/1250000000 : ℝ)|=(669079959/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1118141923/5000000000 : ℝ)|^131 ≤ (861297172073/6250000000000 : ℝ)^99
        have hw : |(-1118141923/5000000000 : ℝ)|=(1118141923/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5236485541/10000000000 : ℝ)|^131 ≤ (10620978613007/25000000000000 : ℝ)^99
        have hw : |(5236485541/10000000000 : ℝ)|=(5236485541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s3_2 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (535263949/1000000000 : ℝ)*x 0 + (5236485853/10000000000 : ℝ)*x 1 + (-1118141839/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (535263949/1000000000 : ℝ)^131 ≤ (4373532880191/10000000000000 : ℝ)^99 := by
    have hnat : (535263949 : ℕ)^131*10000000000000^99 ≤ 4373532880191^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      535263949 1000000000 4373532880191 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5236485853/10000000000 : ℝ)^131 ≤ (10620979450373/25000000000000 : ℝ)^99 := by
    have hnat : (5236485853 : ℕ)^131*25000000000000^99 ≤ 10620979450373^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5236485853 10000000000 10620979450373 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1118141839/5000000000 : ℝ)^131 ≤ (689037669163/5000000000000 : ℝ)^99 := by
    have hnat : (1118141839 : ℕ)^131*5000000000000^99 ≤ 689037669163^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118141839 5000000000 689037669163 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(535263949/1000000000 : ℝ), (5236485853/10000000000 : ℝ), (-1118141839/5000000000 : ℝ)] ![(4373532880191/10000000000000 : ℝ), (10620979450373/25000000000000 : ℝ), (689037669163/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(535263949/1000000000 : ℝ)|^131 ≤ (4373532880191/10000000000000 : ℝ)^99
        have hw : |(535263949/1000000000 : ℝ)|=(535263949/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5236485853/10000000000 : ℝ)|^131 ≤ (10620979450373/25000000000000 : ℝ)^99
        have hw : |(5236485853/10000000000 : ℝ)|=(5236485853/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1118141839/5000000000 : ℝ)|^131 ≤ (689037669163/5000000000000 : ℝ)^99
        have hw : |(-1118141839/5000000000 : ℝ)|=(1118141839/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s3_3 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4355851623/10000000000 : ℝ)*x 0 + (4171226009/10000000000 : ℝ)*x 1 + (4548505077/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355851623/10000000000 : ℝ)^131 ≤ (33297362175071/100000000000000 : ℝ)^99 := by
    have hnat : (4355851623 : ℕ)^131*100000000000000^99 ≤ 33297362175071^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355851623 10000000000 33297362175071 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4171226009/10000000000 : ℝ)^131 ≤ (31442761564303/100000000000000 : ℝ)^99 := by
    have hnat : (4171226009 : ℕ)^131*100000000000000^99 ≤ 31442761564303^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4171226009 10000000000 31442761564303 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4548505077/10000000000 : ℝ)^131 ≤ (7051975247977/20000000000000 : ℝ)^99 := by
    have hnat : (4548505077 : ℕ)^131*20000000000000^99 ≤ 7051975247977^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4548505077 10000000000 7051975247977 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355851623/10000000000 : ℝ), (4171226009/10000000000 : ℝ), (4548505077/10000000000 : ℝ)] ![(33297362175071/100000000000000 : ℝ), (31442761564303/100000000000000 : ℝ), (7051975247977/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355851623/10000000000 : ℝ)|^131 ≤ (33297362175071/100000000000000 : ℝ)^99
        have hw : |(4355851623/10000000000 : ℝ)|=(4355851623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4171226009/10000000000 : ℝ)|^131 ≤ (31442761564303/100000000000000 : ℝ)^99
        have hw : |(4171226009/10000000000 : ℝ)|=(4171226009/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4548505077/10000000000 : ℝ)|^131 ≤ (7051975247977/20000000000000 : ℝ)^99
        have hw : |(4548505077/10000000000 : ℝ)|=(4548505077/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s3_4 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-1070193147/5000000000 : ℝ)*x 0 + (5237190531/10000000000 : ℝ)*x 1 + (1355901743/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1070193147/5000000000 : ℝ)^131 ≤ (13004258299763/100000000000000 : ℝ)^99 := by
    have hnat : (1070193147 : ℕ)^131*100000000000000^99 ≤ 13004258299763^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1070193147 5000000000 13004258299763 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5237190531/10000000000 : ℝ)^131 ≤ (42491483009689/100000000000000 : ℝ)^99 := by
    have hnat : (5237190531 : ℕ)^131*100000000000000^99 ≤ 42491483009689^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5237190531 10000000000 42491483009689 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1355901743/2500000000 : ℝ)^131 ≤ (173844760467/390625000000 : ℝ)^99 := by
    have hnat : (1355901743 : ℕ)^131*390625000000^99 ≤ 173844760467^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1355901743 2500000000 173844760467 390625000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1070193147/5000000000 : ℝ), (5237190531/10000000000 : ℝ), (1355901743/2500000000 : ℝ)] ![(13004258299763/100000000000000 : ℝ), (42491483009689/100000000000000 : ℝ), (173844760467/390625000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1070193147/5000000000 : ℝ)|^131 ≤ (13004258299763/100000000000000 : ℝ)^99
        have hw : |(-1070193147/5000000000 : ℝ)|=(1070193147/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5237190531/10000000000 : ℝ)|^131 ≤ (42491483009689/100000000000000 : ℝ)^99
        have hw : |(5237190531/10000000000 : ℝ)|=(5237190531/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1355901743/2500000000 : ℝ)|^131 ≤ (173844760467/390625000000 : ℝ)^99
        have hw : |(1355901743/2500000000 : ℝ)|=(1355901743/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s3_5 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2652443491/5000000000 : ℝ)*x 0 + (-2049161983/10000000000 : ℝ)*x 1 + (1084721381/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2652443491/5000000000 : ℝ)^131 ≤ (43219781173679/100000000000000 : ℝ)^99 := by
    have hnat : (2652443491 : ℕ)^131*100000000000000^99 ≤ 43219781173679^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2652443491 5000000000 43219781173679 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2049161983/10000000000 : ℝ)^131 ≤ (12275960855183/100000000000000 : ℝ)^99 := by
    have hnat : (2049161983 : ℕ)^131*100000000000000^99 ≤ 12275960855183^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049161983 10000000000 12275960855183 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1084721381/2000000000 : ℝ)^131 ≤ (22252128976033/50000000000000 : ℝ)^99 := by
    have hnat : (1084721381 : ℕ)^131*50000000000000^99 ≤ 22252128976033^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1084721381 2000000000 22252128976033 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2652443491/5000000000 : ℝ), (-2049161983/10000000000 : ℝ), (1084721381/2000000000 : ℝ)] ![(43219781173679/100000000000000 : ℝ), (12275960855183/100000000000000 : ℝ), (22252128976033/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2652443491/5000000000 : ℝ)|^131 ≤ (43219781173679/100000000000000 : ℝ)^99
        have hw : |(2652443491/5000000000 : ℝ)|=(2652443491/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2049161983/10000000000 : ℝ)|^131 ≤ (12275960855183/100000000000000 : ℝ)^99
        have hw : |(-2049161983/10000000000 : ℝ)|=(2049161983/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1084721381/2000000000 : ℝ)|^131 ≤ (22252128976033/50000000000000 : ℝ)^99
        have hw : |(1084721381/2000000000 : ℝ)|=(1084721381/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s3_6 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (1060977323/2000000000 : ℝ)*x 0 + (5423607303/10000000000 : ℝ)*x 1 + (-2049161937/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1060977323/2000000000 : ℝ)^131 ≤ (43219777217203/100000000000000 : ℝ)^99 := by
    have hnat : (1060977323 : ℕ)^131*100000000000000^99 ≤ 43219777217203^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1060977323 2000000000 43219777217203 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5423607303/10000000000 : ℝ)^131 ≤ (44504262273547/100000000000000 : ℝ)^99 := by
    have hnat : (5423607303 : ℕ)^131*100000000000000^99 ≤ 44504262273547^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5423607303 10000000000 44504262273547 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2049161937/10000000000 : ℝ)^131 ≤ (2455192098107/20000000000000 : ℝ)^99 := by
    have hnat : (2049161937 : ℕ)^131*20000000000000^99 ≤ 2455192098107^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2049161937 10000000000 2455192098107 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1060977323/2000000000 : ℝ), (5423607303/10000000000 : ℝ), (-2049161937/10000000000 : ℝ)] ![(43219777217203/100000000000000 : ℝ), (44504262273547/100000000000000 : ℝ), (2455192098107/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1060977323/2000000000 : ℝ)|^131 ≤ (43219777217203/100000000000000 : ℝ)^99
        have hw : |(1060977323/2000000000 : ℝ)|=(1060977323/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5423607303/10000000000 : ℝ)|^131 ≤ (44504262273547/100000000000000 : ℝ)^99
        have hw : |(5423607303/10000000000 : ℝ)|=(5423607303/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2049161937/10000000000 : ℝ)|^131 ≤ (2455192098107/20000000000000 : ℝ)^99
        have hw : |(-2049161937/10000000000 : ℝ)|=(2049161937/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s3_7 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4355884091/10000000000 : ℝ)*x 0 + (4547088111/10000000000 : ℝ)*x 1 + (4172650117/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4355884091/10000000000 : ℝ)^131 ≤ (6659538118911/20000000000000 : ℝ)^99 := by
    have hnat : (4355884091 : ℕ)^131*20000000000000^99 ≤ 6659538118911^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4355884091 10000000000 6659538118911 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4547088111/10000000000 : ℝ)^131 ≤ (17622671109787/50000000000000 : ℝ)^99 := by
    have hnat : (4547088111 : ℕ)^131*50000000000000^99 ≤ 17622671109787^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4547088111 10000000000 17622671109787 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4172650117/10000000000 : ℝ)^131 ≤ (31456967176307/100000000000000 : ℝ)^99 := by
    have hnat : (4172650117 : ℕ)^131*100000000000000^99 ≤ 31456967176307^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4172650117 10000000000 31456967176307 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4355884091/10000000000 : ℝ), (4547088111/10000000000 : ℝ), (4172650117/10000000000 : ℝ)] ![(6659538118911/20000000000000 : ℝ), (17622671109787/50000000000000 : ℝ), (31456967176307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4355884091/10000000000 : ℝ)|^131 ≤ (6659538118911/20000000000000 : ℝ)^99
        have hw : |(4355884091/10000000000 : ℝ)|=(4355884091/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4547088111/10000000000 : ℝ)|^131 ≤ (17622671109787/50000000000000 : ℝ)^99
        have hw : |(4547088111/10000000000 : ℝ)|=(4547088111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4172650117/10000000000 : ℝ)|^131 ≤ (31456967176307/100000000000000 : ℝ)^99
        have hw : |(4172650117/10000000000 : ℝ)|=(4172650117/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1191_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16361/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9287/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (431/4000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14751/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (16361/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (9287/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (16361/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (9287/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (16361/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (9287/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (16361/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (9287/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (16361/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (9287/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (16361/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (9287/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (9287/100000 : ℝ) ^ (8383/2048 : ℝ) ≤ (5959969980666279/100000000000000000000 : ℝ) := by
    have hpowers : (9287/100000 : ℝ)^8383 ≤ (5959969980666279/100000000000000000000 : ℝ)^2048 := by
      have hnat : (9287 : ℕ)^8383*100000000000000000000^2048 ≤ 5959969980666279^2048*100000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9287 100000 5959969980666279 100000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9287/100000 : ℝ)) (X := (5959969980666279/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (16361/100000 : ℝ) ^ (8383/2048 : ℝ) ≤ (30261324857047929/50000000000000000000 : ℝ) := by
    have hpowers : (16361/100000 : ℝ)^8383 ≤ (30261324857047929/50000000000000000000 : ℝ)^2048 := by
      have hnat : (16361 : ℕ)^8383*50000000000000000000^2048 ≤ 30261324857047929^2048*100000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        16361 100000 30261324857047929 50000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (16361/100000 : ℝ)) (X := (30261324857047929/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50005959969980666279/50000000000000000000 : ℝ) ≤ (1000029119572489/1000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50005959969980666279/50000000000000000000 : ℝ)^2048 ≤ (1000029119572489/1000000000000000 : ℝ)^8383 := by
      have hnat : (50005959969980666279 : ℕ)^2048*1000000000000000^8383 ≤ 1000029119572489^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50005959969980666279 50000000000000000000 1000029119572489 1000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000029119572489/1000000000000000 : ℝ)) (X := (50005959969980666279/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (100066482619694762137/100000000000000000000 : ℝ) ≤ (10001623788804757/10000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (100066482619694762137/100000000000000000000 : ℝ)^2048 ≤ (10001623788804757/10000000000000000 : ℝ)^8383 := by
      have hnat : (100066482619694762137 : ℕ)^2048*10000000000000000^8383 ≤ 10001623788804757^8383*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100066482619694762137 100000000000000000000 10001623788804757 10000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001623788804757/10000000000000000 : ℝ)) (X := (100066482619694762137/100000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25030261324857047929/25000000000000000000 : ℝ) ≤ (625184773867789/625000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (25030261324857047929/25000000000000000000 : ℝ)^2048 ≤ (625184773867789/625000000000000 : ℝ)^8383 := by
      have hnat : (25030261324857047929 : ℕ)^2048*625000000000000^8383 ≤ 625184773867789^8383*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25030261324857047929 25000000000000000000 625184773867789 625000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625184773867789/625000000000000 : ℝ)) (X := (25030261324857047929/25000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(5959969980666279/100000000000000000000 : ℝ) ≤ ((3928739351927356789/3930000000000000000 : ℝ)+2*(148065897763/78600000000000 : ℝ)*(9287/100000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (3928739351927356789/3930000000000000000 : ℝ)+2*(148065897763/78600000000000 : ℝ)*(9287/100000 : ℝ)=(1000029119572489/1000000000000000 : ℝ) by norm_num, show 1+2*(5959969980666279/100000000000000000000 : ℝ)=(50005959969980666279/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(30261324857047929/50000000000000000000 : ℝ)+(5959969980666279/100000000000000000000 : ℝ) ≤ ((3928739351927356789/3930000000000000000 : ℝ)+(148065897763/78600000000000 : ℝ)*((16361/100000 : ℝ)+(9287/100000 : ℝ)))^(8383/2048 : ℝ) := by
    rw [show (3928739351927356789/3930000000000000000 : ℝ)+(148065897763/78600000000000 : ℝ)*((16361/100000 : ℝ)+(9287/100000 : ℝ))=(10001623788804757/10000000000000000 : ℝ) by norm_num, show 1+(30261324857047929/50000000000000000000 : ℝ)+(5959969980666279/100000000000000000000 : ℝ)=(100066482619694762137/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(30261324857047929/50000000000000000000 : ℝ) ≤ ((3928739351927356789/3930000000000000000 : ℝ)+2*(148065897763/78600000000000 : ℝ)*(16361/100000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (3928739351927356789/3930000000000000000 : ℝ)+2*(148065897763/78600000000000 : ℝ)*(16361/100000 : ℝ)=(625184773867789/625000000000000 : ℝ) by norm_num, show 1+2*(30261324857047929/50000000000000000000 : ℝ)=(25030261324857047929/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (3928739351927356789/3930000000000000000 : ℝ)*(X 1 0+X 2 0)+(148065897763/78600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (9287/100000 : ℝ)) (hi := (16361/100000 : ℝ)) (c := (3928739351927356789/3930000000000000000 : ℝ)) (alpha := (148065897763/78600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (3928739351927356789/3930000000000000000 : ℝ)*(X 0 1+X 2 1)+(148065897763/78600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (9287/100000 : ℝ)) (hi := (16361/100000 : ℝ)) (c := (3928739351927356789/3930000000000000000 : ℝ)) (alpha := (148065897763/78600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (3928739351927356789/3930000000000000000 : ℝ)*(X 0 2+X 1 2)+(148065897763/78600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (9287/100000 : ℝ)) (hi := (16361/100000 : ℝ)) (c := (3928739351927356789/3930000000000000000 : ℝ)) (alpha := (148065897763/78600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1070185111/5000000000 : ℝ)*X 0 0+(5424316247/10000000000 : ℝ)*X 0 1+(5236485197/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s3_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((669079959/1250000000 : ℝ)*X 1 0+(-1118141923/5000000000 : ℝ)*X 1 1+(5236485541/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s3_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((535263949/1000000000 : ℝ)*X 2 0+(5236485853/10000000000 : ℝ)*X 2 1+(-1118141839/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s3_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((4355851623/10000000000 : ℝ)*X 0 0+(4171226009/10000000000 : ℝ)*X 0 1+(4548505077/10000000000 : ℝ)*X 0 2+(4355851623/10000000000 : ℝ)*X 1 0+(4171226009/10000000000 : ℝ)*X 1 1+(4548505077/10000000000 : ℝ)*X 1 2+(4355851623/10000000000 : ℝ)*X 2 0+(4171226009/10000000000 : ℝ)*X 2 1+(4548505077/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s3_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1070193147/5000000000 : ℝ)*X 0 0+(5237190531/10000000000 : ℝ)*X 0 1+(1355901743/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s3_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((2652443491/5000000000 : ℝ)*X 1 0+(-2049161983/10000000000 : ℝ)*X 1 1+(1084721381/2000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s3_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1060977323/2000000000 : ℝ)*X 2 0+(5423607303/10000000000 : ℝ)*X 2 1+(-2049161937/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s3_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4355884091/10000000000 : ℝ)*X 0 0+(4547088111/10000000000 : ℝ)*X 0 1+(4172650117/10000000000 : ℝ)*X 0 2+(4355884091/10000000000 : ℝ)*X 1 0+(4547088111/10000000000 : ℝ)*X 1 1+(4172650117/10000000000 : ℝ)*X 1 2+(4355884091/10000000000 : ℝ)*X 2 0+(4547088111/10000000000 : ℝ)*X 2 1+(4172650117/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s3_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (769021522366495935371637/62500000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1831651883/100000000000000 : ℝ)*(base19) + (355362201/25000000000000 : ℝ)*(base23) + (122669709/100000000000000 : ℝ)*(lower2) + (12441799/6250000000000 : ℝ)*(upper3) + (34986237/20000000000000 : ℝ)*(upper5) + (996827782640277/25000000000000 : ℝ)*(major0) + (996827782640277/25000000000000 : ℝ)*(major1) + (996827782640277/25000000000000 : ℝ)*(major2) + (665497319300721/12500000000000 : ℝ)*(sp0) + (266201124988569/5000000000000 : ℝ)*(sp1) + (266201145498723/5000000000000 : ℝ)*(sp2) + (33132216567307/1250000000000 : ℝ)*(sp3) + (9155403499/20000000000000 : ℝ)*(sp4) + (20194169571/100000000000000 : ℝ)*(sp7) + (662649379888533/25000000000000 : ℝ)*(f.failure) + (166375760356977/3125000000000 : ℝ)*(f.sum) + (4285042661/5000000000000000000000000 : ℝ)*base66 + (21207849801121/250000000000000000000000000000 : ℝ)*base67 + (1187195749551121/250000000000000000000000000000 : ℝ)*base69 + (3800388040051121/250000000000000000000000000000 : ℝ)*base71 + (23295453291/5000000000000000000000000 : ℝ)*base74 + (3521139463551121/250000000000000000000000000000 : ℝ)*base75 + (1191921469948879/250000000000000000000000000000 : ℝ)*base78 + (182942390051121/250000000000000000000000000000 : ℝ)*base79 + (14856681179/5000000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base84 + (1/100000000000000 : ℝ)*base86 + (1628379/625000000000000000000 : ℝ)*base89 + (1628379/625000000000000000000 : ℝ)*base91 + (1628379/625000000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (11395166343608349155953/1310000000000000000000000000 : ℝ) := by norm_num
    linear_combination (293533709/12500000000000 : ℝ)*(base19) + (2271019051/100000000000000 : ℝ)*(base23) + (85584097/50000000000000 : ℝ)*(upper3) + (7338839/5000000000000 : ℝ)*(lower4) + (293055637/100000000000000 : ℝ)*(upper5) + (4017499042453379/100000000000000 : ℝ)*(major0) + (4017499042453379/100000000000000 : ℝ)*(major1) + (4017499042453379/100000000000000 : ℝ)*(major2) + (23181513611/50000000000000 : ℝ)*(sp1) + (24135666049/50000000000000 : ℝ)*(sp2) + (1341083153831019/25000000000000 : ℝ)*(sp4) + (2682141952013591/50000000000000 : ℝ)*(sp5) + (5364282072972927/100000000000000 : ℝ)*(sp6) + (1335332589814667/50000000000000 : ℝ)*(sp7) + (1335332589814667/50000000000000 : ℝ)*(f.failure) + (1341083153831019/25000000000000 : ℝ)*(f.sum) + (2761312535323/3930000000000000000000000000 : ℝ)*base66 + (78080732933496677/131000000000000000000000000000000 : ℝ)*base67 + (219990737813496677/131000000000000000000000000000000 : ℝ)*base69 + (284559869298503323/131000000000000000000000000000000 : ℝ)*base72 + (8087612392097/3930000000000000000000000000 : ℝ)*base73 + (1010938484673496677/131000000000000000000000000000000 : ℝ)*base75 + (114250203725503323/131000000000000000000000000000000 : ℝ)*base78 + (723216283655503323/131000000000000000000000000000000 : ℝ)*base80 + (15285070673627/3930000000000000000000000000 : ℝ)*base81 + (8506779/1250000000000000000000 : ℝ)*base90 + (8506779/1250000000000000000000 : ℝ)*base92 + (8506779/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1191_s3 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16361/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9287/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (431/4000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1191_s3 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1191_s4_0 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-214300357/1000000000 : ℝ)*x 0 + (5399646243/10000000000 : ℝ)*x 1 + (13148577/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (214300357/1000000000 : ℝ)^131 ≤ (13025304070983/100000000000000 : ℝ)^99 := by
    have hnat : (214300357 : ℕ)^131*100000000000000^99 ≤ 13025304070983^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      214300357 1000000000 13025304070983 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399646243/10000000000 : ℝ)^131 ≤ (44244279251781/100000000000000 : ℝ)^99 := by
    have hnat : (5399646243 : ℕ)^131*100000000000000^99 ≤ 44244279251781^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399646243 10000000000 44244279251781 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13148577/25000000 : ℝ)^131 ≤ (42730416666261/100000000000000 : ℝ)^99 := by
    have hnat : (13148577 : ℕ)^131*100000000000000^99 ≤ 42730416666261^99*25000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13148577 25000000 42730416666261 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-214300357/1000000000 : ℝ), (5399646243/10000000000 : ℝ), (13148577/25000000 : ℝ)] ![(13025304070983/100000000000000 : ℝ), (44244279251781/100000000000000 : ℝ), (42730416666261/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-214300357/1000000000 : ℝ)|^131 ≤ (13025304070983/100000000000000 : ℝ)^99
        have hw : |(-214300357/1000000000 : ℝ)|=(214300357/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399646243/10000000000 : ℝ)|^131 ≤ (44244279251781/100000000000000 : ℝ)^99
        have hw : |(5399646243/10000000000 : ℝ)|=(5399646243/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13148577/25000000 : ℝ)|^131 ≤ (42730416666261/100000000000000 : ℝ)^99
        have hw : |(13148577/25000000 : ℝ)|=(13148577/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s4_1 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (53464493/100000000 : ℝ)*x 0 + (-2214225361/10000000000 : ℝ)*x 1 + (131485763/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (53464493/100000000 : ℝ)^131 ≤ (43668413832789/100000000000000 : ℝ)^99 := by
    have hnat : (53464493 : ℕ)^131*100000000000000^99 ≤ 43668413832789^99*100000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      53464493 100000000 43668413832789 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2214225361/10000000000 : ℝ)^131 ≤ (6800586249161/50000000000000 : ℝ)^99 := by
    have hnat : (2214225361 : ℕ)^131*50000000000000^99 ≤ 6800586249161^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2214225361 10000000000 6800586249161 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (131485763/250000000 : ℝ)^131 ≤ (534130170701/1250000000000 : ℝ)^99 := by
    have hnat : (131485763 : ℕ)^131*1250000000000^99 ≤ 534130170701^99*250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      131485763 250000000 534130170701 1250000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(53464493/100000000 : ℝ), (-2214225361/10000000000 : ℝ), (131485763/250000000 : ℝ)] ![(43668413832789/100000000000000 : ℝ), (6800586249161/50000000000000 : ℝ), (534130170701/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(53464493/100000000 : ℝ)|^131 ≤ (43668413832789/100000000000000 : ℝ)^99
        have hw : |(53464493/100000000 : ℝ)|=(53464493/100000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2214225361/10000000000 : ℝ)|^131 ≤ (6800586249161/50000000000000 : ℝ)^99
        have hw : |(-2214225361/10000000000 : ℝ)|=(2214225361/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(131485763/250000000 : ℝ)|^131 ≤ (534130170701/1250000000000 : ℝ)^99
        have hw : |(131485763/250000000 : ℝ)|=(131485763/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s4_2 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (534644827/1000000000 : ℝ)*x 0 + (5259430979/10000000000 : ℝ)*x 1 + (-553556531/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534644827/1000000000 : ℝ)^131 ≤ (8733680540147/20000000000000 : ℝ)^99 := by
    have hnat : (534644827 : ℕ)^131*20000000000000^99 ≤ 8733680540147^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534644827 1000000000 8733680540147 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5259430979/10000000000 : ℝ)^131 ≤ (21365209295313/50000000000000 : ℝ)^99 := by
    have hnat : (5259430979 : ℕ)^131*50000000000000^99 ≤ 21365209295313^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5259430979 10000000000 21365209295313 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (553556531/2500000000 : ℝ)^131 ≤ (2720235740017/20000000000000 : ℝ)^99 := by
    have hnat : (553556531 : ℕ)^131*20000000000000^99 ≤ 2720235740017^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      553556531 2500000000 2720235740017 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534644827/1000000000 : ℝ), (5259430979/10000000000 : ℝ), (-553556531/2500000000 : ℝ)] ![(8733680540147/20000000000000 : ℝ), (21365209295313/50000000000000 : ℝ), (2720235740017/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534644827/1000000000 : ℝ)|^131 ≤ (8733680540147/20000000000000 : ℝ)^99
        have hw : |(534644827/1000000000 : ℝ)|=(534644827/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5259430979/10000000000 : ℝ)|^131 ≤ (21365209295313/50000000000000 : ℝ)^99
        have hw : |(5259430979/10000000000 : ℝ)|=(5259430979/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-553556531/2500000000 : ℝ)|^131 ≤ (2720235740017/20000000000000 : ℝ)^99
        have hw : |(-553556531/2500000000 : ℝ)|=(553556531/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s4_3 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2178712231/5000000000 : ℝ)*x 0 + (4218843663/10000000000 : ℝ)*x 1 + (562560407/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178712231/5000000000 : ℝ)^131 ≤ (16656636312557/50000000000000 : ℝ)^99 := by
    have hnat : (2178712231 : ℕ)^131*50000000000000^99 ≤ 16656636312557^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178712231 5000000000 16656636312557 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4218843663/10000000000 : ℝ)^131 ≤ (6383720002031/20000000000000 : ℝ)^99 := by
    have hnat : (4218843663 : ℕ)^131*20000000000000^99 ≤ 6383720002031^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4218843663 10000000000 6383720002031 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (562560407/1250000000 : ℝ)^131 ≤ (17384063678969/50000000000000 : ℝ)^99 := by
    have hnat : (562560407 : ℕ)^131*50000000000000^99 ≤ 17384063678969^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      562560407 1250000000 17384063678969 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178712231/5000000000 : ℝ), (4218843663/10000000000 : ℝ), (562560407/1250000000 : ℝ)] ![(16656636312557/50000000000000 : ℝ), (6383720002031/20000000000000 : ℝ), (17384063678969/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178712231/5000000000 : ℝ)|^131 ≤ (16656636312557/50000000000000 : ℝ)^99
        have hw : |(2178712231/5000000000 : ℝ)|=(2178712231/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4218843663/10000000000 : ℝ)|^131 ≤ (6383720002031/20000000000000 : ℝ)^99
        have hw : |(4218843663/10000000000 : ℝ)|=(4218843663/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(562560407/1250000000 : ℝ)|^131 ≤ (17384063678969/50000000000000 : ℝ)^99
        have hw : |(562560407/1250000000 : ℝ)|=(562560407/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s4_4 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2143010247/10000000000 : ℝ)*x 0 + (1051964809/2000000000 : ℝ)*x 1 + (2699625683/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143010247/10000000000 : ℝ)^131 ≤ (651267888601/5000000000000 : ℝ)^99 := by
    have hnat : (2143010247 : ℕ)^131*5000000000000^99 ≤ 651267888601^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143010247 10000000000 651267888601 5000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1051964809/2000000000 : ℝ)^131 ≤ (10683661088593/25000000000000 : ℝ)^99 := by
    have hnat : (1051964809 : ℕ)^131*25000000000000^99 ≤ 10683661088593^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1051964809 2000000000 10683661088593 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699625683/5000000000 : ℝ)^131 ≤ (44239997863427/100000000000000 : ℝ)^99 := by
    have hnat : (2699625683 : ℕ)^131*100000000000000^99 ≤ 44239997863427^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699625683 5000000000 44239997863427 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2143010247/10000000000 : ℝ), (1051964809/2000000000 : ℝ), (2699625683/5000000000 : ℝ)] ![(651267888601/5000000000000 : ℝ), (10683661088593/25000000000000 : ℝ), (44239997863427/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2143010247/10000000000 : ℝ)|^131 ≤ (651267888601/5000000000000 : ℝ)^99
        have hw : |(-2143010247/10000000000 : ℝ)|=(2143010247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1051964809/2000000000 : ℝ)|^131 ≤ (10683661088593/25000000000000 : ℝ)^99
        have hw : |(1051964809/2000000000 : ℝ)|=(1051964809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699625683/5000000000 : ℝ)|^131 ≤ (44239997863427/100000000000000 : ℝ)^99
        have hw : |(2699625683/5000000000 : ℝ)|=(2699625683/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s4_5 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5310800093/10000000000 : ℝ)*x 0 + (-518601231/2500000000 : ℝ)*x 1 + (2699625717/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5310800093/10000000000 : ℝ)^131 ≤ (43283539479737/100000000000000 : ℝ)^99 := by
    have hnat : (5310800093 : ℕ)^131*100000000000000^99 ≤ 43283539479737^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5310800093 10000000000 43283539479737 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (518601231/2500000000 : ℝ)^131 ≤ (12476461903549/100000000000000 : ℝ)^99 := by
    have hnat : (518601231 : ℕ)^131*100000000000000^99 ≤ 12476461903549^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      518601231 2500000000 12476461903549 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2699625717/5000000000 : ℝ)^131 ≤ (44239998600697/100000000000000 : ℝ)^99 := by
    have hnat : (2699625717 : ℕ)^131*100000000000000^99 ≤ 44239998600697^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2699625717 5000000000 44239998600697 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5310800093/10000000000 : ℝ), (-518601231/2500000000 : ℝ), (2699625717/5000000000 : ℝ)] ![(43283539479737/100000000000000 : ℝ), (12476461903549/100000000000000 : ℝ), (44239998600697/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5310800093/10000000000 : ℝ)|^131 ≤ (43283539479737/100000000000000 : ℝ)^99
        have hw : |(5310800093/10000000000 : ℝ)|=(5310800093/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-518601231/2500000000 : ℝ)|^131 ≤ (12476461903549/100000000000000 : ℝ)^99
        have hw : |(-518601231/2500000000 : ℝ)|=(518601231/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2699625717/5000000000 : ℝ)|^131 ≤ (44239998600697/100000000000000 : ℝ)^99
        have hw : |(2699625717/5000000000 : ℝ)|=(2699625717/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s4_6 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2655400223/5000000000 : ℝ)*x 0 + (5399251083/10000000000 : ℝ)*x 1 + (-2074404923/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2655400223/5000000000 : ℝ)^131 ≤ (338152681927/781250000000 : ℝ)^99 := by
    have hnat : (2655400223 : ℕ)^131*781250000000^99 ≤ 338152681927^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2655400223 5000000000 338152681927 781250000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5399251083/10000000000 : ℝ)^131 ≤ (44239994795083/100000000000000 : ℝ)^99 := by
    have hnat : (5399251083 : ℕ)^131*100000000000000^99 ≤ 44239994795083^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5399251083 10000000000 44239994795083 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2074404923/10000000000 : ℝ)^131 ≤ (12476461895591/100000000000000 : ℝ)^99 := by
    have hnat : (2074404923 : ℕ)^131*100000000000000^99 ≤ 12476461895591^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2074404923 10000000000 12476461895591 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2655400223/5000000000 : ℝ), (5399251083/10000000000 : ℝ), (-2074404923/10000000000 : ℝ)] ![(338152681927/781250000000 : ℝ), (44239994795083/100000000000000 : ℝ), (12476461895591/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2655400223/5000000000 : ℝ)|^131 ≤ (338152681927/781250000000 : ℝ)^99
        have hw : |(2655400223/5000000000 : ℝ)|=(2655400223/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5399251083/10000000000 : ℝ)|^131 ≤ (44239994795083/100000000000000 : ℝ)^99
        have hw : |(5399251083/10000000000 : ℝ)|=(5399251083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2074404923/10000000000 : ℝ)|^131 ≤ (12476461895591/100000000000000 : ℝ)^99
        have hw : |(-2074404923/10000000000 : ℝ)|=(2074404923/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s4_7 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (2178719277/5000000000 : ℝ)*x 0 + (4499692111/10000000000 : ℝ)*x 1 + (4219637219/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2178719277/5000000000 : ℝ)^131 ≤ (3331341518469/10000000000000 : ℝ)^99 := by
    have hnat : (2178719277 : ℕ)^131*10000000000000^99 ≤ 3331341518469^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2178719277 5000000000 3331341518469 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4499692111/10000000000 : ℝ)^131 ≤ (34760040086887/100000000000000 : ℝ)^99 := by
    have hnat : (4499692111 : ℕ)^131*100000000000000^99 ≤ 34760040086887^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4499692111 10000000000 34760040086887 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4219637219/10000000000 : ℝ)^131 ≤ (3192654470617/10000000000000 : ℝ)^99 := by
    have hnat : (4219637219 : ℕ)^131*10000000000000^99 ≤ 3192654470617^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4219637219 10000000000 3192654470617 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2178719277/5000000000 : ℝ), (4499692111/10000000000 : ℝ), (4219637219/10000000000 : ℝ)] ![(3331341518469/10000000000000 : ℝ), (34760040086887/100000000000000 : ℝ), (3192654470617/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2178719277/5000000000 : ℝ)|^131 ≤ (3331341518469/10000000000000 : ℝ)^99
        have hw : |(2178719277/5000000000 : ℝ)|=(2178719277/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4499692111/10000000000 : ℝ)|^131 ≤ (34760040086887/100000000000000 : ℝ)^99
        have hw : |(4499692111/10000000000 : ℝ)|=(4499692111/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4219637219/10000000000 : ℝ)|^131 ≤ (3192654470617/10000000000000 : ℝ)^99
        have hw : |(4219637219/10000000000 : ℝ)|=(4219637219/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1191_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (431/4000 : ℝ)*pair X i i ≤ pair X i h) :
    (2253/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (2847/20000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (431/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (431/4000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (431/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (14751/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (431/4000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (431/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (14751/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (431/4000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (431/4000 : ℝ) ^ (8383/2048 : ℝ) ≤ (10950417755803807/100000000000000000000 : ℝ) := by
    have hpowers : (431/4000 : ℝ)^8383 ≤ (10950417755803807/100000000000000000000 : ℝ)^2048 := by
      have hnat : (431 : ℕ)^8383*100000000000000000000^2048 ≤ 10950417755803807^2048*4000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        431 4000 10950417755803807 100000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (431/4000 : ℝ)) (X := (10950417755803807/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (14751/100000 : ℝ) ^ (8383/2048 : ℝ) ≤ (39606704948795589/100000000000000000000 : ℝ) := by
    have hpowers : (14751/100000 : ℝ)^8383 ≤ (39606704948795589/100000000000000000000 : ℝ)^2048 := by
      have hnat : (14751 : ℕ)^8383*100000000000000000000^2048 ≤ 39606704948795589^2048*100000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        14751 100000 39606704948795589 100000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (14751/100000 : ℝ)) (X := (39606704948795589/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50010950417755803807/50000000000000000000 : ℝ) ≤ (1250066875223579/1250000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50010950417755803807/50000000000000000000 : ℝ)^2048 ≤ (1250066875223579/1250000000000000 : ℝ)^8383 := by
      have hnat : (50010950417755803807 : ℕ)^2048*1250000000000000^8383 ≤ 1250066875223579^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50010950417755803807 50000000000000000000 1250066875223579 1250000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250066875223579/1250000000000000 : ℝ)) (X := (50010950417755803807/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (25012639280676149849/25000000000000000000 : ℝ) ≤ (2500308723648481/2500000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (25012639280676149849/25000000000000000000 : ℝ)^2048 ≤ (2500308723648481/2500000000000000 : ℝ)^8383 := by
      have hnat : (25012639280676149849 : ℕ)^2048*2500000000000000^8383 ≤ 2500308723648481^8383*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25012639280676149849 25000000000000000000 2500308723648481 2500000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2500308723648481/2500000000000000 : ℝ)) (X := (25012639280676149849/25000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (50039606704948795589/50000000000000000000 : ℝ) ≤ (625120924212451/625000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (50039606704948795589/50000000000000000000 : ℝ)^2048 ≤ (625120924212451/625000000000000 : ℝ)^8383 := by
      have hnat : (50039606704948795589 : ℕ)^2048*625000000000000^8383 ≤ 625120924212451^8383*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50039606704948795589 50000000000000000000 625120924212451 625000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625120924212451/625000000000000 : ℝ)) (X := (50039606704948795589/50000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(10950417755803807/100000000000000000000 : ℝ) ≤ ((4968380559644694779/4970000000000000000 : ℝ)+2*(174973201323/99400000000000 : ℝ)*(431/4000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (4968380559644694779/4970000000000000000 : ℝ)+2*(174973201323/99400000000000 : ℝ)*(431/4000 : ℝ)=(1250066875223579/1250000000000000 : ℝ) by norm_num, show 1+2*(10950417755803807/100000000000000000000 : ℝ)=(50010950417755803807/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(39606704948795589/100000000000000000000 : ℝ)+(10950417755803807/100000000000000000000 : ℝ) ≤ ((4968380559644694779/4970000000000000000 : ℝ)+(174973201323/99400000000000 : ℝ)*((14751/100000 : ℝ)+(431/4000 : ℝ)))^(8383/2048 : ℝ) := by
    rw [show (4968380559644694779/4970000000000000000 : ℝ)+(174973201323/99400000000000 : ℝ)*((14751/100000 : ℝ)+(431/4000 : ℝ))=(2500308723648481/2500000000000000 : ℝ) by norm_num, show 1+(39606704948795589/100000000000000000000 : ℝ)+(10950417755803807/100000000000000000000 : ℝ)=(25012639280676149849/25000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(39606704948795589/100000000000000000000 : ℝ) ≤ ((4968380559644694779/4970000000000000000 : ℝ)+2*(174973201323/99400000000000 : ℝ)*(14751/100000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (4968380559644694779/4970000000000000000 : ℝ)+2*(174973201323/99400000000000 : ℝ)*(14751/100000 : ℝ)=(625120924212451/625000000000000 : ℝ) by norm_num, show 1+2*(39606704948795589/100000000000000000000 : ℝ)=(50039606704948795589/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (4968380559644694779/4970000000000000000 : ℝ)*(X 1 0+X 2 0)+(174973201323/99400000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (431/4000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (4968380559644694779/4970000000000000000 : ℝ)) (alpha := (174973201323/99400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (4968380559644694779/4970000000000000000 : ℝ)*(X 0 1+X 2 1)+(174973201323/99400000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (431/4000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (4968380559644694779/4970000000000000000 : ℝ)) (alpha := (174973201323/99400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (4968380559644694779/4970000000000000000 : ℝ)*(X 0 2+X 1 2)+(174973201323/99400000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (431/4000 : ℝ)) (hi := (14751/100000 : ℝ)) (c := (4968380559644694779/4970000000000000000 : ℝ)) (alpha := (174973201323/99400000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-214300357/1000000000 : ℝ)*X 0 0+(5399646243/10000000000 : ℝ)*X 0 1+(13148577/25000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s4_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((53464493/100000000 : ℝ)*X 1 0+(-2214225361/10000000000 : ℝ)*X 1 1+(131485763/250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s4_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534644827/1000000000 : ℝ)*X 2 0+(5259430979/10000000000 : ℝ)*X 2 1+(-553556531/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s4_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2178712231/5000000000 : ℝ)*X 0 0+(4218843663/10000000000 : ℝ)*X 0 1+(562560407/1250000000 : ℝ)*X 0 2+(2178712231/5000000000 : ℝ)*X 1 0+(4218843663/10000000000 : ℝ)*X 1 1+(562560407/1250000000 : ℝ)*X 1 2+(2178712231/5000000000 : ℝ)*X 2 0+(4218843663/10000000000 : ℝ)*X 2 1+(562560407/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s4_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2143010247/10000000000 : ℝ)*X 0 0+(1051964809/2000000000 : ℝ)*X 0 1+(2699625683/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s4_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5310800093/10000000000 : ℝ)*X 1 0+(-518601231/2500000000 : ℝ)*X 1 1+(2699625717/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s4_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((2655400223/5000000000 : ℝ)*X 2 0+(5399251083/10000000000 : ℝ)*X 2 1+(-2074404923/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s4_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2178719277/5000000000 : ℝ)*X 0 0+(4499692111/10000000000 : ℝ)*X 0 1+(4219637219/10000000000 : ℝ)*X 0 2+(2178719277/5000000000 : ℝ)*X 1 0+(4499692111/10000000000 : ℝ)*X 1 1+(4219637219/10000000000 : ℝ)*X 1 2+(2178719277/5000000000 : ℝ)*X 2 0+(4499692111/10000000000 : ℝ)*X 2 1+(4219637219/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s4_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (569635245344301908496903729/62125000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (22532081/2000000000000 : ℝ)*(base19) + (2713171/50000000000000 : ℝ)*(base23) + (247496329/100000000000000 : ℝ)*(upper2) + (178095629/100000000000000 : ℝ)*(upper3) + (2670652563310017/50000000000000 : ℝ)*(major0) + (2670652563310017/50000000000000 : ℝ)*(major1) + (2670652563310017/50000000000000 : ℝ)*(major2) + (1782980680984877/25000000000000 : ℝ)*(sp0) + (285277310994167/4000000000000 : ℝ)*(sp1) + (3565951191217657/50000000000000 : ℝ)*(sp2) + (1775329816181033/50000000000000 : ℝ)*(sp3) + (11177518717/100000000000000 : ℝ)*(sp4) + (31513596569/100000000000000 : ℝ)*(sp6) + (4103445117/25000000000000 : ℝ)*(sp7) + (1775338023071267/50000000000000 : ℝ)*(f.failure) + (285277356058329/4000000000000 : ℝ)*(f.sum) + (4524869966717/1242500000000000000000000000 : ℝ)*base66 + (2955793496584648757/248500000000000000000000000000000 : ℝ)*base68 + (2504635483142148757/248500000000000000000000000000000 : ℝ)*base70 + (1242749473438851243/248500000000000000000000000000000 : ℝ)*base71 + (4336265905511/621250000000000000000000000 : ℝ)*base74 + (2400155441875148757/248500000000000000000000000000000 : ℝ)*base76 + (24761816480148757/248500000000000000000000000000000 : ℝ)*base78 + (7594768615698648757/248500000000000000000000000000000 : ℝ)*base80 + (5954823655517/1242500000000000000000000000 : ℝ)*base82 + (9319021/1250000000000000000000 : ℝ)*base89 + (9319021/1250000000000000000000 : ℝ)*base91 + (9319021/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (503256560159389995264226269/49700000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (2053566871/100000000000000 : ℝ)*(base19) + (1251449041/50000000000000 : ℝ)*(base23) + (21299773/12500000000000 : ℝ)*(upper3) + (539387/100000000000000 : ℝ)*(lower4) + (366460041/100000000000000 : ℝ)*(upper5) + (1074293587583437/20000000000000 : ℝ)*(major0) + (1074293587583437/20000000000000 : ℝ)*(major1) + (1074293587583437/20000000000000 : ℝ)*(major2) + (29436487567/50000000000000 : ℝ)*(sp1) + (6830362597/12500000000000 : ℝ)*(sp2) + (717220851791193/10000000000000 : ℝ)*(sp4) + (286885903654797/4000000000000 : ℝ)*(sp5) + (448259460757067/6250000000000 : ℝ)*(sp6) + (1785363510196441/50000000000000 : ℝ)*(sp7) + (1785363510196441/50000000000000 : ℝ)*(f.failure) + (717220851791193/10000000000000 : ℝ)*(f.sum) + (6549842075341/994000000000000000000000000 : ℝ)*base66 + (332212160330474577/99400000000000000000000000000000 : ℝ)*base68 + (807300502458874577/99400000000000000000000000000000 : ℝ)*base70 + (2060695767769874577/99400000000000000000000000000000 : ℝ)*base72 + (3055776921881/994000000000000000000000000 : ℝ)*base74 + (880390651991125423/99400000000000000000000000000000 : ℝ)*base75 + (926320941425674577/99400000000000000000000000000000 : ℝ)*base78 + (551887240567525423/99400000000000000000000000000000 : ℝ)*base79 + (3409720093981/994000000000000000000000000 : ℝ)*base82 + (4427383/1250000000000000000000 : ℝ)*base89 + (4427383/1250000000000000000000 : ℝ)*base91 + (4427383/1250000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1191_s4 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (14751/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (431/4000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1191_s4 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1191_s5_0 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-2143538953/10000000000 : ℝ)*x 0 + (1078732599/2000000000 : ℝ)*x 1 + (5265062551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2143538953/10000000000 : ℝ)^131 ≤ (13029610161829/100000000000000 : ℝ)^99 := by
    have hnat : (2143538953 : ℕ)^131*100000000000000^99 ≤ 13029610161829^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2143538953 10000000000 13029610161829 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1078732599/2000000000 : ℝ)^131 ≤ (4417941773199/10000000000000 : ℝ)^99 := by
    have hnat : (1078732599 : ℕ)^131*10000000000000^99 ≤ 4417941773199^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078732599 2000000000 4417941773199 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5265062551/10000000000 : ℝ)^131 ≤ (42790972091933/100000000000000 : ℝ)^99 := by
    have hnat : (5265062551 : ℕ)^131*100000000000000^99 ≤ 42790972091933^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265062551 10000000000 42790972091933 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2143538953/10000000000 : ℝ), (1078732599/2000000000 : ℝ), (5265062551/10000000000 : ℝ)] ![(13029610161829/100000000000000 : ℝ), (4417941773199/10000000000000 : ℝ), (42790972091933/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2143538953/10000000000 : ℝ)|^131 ≤ (13029610161829/100000000000000 : ℝ)^99
        have hw : |(-2143538953/10000000000 : ℝ)|=(2143538953/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1078732599/2000000000 : ℝ)|^131 ≤ (4417941773199/10000000000000 : ℝ)^99
        have hw : |(1078732599/2000000000 : ℝ)|=(1078732599/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5265062551/10000000000 : ℝ)|^131 ≤ (42790972091933/100000000000000 : ℝ)^99
        have hw : |(5265062551/10000000000 : ℝ)|=(5265062551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s5_1 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5344942241/10000000000 : ℝ)*x 0 + (-441755319/2000000000 : ℝ)*x 1 + (658132813/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5344942241/10000000000 : ℝ)^131 ≤ (5456515819233/12500000000000 : ℝ)^99 := by
    have hnat : (5344942241 : ℕ)^131*12500000000000^99 ≤ 5456515819233^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5344942241 10000000000 5456515819233 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (441755319/2000000000 : ℝ)^131 ≤ (108455214757/800000000000 : ℝ)^99 := by
    have hnat : (441755319 : ℕ)^131*800000000000^99 ≤ 108455214757^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      441755319 2000000000 108455214757 800000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (658132813/1250000000 : ℝ)^131 ≤ (21395485793239/50000000000000 : ℝ)^99 := by
    have hnat : (658132813 : ℕ)^131*50000000000000^99 ≤ 21395485793239^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      658132813 1250000000 21395485793239 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5344942241/10000000000 : ℝ), (-441755319/2000000000 : ℝ), (658132813/1250000000 : ℝ)] ![(5456515819233/12500000000000 : ℝ), (108455214757/800000000000 : ℝ), (21395485793239/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5344942241/10000000000 : ℝ)|^131 ≤ (5456515819233/12500000000000 : ℝ)^99
        have hw : |(5344942241/10000000000 : ℝ)|=(5344942241/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-441755319/2000000000 : ℝ)|^131 ≤ (108455214757/800000000000 : ℝ)^99
        have hw : |(-441755319/2000000000 : ℝ)|=(441755319/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(658132813/1250000000 : ℝ)|^131 ≤ (21395485793239/50000000000000 : ℝ)^99
        have hw : |(658132813/1250000000 : ℝ)|=(658132813/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s5_2 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (534494223/1000000000 : ℝ)*x 0 + (5265062523/10000000000 : ℝ)*x 1 + (-276097073/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (534494223/1000000000 : ℝ)^131 ≤ (43652126434989/100000000000000 : ℝ)^99 := by
    have hnat : (534494223 : ℕ)^131*100000000000000^99 ≤ 43652126434989^99*1000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      534494223 1000000000 43652126434989 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265062523/10000000000 : ℝ)^131 ≤ (4279097179081/10000000000000 : ℝ)^99 := by
    have hnat : (5265062523 : ℕ)^131*10000000000000^99 ≤ 4279097179081^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265062523 10000000000 4279097179081 10000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276097073/1250000000 : ℝ)^131 ≤ (13556901755287/100000000000000 : ℝ)^99 := by
    have hnat : (276097073 : ℕ)^131*100000000000000^99 ≤ 13556901755287^99*1250000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276097073 1250000000 13556901755287 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(534494223/1000000000 : ℝ), (5265062523/10000000000 : ℝ), (-276097073/1250000000 : ℝ)] ![(43652126434989/100000000000000 : ℝ), (4279097179081/10000000000000 : ℝ), (13556901755287/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(534494223/1000000000 : ℝ)|^131 ≤ (43652126434989/100000000000000 : ℝ)^99
        have hw : |(534494223/1000000000 : ℝ)|=(534494223/1000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265062523/10000000000 : ℝ)|^131 ≤ (4279097179081/10000000000000 : ℝ)^99
        have hw : |(5265062523/10000000000 : ℝ)|=(5265062523/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276097073/1250000000 : ℝ)|^131 ≤ (13556901755287/100000000000000 : ℝ)^99
        have hw : |(-276097073/1250000000 : ℝ)|=(276097073/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s5_3 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (871547951/2000000000 : ℝ)*x 0 + (1057617079/2500000000 : ℝ)*x 1 + (4488776893/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (871547951/2000000000 : ℝ)^131 ≤ (33316462274451/100000000000000 : ℝ)^99 := by
    have hnat : (871547951 : ℕ)^131*100000000000000^99 ≤ 33316462274451^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      871547951 2000000000 33316462274451 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1057617079/2500000000 : ℝ)^131 ≤ (32035028626919/100000000000000 : ℝ)^99 := by
    have hnat : (1057617079 : ℕ)^131*100000000000000^99 ≤ 32035028626919^99*2500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1057617079 2500000000 32035028626919 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4488776893/10000000000 : ℝ)^131 ≤ (17324254543451/50000000000000 : ℝ)^99 := by
    have hnat : (4488776893 : ℕ)^131*50000000000000^99 ≤ 17324254543451^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488776893 10000000000 17324254543451 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(871547951/2000000000 : ℝ), (1057617079/2500000000 : ℝ), (4488776893/10000000000 : ℝ)] ![(33316462274451/100000000000000 : ℝ), (32035028626919/100000000000000 : ℝ), (17324254543451/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(871547951/2000000000 : ℝ)|^131 ≤ (33316462274451/100000000000000 : ℝ)^99
        have hw : |(871547951/2000000000 : ℝ)|=(871547951/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1057617079/2500000000 : ℝ)|^131 ≤ (32035028626919/100000000000000 : ℝ)^99
        have hw : |(1057617079/2500000000 : ℝ)|=(1057617079/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4488776893/10000000000 : ℝ)|^131 ≤ (17324254543451/50000000000000 : ℝ)^99
        have hw : |(4488776893/10000000000 : ℝ)|=(4488776893/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s5_4 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (-428708809/2000000000 : ℝ)*x 0 + (5265393807/10000000000 : ℝ)*x 1 + (168541579/312500000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (428708809/2000000000 : ℝ)^131 ≤ (2605930223701/20000000000000 : ℝ)^99 := by
    have hnat : (428708809 : ℕ)^131*20000000000000^99 ≤ 2605930223701^99*2000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      428708809 2000000000 2605930223701 20000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5265393807/10000000000 : ℝ)^131 ≤ (42794534575647/100000000000000 : ℝ)^99 := by
    have hnat : (5265393807 : ℕ)^131*100000000000000^99 ≤ 42794534575647^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5265393807 10000000000 42794534575647 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (168541579/312500000 : ℝ)^131 ≤ (44175814298593/100000000000000 : ℝ)^99 := by
    have hnat : (168541579 : ℕ)^131*100000000000000^99 ≤ 44175814298593^99*312500000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      168541579 312500000 44175814298593 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-428708809/2000000000 : ℝ), (5265393807/10000000000 : ℝ), (168541579/312500000 : ℝ)] ![(2605930223701/20000000000000 : ℝ), (42794534575647/100000000000000 : ℝ), (44175814298593/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-428708809/2000000000 : ℝ)|^131 ≤ (2605930223701/20000000000000 : ℝ)^99
        have hw : |(-428708809/2000000000 : ℝ)|=(428708809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5265393807/10000000000 : ℝ)|^131 ≤ (42794534575647/100000000000000 : ℝ)^99
        have hw : |(5265393807/10000000000 : ℝ)|=(5265393807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(168541579/312500000 : ℝ)|^131 ≤ (44175814298593/100000000000000 : ℝ)^99
        have hw : |(168541579/312500000 : ℝ)|=(168541579/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s5_5 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (265612259/500000000 : ℝ)*x 0 + (-104025427/500000000 : ℝ)*x 1 + (5393330537/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (265612259/500000000 : ℝ)^131 ≤ (43299124666313/100000000000000 : ℝ)^99 := by
    have hnat : (265612259 : ℕ)^131*100000000000000^99 ≤ 43299124666313^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      265612259 500000000 43299124666313 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (104025427/500000000 : ℝ)^131 ≤ (12525060927649/100000000000000 : ℝ)^99 := by
    have hnat : (104025427 : ℕ)^131*100000000000000^99 ≤ 12525060927649^99*500000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      104025427 500000000 12525060927649 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5393330537/10000000000 : ℝ)^131 ≤ (22087907198069/50000000000000 : ℝ)^99 := by
    have hnat : (5393330537 : ℕ)^131*50000000000000^99 ≤ 22087907198069^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5393330537 10000000000 22087907198069 50000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(265612259/500000000 : ℝ), (-104025427/500000000 : ℝ), (5393330537/10000000000 : ℝ)] ![(43299124666313/100000000000000 : ℝ), (12525060927649/100000000000000 : ℝ), (22087907198069/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(265612259/500000000 : ℝ)|^131 ≤ (43299124666313/100000000000000 : ℝ)^99
        have hw : |(265612259/500000000 : ℝ)|=(265612259/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-104025427/500000000 : ℝ)|^131 ≤ (12525060927649/100000000000000 : ℝ)^99
        have hw : |(-104025427/500000000 : ℝ)|=(104025427/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5393330537/10000000000 : ℝ)|^131 ≤ (22087907198069/50000000000000 : ℝ)^99
        have hw : |(5393330537/10000000000 : ℝ)|=(5393330537/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s5_6 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (5312245179/10000000000 : ℝ)*x 0 + (2696665269/5000000000 : ℝ)*x 1 + (-1040254269/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5312245179/10000000000 : ℝ)^131 ≤ (5412390581941/12500000000000 : ℝ)^99 := by
    have hnat : (5312245179 : ℕ)^131*12500000000000^99 ≤ 5412390581941^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5312245179 10000000000 5412390581941 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2696665269/5000000000 : ℝ)^131 ≤ (44175814406977/100000000000000 : ℝ)^99 := by
    have hnat : (2696665269 : ℕ)^131*100000000000000^99 ≤ 44175814406977^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2696665269 5000000000 44175814406977 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1040254269/5000000000 : ℝ)^131 ≤ (12525060911717/100000000000000 : ℝ)^99 := by
    have hnat : (1040254269 : ℕ)^131*100000000000000^99 ≤ 12525060911717^99*5000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1040254269 5000000000 12525060911717 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5312245179/10000000000 : ℝ), (2696665269/5000000000 : ℝ), (-1040254269/5000000000 : ℝ)] ![(5412390581941/12500000000000 : ℝ), (44175814406977/100000000000000 : ℝ), (12525060911717/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5312245179/10000000000 : ℝ)|^131 ≤ (5412390581941/12500000000000 : ℝ)^99
        have hw : |(5312245179/10000000000 : ℝ)|=(5312245179/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2696665269/5000000000 : ℝ)|^131 ≤ (44175814406977/100000000000000 : ℝ)^99
        have hw : |(2696665269/5000000000 : ℝ)|=(2696665269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-1040254269/5000000000 : ℝ)|^131 ≤ (12525060911717/100000000000000 : ℝ)^99
        have hw : |(-1040254269/5000000000 : ℝ)|=(1040254269/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1191_s5_7 (p : ℝ) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ)) (x : Fin 3 → ℝ) :
    (4357750073/10000000000 : ℝ)*x 0 + (4488111541/10000000000 : ℝ)*x 1 + (4231136087/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4357750073/10000000000 : ℝ)^131 ≤ (8329141664339/25000000000000 : ℝ)^99 := by
    have hnat : (4357750073 : ℕ)^131*25000000000000^99 ≤ 8329141664339^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4357750073 10000000000 8329141664339 25000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4488111541/10000000000 : ℝ)^131 ≤ (4330214174347/12500000000000 : ℝ)^99 := by
    have hnat : (4488111541 : ℕ)^131*12500000000000^99 ≤ 4330214174347^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4488111541 10000000000 4330214174347 12500000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4231136087/10000000000 : ℝ)^131 ≤ (32041719940821/100000000000000 : ℝ)^99 := by
    have hnat : (4231136087 : ℕ)^131*100000000000000^99 ≤ 32041719940821^99*10000000000^131 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4231136087 10000000000 32041719940821 100000000000000 131 99 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (131/32 : ℝ)) 131 99 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4357750073/10000000000 : ℝ), (4488111541/10000000000 : ℝ), (4231136087/10000000000 : ℝ)] ![(8329141664339/25000000000000 : ℝ), (4330214174347/12500000000000 : ℝ), (32041719940821/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4357750073/10000000000 : ℝ)|^131 ≤ (8329141664339/25000000000000 : ℝ)^99
        have hw : |(4357750073/10000000000 : ℝ)|=(4357750073/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4488111541/10000000000 : ℝ)|^131 ≤ (4330214174347/12500000000000 : ℝ)^99
        have hw : |(4488111541/10000000000 : ℝ)|=(4488111541/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4231136087/10000000000 : ℝ)|^131 ≤ (32041719940821/100000000000000 : ℝ)^99
        have hw : |(4231136087/10000000000 : ℝ)|=(4231136087/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1191_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h) :
    (2277/20000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (14109/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (2253/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (2253/20000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (2253/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (2847/20000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (2253/20000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (2253/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (2847/20000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (2253/20000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (2253/20000 : ℝ) ^ (8383/2048 : ℝ) ≤ (1642092504645087/12500000000000000000 : ℝ) := by
    have hpowers : (2253/20000 : ℝ)^8383 ≤ (1642092504645087/12500000000000000000 : ℝ)^2048 := by
      have hnat : (2253 : ℕ)^8383*12500000000000000000^2048 ≤ 1642092504645087^2048*20000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2253 20000 1642092504645087 12500000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2253/20000 : ℝ)) (X := (1642092504645087/12500000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2847/20000 : ℝ) ^ (8383/2048 : ℝ) ≤ (17117508527416547/50000000000000000000 : ℝ) := by
    have hpowers : (2847/20000 : ℝ)^8383 ≤ (17117508527416547/50000000000000000000 : ℝ)^2048 := by
      have hnat : (2847 : ℕ)^8383*50000000000000000000^2048 ≤ 17117508527416547^2048*20000^8383 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2847 20000 17117508527416547 50000000000000000000 8383 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2847/20000 : ℝ)) (X := (17117508527416547/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (6251642092504645087/6250000000000000000 : ℝ) ≤ (10000641807780971/10000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (6251642092504645087/6250000000000000000 : ℝ)^2048 ≤ (10000641807780971/10000000000000000 : ℝ)^8383 := by
      have hnat : (6251642092504645087 : ℕ)^2048*10000000000000000^8383 ≤ 10000641807780971^8383*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6251642092504645087 6250000000000000000 10000641807780971 10000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10000641807780971/10000000000000000 : ℝ)) (X := (6251642092504645087/6250000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (10004737175709199379/10000000000000000000 : ℝ) ≤ (625072318977309/625000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (10004737175709199379/10000000000000000000 : ℝ)^2048 ≤ (625072318977309/625000000000000 : ℝ)^8383 := by
      have hnat : (10004737175709199379 : ℕ)^2048*625000000000000^8383 ≤ 625072318977309^8383*10000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        10004737175709199379 10000000000000000000 625072318977309 625000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (625072318977309/625000000000000 : ℝ)) (X := (10004737175709199379/10000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25017117508527416547/25000000000000000000 : ℝ) ≤ (10001672399492917/10000000000000000 : ℝ) ^ (8383/2048 : ℝ) := by
    have hpowers : (25017117508527416547/25000000000000000000 : ℝ)^2048 ≤ (10001672399492917/10000000000000000 : ℝ)^8383 := by
      have hnat : (25017117508527416547 : ℕ)^2048*10000000000000000^8383 ≤ 10001672399492917^8383*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25017117508527416547 25000000000000000000 10001672399492917 10000000000000000 2048 8383 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10001672399492917/10000000000000000 : ℝ)) (X := (25017117508527416547/25000000000000000000 : ℝ)) (by norm_num) 8383 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(1642092504645087/12500000000000000000 : ℝ) ≤ ((494838275891240203/495000000000000000 : ℝ)+2*(515295855973/297000000000000 : ℝ)*(2253/20000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (494838275891240203/495000000000000000 : ℝ)+2*(515295855973/297000000000000 : ℝ)*(2253/20000 : ℝ)=(10000641807780971/10000000000000000 : ℝ) by norm_num, show 1+2*(1642092504645087/12500000000000000000 : ℝ)=(6251642092504645087/6250000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(17117508527416547/50000000000000000000 : ℝ)+(1642092504645087/12500000000000000000 : ℝ) ≤ ((494838275891240203/495000000000000000 : ℝ)+(515295855973/297000000000000 : ℝ)*((2847/20000 : ℝ)+(2253/20000 : ℝ)))^(8383/2048 : ℝ) := by
    rw [show (494838275891240203/495000000000000000 : ℝ)+(515295855973/297000000000000 : ℝ)*((2847/20000 : ℝ)+(2253/20000 : ℝ))=(625072318977309/625000000000000 : ℝ) by norm_num, show 1+(17117508527416547/50000000000000000000 : ℝ)+(1642092504645087/12500000000000000000 : ℝ)=(10004737175709199379/10000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(17117508527416547/50000000000000000000 : ℝ) ≤ ((494838275891240203/495000000000000000 : ℝ)+2*(515295855973/297000000000000 : ℝ)*(2847/20000 : ℝ))^(8383/2048 : ℝ) := by
    rw [show (494838275891240203/495000000000000000 : ℝ)+2*(515295855973/297000000000000 : ℝ)*(2847/20000 : ℝ)=(10001672399492917/10000000000000000 : ℝ) by norm_num, show 1+2*(17117508527416547/50000000000000000000 : ℝ)=(25017117508527416547/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (494838275891240203/495000000000000000 : ℝ)*(X 1 0+X 2 0)+(515295855973/297000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (2253/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (494838275891240203/495000000000000000 : ℝ)) (alpha := (515295855973/297000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (494838275891240203/495000000000000000 : ℝ)*(X 0 1+X 2 1)+(515295855973/297000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (2253/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (494838275891240203/495000000000000000 : ℝ)) (alpha := (515295855973/297000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (494838275891240203/495000000000000000 : ℝ)*(X 0 2+X 1 2)+(515295855973/297000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8383/2048 : ℝ)) (lo := (2253/20000 : ℝ)) (hi := (2847/20000 : ℝ)) (c := (494838275891240203/495000000000000000 : ℝ)) (alpha := (515295855973/297000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-2143538953/10000000000 : ℝ)*X 0 0+(1078732599/2000000000 : ℝ)*X 0 1+(5265062551/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s5_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5344942241/10000000000 : ℝ)*X 1 0+(-441755319/2000000000 : ℝ)*X 1 1+(658132813/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s5_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((534494223/1000000000 : ℝ)*X 2 0+(5265062523/10000000000 : ℝ)*X 2 1+(-276097073/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s5_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((871547951/2000000000 : ℝ)*X 0 0+(1057617079/2500000000 : ℝ)*X 0 1+(4488776893/10000000000 : ℝ)*X 0 2+(871547951/2000000000 : ℝ)*X 1 0+(1057617079/2500000000 : ℝ)*X 1 1+(4488776893/10000000000 : ℝ)*X 1 2+(871547951/2000000000 : ℝ)*X 2 0+(1057617079/2500000000 : ℝ)*X 2 1+(4488776893/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s5_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-428708809/2000000000 : ℝ)*X 0 0+(5265393807/10000000000 : ℝ)*X 0 1+(168541579/312500000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s5_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((265612259/500000000 : ℝ)*X 1 0+(-104025427/500000000 : ℝ)*X 1 1+(5393330537/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s5_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5312245179/10000000000 : ℝ)*X 2 0+(2696665269/5000000000 : ℝ)*X 2 1+(-1040254269/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s5_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4357750073/10000000000 : ℝ)*X 0 0+(4488111541/10000000000 : ℝ)*X 0 1+(4231136087/10000000000 : ℝ)*X 0 2+(4357750073/10000000000 : ℝ)*X 1 0+(4488111541/10000000000 : ℝ)*X 1 1+(4231136087/10000000000 : ℝ)*X 1 2+(4357750073/10000000000 : ℝ)*X 2 0+(4488111541/10000000000 : ℝ)*X 2 1+(4231136087/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1191_s5_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (43735954416928651107979/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (128932123/10000000000000 : ℝ)*(base19) + (15296671/1250000000000 : ℝ)*(base23) + (26502471/100000000000000 : ℝ)*(lower2) + (152431281/100000000000000 : ℝ)*(upper3) + (26002293/20000000000000 : ℝ)*(upper5) + (291186540803169/5000000000000 : ℝ)*(major0) + (291186540803169/5000000000000 : ℝ)*(major1) + (291186540803169/5000000000000 : ℝ)*(major2) + (3888028044334611/50000000000000 : ℝ)*(sp0) + (7776087660756953/100000000000000 : ℝ)*(sp1) + (3888043863172251/50000000000000 : ℝ)*(sp2) + (387135522886807/10000000000000 : ℝ)*(sp3) + (32861408961/100000000000000 : ℝ)*(sp4) + (8609961037/50000000000000 : ℝ)*(sp7) + (30245097256173/781250000000 : ℝ)*(f.failure) + (7776088950078183/100000000000000 : ℝ)*(f.sum) + (80931479111/15000000000000000000000000 : ℝ)*base65 + (348955522522021/75000000000000000000000000000 : ℝ)*base68 + (855819555547021/75000000000000000000000000000 : ℝ)*base70 + (364211674072021/75000000000000000000000000000 : ℝ)*base72 + (126191448941/15000000000000000000000000 : ℝ)*base73 + (620696324197021/75000000000000000000000000000 : ℝ)*base76 + (674990741902979/75000000000000000000000000000 : ℝ)*base77 + (1340962082197021/75000000000000000000000000000 : ℝ)*base80 + (8205565487/7500000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (52551/19531250000000000000 : ℝ)*base90 + (52551/19531250000000000000 : ℝ)*base92 + (52551/19531250000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (775748109463165441880719/140625000000000000000000000000 : ℝ) := by norm_num
    linear_combination (995421843/100000000000000 : ℝ)*(base19) + (1113384921/100000000000000 : ℝ)*(base23) + (12546851/10000000000000 : ℝ)*(upper3) + (5087381/10000000000000 : ℝ)*(lower4) + (49240599/50000000000000 : ℝ)*(upper5) + (365868255438587/6250000000000 : ℝ)*(major0) + (365868255438587/6250000000000 : ℝ)*(major1) + (365868255438587/6250000000000 : ℝ)*(major2) + (26516673581/100000000000000 : ℝ)*(sp1) + (15180946077/50000000000000 : ℝ)*(sp2) + (3908180795534441/50000000000000 : ℝ)*(sp4) + (7816334078973459/100000000000000 : ℝ)*(sp5) + (3908165057895903/50000000000000 : ℝ)*(sp6) + (486427799885607/12500000000000 : ℝ)*(sp7) + (486427799885607/12500000000000 : ℝ)*(f.failure) + (3908180795534441/50000000000000 : ℝ)*(f.sum) + (2006418883361/337500000000000000000000000 : ℝ)*base66 + (6997627201982453/843750000000000000000000000000 : ℝ)*base67 + (5993487669294953/843750000000000000000000000000 : ℝ)*base69 + (4243966454048797/843750000000000000000000000000 : ℝ)*base72 + (1366804406753/675000000000000000000000000 : ℝ)*base73 + (2005676591263703/843750000000000000000000000000 : ℝ)*base75 + (13478872313732453/843750000000000000000000000000 : ℝ)*base77 + (4508647055357453/843750000000000000000000000000 : ℝ)*base79 + (11558522743/168750000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (3393559/312500000000000000000 : ℝ)*base90 + (3393559/312500000000000000000 : ℝ)*base92 + (3393559/312500000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1191_s5 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2847/20000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (2253/20000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1191_s5 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1191_b1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16361/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9287/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1191_s3 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1191_s4 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1191_s5 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8383/2048 : ℝ) ≤ p) (hpb : p ≤ (131/32 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (37607663/25000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (16361/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (9287/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (2277/20000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (14109/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1191_b1 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
