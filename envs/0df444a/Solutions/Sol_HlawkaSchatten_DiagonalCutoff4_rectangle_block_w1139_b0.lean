-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1139_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T15:30:49.766587+00:00
-- url     : https://prove2.me/submissions/c62bb134-d186-4ca7-8e8e-ddc989e0d991

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
theorem support_rectangle_w1139_s0_0 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1892760557/10000000000 : ℝ)*x 0 + (30275119/50000000 : ℝ)*x 1 + (298755801/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1892760557/10000000000 : ℝ)^2083 ≤ (11002618397409/100000000000000 : ℝ)^1571 := by
    have hnat : (1892760557 : ℕ)^2083*100000000000000^1571 ≤ 11002618397409^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1892760557 10000000000 11002618397409 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (30275119/50000000 : ℝ)^2083 ≤ (51416898010839/100000000000000 : ℝ)^1571 := by
    have hnat : (30275119 : ℕ)^2083*100000000000000^1571 ≤ 51416898010839^1571*50000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      30275119 50000000 51416898010839 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (298755801/625000000 : ℝ)^2083 ≤ (234878022403/625000000000 : ℝ)^1571 := by
    have hnat : (298755801 : ℕ)^2083*625000000000^1571 ≤ 234878022403^1571*625000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      298755801 625000000 234878022403 625000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1892760557/10000000000 : ℝ), (30275119/50000000 : ℝ), (298755801/625000000 : ℝ)] ![(11002618397409/100000000000000 : ℝ), (51416898010839/100000000000000 : ℝ), (234878022403/625000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1892760557/10000000000 : ℝ)|^2083 ≤ (11002618397409/100000000000000 : ℝ)^1571
        have hw : |(-1892760557/10000000000 : ℝ)|=(1892760557/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(30275119/50000000 : ℝ)|^2083 ≤ (51416898010839/100000000000000 : ℝ)^1571
        have hw : |(30275119/50000000 : ℝ)|=(30275119/50000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(298755801/625000000 : ℝ)|^2083 ≤ (234878022403/625000000000 : ℝ)^1571
        have hw : |(298755801/625000000 : ℝ)|=(298755801/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s0_1 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5516962651/10000000000 : ℝ)*x 0 + (-20996057/80000000 : ℝ)*x 1 + (4780092799/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5516962651/10000000000 : ℝ)^2083 ≤ (5681045611619/12500000000000 : ℝ)^1571 := by
    have hnat : (5516962651 : ℕ)^2083*12500000000000^1571 ≤ 5681045611619^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5516962651 10000000000 5681045611619 12500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (20996057/80000000 : ℝ)^2083 ≤ (16971151683921/100000000000000 : ℝ)^1571 := by
    have hnat : (20996057 : ℕ)^2083*100000000000000^1571 ≤ 16971151683921^1571*80000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      20996057 80000000 16971151683921 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4780092799/10000000000 : ℝ)^2083 ≤ (3758048340727/10000000000000 : ℝ)^1571 := by
    have hnat : (4780092799 : ℕ)^2083*10000000000000^1571 ≤ 3758048340727^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4780092799 10000000000 3758048340727 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5516962651/10000000000 : ℝ), (-20996057/80000000 : ℝ), (4780092799/10000000000 : ℝ)] ![(5681045611619/12500000000000 : ℝ), (16971151683921/100000000000000 : ℝ), (3758048340727/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5516962651/10000000000 : ℝ)|^2083 ≤ (5681045611619/12500000000000 : ℝ)^1571
        have hw : |(5516962651/10000000000 : ℝ)|=(5516962651/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-20996057/80000000 : ℝ)|^2083 ≤ (16971151683921/100000000000000 : ℝ)^1571
        have hw : |(-20996057/80000000 : ℝ)|=(20996057/80000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4780092799/10000000000 : ℝ)|^2083 ≤ (3758048340727/10000000000000 : ℝ)^1571
        have hw : |(4780092799/10000000000 : ℝ)|=(4780092799/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s0_2 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2758481319/5000000000 : ℝ)*x 0 + (1195023197/2500000000 : ℝ)*x 1 + (-524901431/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2758481319/5000000000 : ℝ)^2083 ≤ (11362091187739/25000000000000 : ℝ)^1571 := by
    have hnat : (2758481319 : ℕ)^2083*25000000000000^1571 ≤ 11362091187739^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2758481319 5000000000 11362091187739 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1195023197/2500000000 : ℝ)^2083 ≤ (7516096658521/20000000000000 : ℝ)^1571 := by
    have hnat : (1195023197 : ℕ)^2083*20000000000000^1571 ≤ 7516096658521^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1195023197 2500000000 7516096658521 20000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (524901431/2000000000 : ℝ)^2083 ≤ (16971151941137/100000000000000 : ℝ)^1571 := by
    have hnat : (524901431 : ℕ)^2083*100000000000000^1571 ≤ 16971151941137^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524901431 2000000000 16971151941137 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2758481319/5000000000 : ℝ), (1195023197/2500000000 : ℝ), (-524901431/2000000000 : ℝ)] ![(11362091187739/25000000000000 : ℝ), (7516096658521/20000000000000 : ℝ), (16971151941137/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2758481319/5000000000 : ℝ)|^2083 ≤ (11362091187739/25000000000000 : ℝ)^1571
        have hw : |(2758481319/5000000000 : ℝ)|=(2758481319/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1195023197/2500000000 : ℝ)|^2083 ≤ (7516096658521/20000000000000 : ℝ)^1571
        have hw : |(1195023197/2500000000 : ℝ)|=(1195023197/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-524901431/2000000000 : ℝ)|^2083 ≤ (16971151941137/100000000000000 : ℝ)^1571
        have hw : |(-524901431/2000000000 : ℝ)|=(524901431/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s0_3 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2100616771/5000000000 : ℝ)*x 0 + (3121217871/10000000000 : ℝ)*x 1 + (1414041949/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2100616771/5000000000 : ℝ)^2083 ≤ (15834438749441/50000000000000 : ℝ)^1571 := by
    have hnat : (2100616771 : ℕ)^2083*50000000000000^1571 ≤ 15834438749441^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2100616771 5000000000 15834438749441 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3121217871/10000000000 : ℝ)^2083 ≤ (10678020138159/50000000000000 : ℝ)^1571 := by
    have hnat : (3121217871 : ℕ)^2083*50000000000000^1571 ≤ 10678020138159^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3121217871 10000000000 10678020138159 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1414041949/2500000000 : ℝ)^2083 ≤ (23487541104179/50000000000000 : ℝ)^1571 := by
    have hnat : (1414041949 : ℕ)^2083*50000000000000^1571 ≤ 23487541104179^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1414041949 2500000000 23487541104179 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2100616771/5000000000 : ℝ), (3121217871/10000000000 : ℝ), (1414041949/2500000000 : ℝ)] ![(15834438749441/50000000000000 : ℝ), (10678020138159/50000000000000 : ℝ), (23487541104179/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2100616771/5000000000 : ℝ)|^2083 ≤ (15834438749441/50000000000000 : ℝ)^1571
        have hw : |(2100616771/5000000000 : ℝ)|=(2100616771/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3121217871/10000000000 : ℝ)|^2083 ≤ (10678020138159/50000000000000 : ℝ)^1571
        have hw : |(3121217871/10000000000 : ℝ)|=(3121217871/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1414041949/2500000000 : ℝ)|^2083 ≤ (23487541104179/50000000000000 : ℝ)^1571
        have hw : |(1414041949/2500000000 : ℝ)|=(1414041949/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s0_4 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-474478749/2500000000 : ℝ)*x 0 + (2406491947/5000000000 : ℝ)*x 1 + (47038879/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (474478749/2500000000 : ℝ)^2083 ≤ (11042363848041/100000000000000 : ℝ)^1571 := by
    have hnat : (474478749 : ℕ)^2083*100000000000000^1571 ≤ 11042363848041^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      474478749 2500000000 11042363848041 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2406491947/5000000000 : ℝ)^2083 ≤ (37923727747659/100000000000000 : ℝ)^1571 := by
    have hnat : (2406491947 : ℕ)^2083*100000000000000^1571 ≤ 37923727747659^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2406491947 5000000000 37923727747659 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (47038879/78125000 : ℝ)^2083 ≤ (5103390839181/10000000000000 : ℝ)^1571 := by
    have hnat : (47038879 : ℕ)^2083*10000000000000^1571 ≤ 5103390839181^1571*78125000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      47038879 78125000 5103390839181 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-474478749/2500000000 : ℝ), (2406491947/5000000000 : ℝ), (47038879/78125000 : ℝ)] ![(11042363848041/100000000000000 : ℝ), (37923727747659/100000000000000 : ℝ), (5103390839181/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-474478749/2500000000 : ℝ)|^2083 ≤ (11042363848041/100000000000000 : ℝ)^1571
        have hw : |(-474478749/2500000000 : ℝ)|=(474478749/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2406491947/5000000000 : ℝ)|^2083 ≤ (37923727747659/100000000000000 : ℝ)^1571
        have hw : |(2406491947/5000000000 : ℝ)|=(2406491947/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(47038879/78125000 : ℝ)|^2083 ≤ (5103390839181/10000000000000 : ℝ)^1571
        have hw : |(47038879/78125000 : ℝ)|=(47038879/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s0_5 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5170550103/10000000000 : ℝ)*x 0 + (-276724699/2000000000 : ℝ)*x 1 + (752622049/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5170550103/10000000000 : ℝ)^2083 ≤ (41703869593647/100000000000000 : ℝ)^1571 := by
    have hnat : (5170550103 : ℕ)^2083*100000000000000^1571 ≤ 41703869593647^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5170550103 10000000000 41703869593647 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (276724699/2000000000 : ℝ)^2083 ≤ (3631111675811/50000000000000 : ℝ)^1571 := by
    have hnat : (276724699 : ℕ)^2083*50000000000000^1571 ≤ 3631111675811^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276724699 2000000000 3631111675811 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (752622049/1250000000 : ℝ)^2083 ≤ (15948095951/31250000000 : ℝ)^1571 := by
    have hnat : (752622049 : ℕ)^2083*31250000000^1571 ≤ 15948095951^1571*1250000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752622049 1250000000 15948095951 31250000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5170550103/10000000000 : ℝ), (-276724699/2000000000 : ℝ), (752622049/1250000000 : ℝ)] ![(41703869593647/100000000000000 : ℝ), (3631111675811/50000000000000 : ℝ), (15948095951/31250000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5170550103/10000000000 : ℝ)|^2083 ≤ (41703869593647/100000000000000 : ℝ)^1571
        have hw : |(5170550103/10000000000 : ℝ)|=(5170550103/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-276724699/2000000000 : ℝ)|^2083 ≤ (3631111675811/50000000000000 : ℝ)^1571
        have hw : |(-276724699/2000000000 : ℝ)|=(276724699/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(752622049/1250000000 : ℝ)|^2083 ≤ (15948095951/31250000000 : ℝ)^1571
        have hw : |(752622049/1250000000 : ℝ)|=(752622049/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s0_6 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (161579691/312500000 : ℝ)*x 0 + (752622051/1250000000 : ℝ)*x 1 + (-276724691/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (161579691/312500000 : ℝ)^2083 ≤ (5212983711237/12500000000000 : ℝ)^1571 := by
    have hnat : (161579691 : ℕ)^2083*12500000000000^1571 ≤ 5212983711237^1571*312500000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      161579691 312500000 5212983711237 12500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (752622051/1250000000 : ℝ)^2083 ≤ (10206781444603/20000000000000 : ℝ)^1571 := by
    have hnat : (752622051 : ℕ)^2083*20000000000000^1571 ≤ 10206781444603^1571*1250000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      752622051 1250000000 10206781444603 20000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (276724691/2000000000 : ℝ)^2083 ≤ (7262223073251/100000000000000 : ℝ)^1571 := by
    have hnat : (276724691 : ℕ)^2083*100000000000000^1571 ≤ 7262223073251^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      276724691 2000000000 7262223073251 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(161579691/312500000 : ℝ), (752622051/1250000000 : ℝ), (-276724691/2000000000 : ℝ)] ![(5212983711237/12500000000000 : ℝ), (10206781444603/20000000000000 : ℝ), (7262223073251/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(161579691/312500000 : ℝ)|^2083 ≤ (5212983711237/12500000000000 : ℝ)^1571
        have hw : |(161579691/312500000 : ℝ)|=(161579691/312500000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(752622051/1250000000 : ℝ)|^2083 ≤ (10206781444603/20000000000000 : ℝ)^1571
        have hw : |(752622051/1250000000 : ℝ)|=(752622051/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-276724691/2000000000 : ℝ)|^2083 ≤ (7262223073251/100000000000000 : ℝ)^1571
        have hw : |(-276724691/2000000000 : ℝ)|=(276724691/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s0_7 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2105741137/5000000000 : ℝ)*x 0 + (1118154017/2000000000 : ℝ)*x 1 + (1594457211/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2105741137/5000000000 : ℝ)^2083 ≤ (3971418875121/12500000000000 : ℝ)^1571 := by
    have hnat : (2105741137 : ℕ)^2083*12500000000000^1571 ≤ 3971418875121^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2105741137 5000000000 3971418875121 12500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1118154017/2000000000 : ℝ)^2083 ≤ (23128148004357/50000000000000 : ℝ)^1571 := by
    have hnat : (1118154017 : ℕ)^2083*50000000000000^1571 ≤ 23128148004357^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1118154017 2000000000 23128148004357 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1594457211/5000000000 : ℝ)^2083 ≤ (21972352977129/100000000000000 : ℝ)^1571 := by
    have hnat : (1594457211 : ℕ)^2083*100000000000000^1571 ≤ 21972352977129^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1594457211 5000000000 21972352977129 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2105741137/5000000000 : ℝ), (1118154017/2000000000 : ℝ), (1594457211/5000000000 : ℝ)] ![(3971418875121/12500000000000 : ℝ), (23128148004357/50000000000000 : ℝ), (21972352977129/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2105741137/5000000000 : ℝ)|^2083 ≤ (3971418875121/12500000000000 : ℝ)^1571
        have hw : |(2105741137/5000000000 : ℝ)|=(2105741137/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1118154017/2000000000 : ℝ)|^2083 ≤ (23128148004357/50000000000000 : ℝ)^1571
        have hw : |(1118154017/2000000000 : ℝ)|=(1118154017/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1594457211/5000000000 : ℝ)|^2083 ≤ (21972352977129/100000000000000 : ℝ)^1571
        have hw : |(1594457211/5000000000 : ℝ)|=(1594457211/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1139_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (401/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (27827/100000 : ℝ)*pair X 0 0 := by
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
  have base24 : ((-1 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 2).1]
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
  have hpowlo : (0 : ℝ) ^ (8331/2048 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^8331 ≤ (0 : ℝ)^2048 := by
      have hnat : (0 : ℕ)^8331*1^2048 ≤ 0^2048*1^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (8331/2048 : ℝ) ≤ (2405643906531436857/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^8331 ≤ (2405643906531436857/100000000000000000000 : ℝ)^2048 := by
      have hnat : (2 : ℕ)^8331*100000000000000000000^2048 ≤ 2405643906531436857^2048*5^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2405643906531436857 100000000000000000000 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2405643906531436857/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (1 : ℝ)^2048 ≤ (1 : ℝ)^8331 := by
      have hnat : (1 : ℕ)^2048*1^8331 ≤ 1^8331*1^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (102405643906531436857/100000000000000000000 : ℝ) ≤ (5029304314396767/5000000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (102405643906531436857/100000000000000000000 : ℝ)^2048 ≤ (5029304314396767/5000000000000000 : ℝ)^8331 := by
      have hnat : (102405643906531436857 : ℕ)^2048*5000000000000000^8331 ≤ 5029304314396767^8331*100000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102405643906531436857 100000000000000000000 5029304314396767 5000000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5029304314396767/5000000000000000 : ℝ)) (X := (102405643906531436857/100000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (52405643906531436857/50000000000000000000 : ℝ) ≤ (2529304314396767/2500000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (52405643906531436857/50000000000000000000 : ℝ)^2048 ≤ (2529304314396767/2500000000000000 : ℝ)^8331 := by
      have hnat : (52405643906531436857 : ℕ)^2048*2500000000000000^8331 ≤ 2529304314396767^8331*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52405643906531436857 50000000000000000000 2529304314396767 2500000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2529304314396767/2500000000000000 : ℝ)) (X := (52405643906531436857/50000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(29304314396767/2000000000000000 : ℝ)*(0 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(29304314396767/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2405643906531436857/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(29304314396767/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(8331/2048 : ℝ) := by
    rw [show (1 : ℝ)+(29304314396767/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5029304314396767/5000000000000000 : ℝ) by norm_num, show 1+(2405643906531436857/100000000000000000000 : ℝ)+(0 : ℝ)=(102405643906531436857/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2405643906531436857/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(29304314396767/2000000000000000 : ℝ)*(2/5 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (1 : ℝ)+2*(29304314396767/2000000000000000 : ℝ)*(2/5 : ℝ)=(2529304314396767/2500000000000000 : ℝ) by norm_num, show 1+2*(2405643906531436857/100000000000000000000 : ℝ)=(52405643906531436857/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(29304314396767/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29304314396767/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(29304314396767/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29304314396767/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(29304314396767/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (29304314396767/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1892760557/10000000000 : ℝ)*X 0 0+(30275119/50000000 : ℝ)*X 0 1+(298755801/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5516962651/10000000000 : ℝ)*X 1 0+(-20996057/80000000 : ℝ)*X 1 1+(4780092799/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2758481319/5000000000 : ℝ)*X 2 0+(1195023197/2500000000 : ℝ)*X 2 1+(-524901431/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((2100616771/5000000000 : ℝ)*X 0 0+(3121217871/10000000000 : ℝ)*X 0 1+(1414041949/2500000000 : ℝ)*X 0 2+(2100616771/5000000000 : ℝ)*X 1 0+(3121217871/10000000000 : ℝ)*X 1 1+(1414041949/2500000000 : ℝ)*X 1 2+(2100616771/5000000000 : ℝ)*X 2 0+(3121217871/10000000000 : ℝ)*X 2 1+(1414041949/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-474478749/2500000000 : ℝ)*X 0 0+(2406491947/5000000000 : ℝ)*X 0 1+(47038879/78125000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5170550103/10000000000 : ℝ)*X 1 0+(-276724699/2000000000 : ℝ)*X 1 1+(752622049/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((161579691/312500000 : ℝ)*X 2 0+(752622051/1250000000 : ℝ)*X 2 1+(-276724691/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2105741137/5000000000 : ℝ)*X 0 0+(1118154017/2000000000 : ℝ)*X 0 1+(1594457211/5000000000 : ℝ)*X 0 2+(2105741137/5000000000 : ℝ)*X 1 0+(1118154017/2000000000 : ℝ)*X 1 1+(1594457211/5000000000 : ℝ)*X 1 2+(2105741137/5000000000 : ℝ)*X 2 0+(1118154017/2000000000 : ℝ)*X 2 1+(1594457211/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (273474770864706655413369/50000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (61524261/100000000000000 : ℝ)*(base1) + (663441821/50000000000000 : ℝ)*(base19) + (77278479/6250000000000 : ℝ)*(base23) + (88579731/100000000000000 : ℝ)*(base24) + (15152099/5000000000000 : ℝ)*(upper3) + (294713115602669/50000000000000 : ℝ)*(major0) + (294713115602669/50000000000000 : ℝ)*(major1) + (294713115602669/50000000000000 : ℝ)*(major2) + (784360590609709/100000000000000 : ℝ)*(sp0) + (784362093982747/100000000000000 : ℝ)*(sp1) + (392181047915497/50000000000000 : ℝ)*(sp2) + (197243237737291/50000000000000 : ℝ)*(sp3) + (1445890471/50000000000000 : ℝ)*(sp4) + (580557231/25000000000000 : ℝ)*(sp7) + (394488859227767/100000000000000 : ℝ)*(f.failure) + (784363420866389/100000000000000 : ℝ)*(f.sum) + (5531033578877/50000000000000000000000000000 : ℝ)*base66 + (280970809171123/100000000000000000000000000000 : ℝ)*base67 + (463256414628877/100000000000000000000000000000 : ℝ)*base70 + (260321898471123/100000000000000000000000000000 : ℝ)*base71 + (61498664178877/50000000000000000000000000000 : ℝ)*base74 + (188448184871123/100000000000000000000000000000 : ℝ)*base75 + (18019910971123/100000000000000000000000000000 : ℝ)*base77 + (685165916771123/100000000000000000000000000000 : ℝ)*base79 + (251164666328877/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base83 + (25576237/5000000000000000000000 : ℝ)*base90 + (25576237/5000000000000000000000 : ℝ)*base92 + (25576237/5000000000000000000000 : ℝ)*base94 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (51987330642894867682407/6250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (49735301/50000000000000 : ℝ)*(base1) + (2052585931/100000000000000 : ℝ)*(base19) + (51334521/2500000000000 : ℝ)*(base23) + (56632217/25000000000000 : ℝ)*(upper3) + (29869227/12500000000000 : ℝ)*(upper5) + (77760294016557/12500000000000 : ℝ)*(major0) + (77760294016557/12500000000000 : ℝ)*(major1) + (77760294016557/12500000000000 : ℝ)*(major2) + (4193584893/100000000000000 : ℝ)*(sp1) + (2091971387/50000000000000 : ℝ)*(sp2) + (827819707650567/100000000000000 : ℝ)*(sp4) + (827813362009141/100000000000000 : ℝ)*(sp5) + (827813370856351/100000000000000 : ℝ)*(sp6) + (416344719348579/100000000000000 : ℝ)*(sp7) + (416344818819181/100000000000000 : ℝ)*(f.failure) + (165563921635993/20000000000000 : ℝ)*(f.sum) + (2001858653781/12500000000000000000000000000 : ℝ)*base66 + (66682712553781/25000000000000000000000000000 : ℝ)*base68 + (89616750778781/25000000000000000000000000000 : ℝ)*base70 + (125119822528781/25000000000000000000000000000 : ℝ)*base72 + (9887605333719/12500000000000000000000000000 : ℝ)*base73 + (8803187346219/25000000000000000000000000000 : ℝ)*base75 + (78212728978781/25000000000000000000000000000 : ℝ)*base78 + (33839456896219/25000000000000000000000000000 : ℝ)*base79 + (9715105516281/12500000000000000000000000000 : ℝ)*base82 + (39464609/5000000000000000000000 : ℝ)*base89 + (39464609/5000000000000000000000 : ℝ)*base91 + (39464609/5000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1139_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (401/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (27827/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1139_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1139_s1_0 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-524409359/2500000000 : ℝ)*x 0 + (1140464349/2000000000 : ℝ)*x 1 + (1000326369/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (524409359/2500000000 : ℝ)^2083 ≤ (315222774341/2500000000000 : ℝ)^1571 := by
    have hnat : (524409359 : ℕ)^2083*2500000000000^1571 ≤ 315222774341^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      524409359 2500000000 315222774341 2500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1140464349/2000000000 : ℝ)^2083 ≤ (47483994867863/100000000000000 : ℝ)^1571 := by
    have hnat : (1140464349 : ℕ)^2083*100000000000000^1571 ≤ 47483994867863^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1140464349 2000000000 47483994867863 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1000326369/2000000000 : ℝ)^2083 ≤ (19953547071687/50000000000000 : ℝ)^1571 := by
    have hnat : (1000326369 : ℕ)^2083*50000000000000^1571 ≤ 19953547071687^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1000326369 2000000000 19953547071687 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-524409359/2500000000 : ℝ), (1140464349/2000000000 : ℝ), (1000326369/2000000000 : ℝ)] ![(315222774341/2500000000000 : ℝ), (47483994867863/100000000000000 : ℝ), (19953547071687/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-524409359/2500000000 : ℝ)|^2083 ≤ (315222774341/2500000000000 : ℝ)^1571
        have hw : |(-524409359/2500000000 : ℝ)|=(524409359/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1140464349/2000000000 : ℝ)|^2083 ≤ (47483994867863/100000000000000 : ℝ)^1571
        have hw : |(1140464349/2000000000 : ℝ)|=(1140464349/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1000326369/2000000000 : ℝ)|^2083 ≤ (19953547071687/50000000000000 : ℝ)^1571
        have hw : |(1000326369/2000000000 : ℝ)|=(1000326369/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s1_1 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2709645053/5000000000 : ℝ)*x 0 + (-618956717/2500000000 : ℝ)*x 1 + (2500815607/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709645053/5000000000 : ℝ)^2083 ≤ (44384603928519/100000000000000 : ℝ)^1571 := by
    have hnat : (2709645053 : ℕ)^2083*100000000000000^1571 ≤ 44384603928519^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709645053 5000000000 44384603928519 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (618956717/2500000000 : ℝ)^2083 ≤ (15708308592367/100000000000000 : ℝ)^1571 := by
    have hnat : (618956717 : ℕ)^2083*100000000000000^1571 ≤ 15708308592367^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      618956717 2500000000 15708308592367 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2500815607/5000000000 : ℝ)^2083 ≤ (498838593349/1250000000000 : ℝ)^1571 := by
    have hnat : (2500815607 : ℕ)^2083*1250000000000^1571 ≤ 498838593349^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2500815607 5000000000 498838593349 1250000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709645053/5000000000 : ℝ), (-618956717/2500000000 : ℝ), (2500815607/5000000000 : ℝ)] ![(44384603928519/100000000000000 : ℝ), (15708308592367/100000000000000 : ℝ), (498838593349/1250000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709645053/5000000000 : ℝ)|^2083 ≤ (44384603928519/100000000000000 : ℝ)^1571
        have hw : |(2709645053/5000000000 : ℝ)|=(2709645053/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-618956717/2500000000 : ℝ)|^2083 ≤ (15708308592367/100000000000000 : ℝ)^1571
        have hw : |(-618956717/2500000000 : ℝ)|=(618956717/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2500815607/5000000000 : ℝ)|^2083 ≤ (498838593349/1250000000000 : ℝ)^1571
        have hw : |(2500815607/5000000000 : ℝ)|=(2500815607/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s1_2 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2709645997/5000000000 : ℝ)*x 0 + (1250407383/2500000000 : ℝ)*x 1 + (-495165309/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2709645997/5000000000 : ℝ)^2083 ≤ (5548078053867/12500000000000 : ℝ)^1571 := by
    have hnat : (2709645997 : ℕ)^2083*12500000000000^1571 ≤ 5548078053867^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2709645997 5000000000 5548078053867 12500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1250407383/2500000000 : ℝ)^2083 ≤ (39907069673763/100000000000000 : ℝ)^1571 := by
    have hnat : (1250407383 : ℕ)^2083*100000000000000^1571 ≤ 39907069673763^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1250407383 2500000000 39907069673763 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (495165309/2000000000 : ℝ)^2083 ≤ (15708305875147/100000000000000 : ℝ)^1571 := by
    have hnat : (495165309 : ℕ)^2083*100000000000000^1571 ≤ 15708305875147^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      495165309 2000000000 15708305875147 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2709645997/5000000000 : ℝ), (1250407383/2500000000 : ℝ), (-495165309/2000000000 : ℝ)] ![(5548078053867/12500000000000 : ℝ), (39907069673763/100000000000000 : ℝ), (15708305875147/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2709645997/5000000000 : ℝ)|^2083 ≤ (5548078053867/12500000000000 : ℝ)^1571
        have hw : |(2709645997/5000000000 : ℝ)|=(2709645997/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1250407383/2500000000 : ℝ)|^2083 ≤ (39907069673763/100000000000000 : ℝ)^1571
        have hw : |(1250407383/2500000000 : ℝ)|=(1250407383/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-495165309/2000000000 : ℝ)|^2083 ≤ (15708305875147/100000000000000 : ℝ)^1571
        have hw : |(-495165309/2000000000 : ℝ)|=(495165309/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s1_3 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (107942247/250000000 : ℝ)*x 0 + (1838228187/5000000000 : ℝ)*x 1 + (1013927613/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (107942247/250000000 : ℝ)^2083 ≤ (32838046592693/100000000000000 : ℝ)^1571 := by
    have hnat : (107942247 : ℕ)^2083*100000000000000^1571 ≤ 32838046592693^1571*250000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      107942247 250000000 32838046592693 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1838228187/5000000000 : ℝ)^2083 ≤ (26533820897111/100000000000000 : ℝ)^1571 := by
    have hnat : (1838228187 : ℕ)^2083*100000000000000^1571 ≤ 26533820897111^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1838228187 5000000000 26533820897111 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1013927613/2000000000 : ℝ)^2083 ≤ (10157033124663/25000000000000 : ℝ)^1571 := by
    have hnat : (1013927613 : ℕ)^2083*25000000000000^1571 ≤ 10157033124663^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1013927613 2000000000 10157033124663 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(107942247/250000000 : ℝ), (1838228187/5000000000 : ℝ), (1013927613/2000000000 : ℝ)] ![(32838046592693/100000000000000 : ℝ), (26533820897111/100000000000000 : ℝ), (10157033124663/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(107942247/250000000 : ℝ)|^2083 ≤ (32838046592693/100000000000000 : ℝ)^1571
        have hw : |(107942247/250000000 : ℝ)|=(107942247/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1838228187/5000000000 : ℝ)|^2083 ≤ (26533820897111/100000000000000 : ℝ)^1571
        have hw : |(1838228187/5000000000 : ℝ)|=(1838228187/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1013927613/2000000000 : ℝ)|^2083 ≤ (10157033124663/25000000000000 : ℝ)^1571
        have hw : |(1013927613/2000000000 : ℝ)|=(1013927613/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s1_4 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-1049224091/5000000000 : ℝ)*x 0 + (5011210169/10000000000 : ℝ)*x 1 + (2846276603/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1049224091/5000000000 : ℝ)^2083 ≤ (12615373054713/100000000000000 : ℝ)^1571 := by
    have hnat : (1049224091 : ℕ)^2083*100000000000000^1571 ≤ 12615373054713^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1049224091 5000000000 12615373054713 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5011210169/10000000000 : ℝ)^2083 ≤ (20004228219781/50000000000000 : ℝ)^1571 := by
    have hnat : (5011210169 : ℕ)^2083*50000000000000^1571 ≤ 20004228219781^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5011210169 10000000000 20004228219781 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2846276603/5000000000 : ℝ)^2083 ≤ (9475234099397/20000000000000 : ℝ)^1571 := by
    have hnat : (2846276603 : ℕ)^2083*20000000000000^1571 ≤ 9475234099397^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2846276603 5000000000 9475234099397 20000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1049224091/5000000000 : ℝ), (5011210169/10000000000 : ℝ), (2846276603/5000000000 : ℝ)] ![(12615373054713/100000000000000 : ℝ), (20004228219781/50000000000000 : ℝ), (9475234099397/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1049224091/5000000000 : ℝ)|^2083 ≤ (12615373054713/100000000000000 : ℝ)^1571
        have hw : |(-1049224091/5000000000 : ℝ)|=(1049224091/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5011210169/10000000000 : ℝ)|^2083 ≤ (20004228219781/50000000000000 : ℝ)^1571
        have hw : |(5011210169/10000000000 : ℝ)|=(5011210169/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2846276603/5000000000 : ℝ)|^2083 ≤ (9475234099397/20000000000000 : ℝ)^1571
        have hw : |(2846276603/5000000000 : ℝ)|=(2846276603/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s1_5 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5239672733/10000000000 : ℝ)*x 0 + (-1784904599/10000000000 : ℝ)*x 1 + (711569111/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5239672733/10000000000 : ℝ)^2083 ≤ (21222346914177/50000000000000 : ℝ)^1571 := by
    have hnat : (5239672733 : ℕ)^2083*50000000000000^1571 ≤ 21222346914177^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5239672733 10000000000 21222346914177 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1784904599/10000000000 : ℝ)^2083 ≤ (5089569584569/50000000000000 : ℝ)^1571 := by
    have hnat : (1784904599 : ℕ)^2083*50000000000000^1571 ≤ 5089569584569^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1784904599 10000000000 5089569584569 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (711569111/1250000000 : ℝ)^2083 ≤ (47376166987907/100000000000000 : ℝ)^1571 := by
    have hnat : (711569111 : ℕ)^2083*100000000000000^1571 ≤ 47376166987907^1571*1250000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      711569111 1250000000 47376166987907 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5239672733/10000000000 : ℝ), (-1784904599/10000000000 : ℝ), (711569111/1250000000 : ℝ)] ![(21222346914177/50000000000000 : ℝ), (5089569584569/50000000000000 : ℝ), (47376166987907/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5239672733/10000000000 : ℝ)|^2083 ≤ (21222346914177/50000000000000 : ℝ)^1571
        have hw : |(5239672733/10000000000 : ℝ)|=(5239672733/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1784904599/10000000000 : ℝ)|^2083 ≤ (5089569584569/50000000000000 : ℝ)^1571
        have hw : |(-1784904599/10000000000 : ℝ)|=(1784904599/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(711569111/1250000000 : ℝ)|^2083 ≤ (47376166987907/100000000000000 : ℝ)^1571
        have hw : |(711569111/1250000000 : ℝ)|=(711569111/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s1_6 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (654959099/1250000000 : ℝ)*x 0 + (5692553079/10000000000 : ℝ)*x 1 + (-446226059/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (654959099/1250000000 : ℝ)^2083 ≤ (8488938892411/20000000000000 : ℝ)^1571 := by
    have hnat : (654959099 : ℕ)^2083*20000000000000^1571 ≤ 8488938892411^1571*1250000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      654959099 1250000000 8488938892411 20000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5692553079/10000000000 : ℝ)^2083 ≤ (47376169095561/100000000000000 : ℝ)^1571 := by
    have hnat : (5692553079 : ℕ)^2083*100000000000000^1571 ≤ 47376169095561^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5692553079 10000000000 47376169095561 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (446226059/2500000000 : ℝ)^2083 ≤ (10179136424307/100000000000000 : ℝ)^1571 := by
    have hnat : (446226059 : ℕ)^2083*100000000000000^1571 ≤ 10179136424307^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      446226059 2500000000 10179136424307 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(654959099/1250000000 : ℝ), (5692553079/10000000000 : ℝ), (-446226059/2500000000 : ℝ)] ![(8488938892411/20000000000000 : ℝ), (47376169095561/100000000000000 : ℝ), (10179136424307/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(654959099/1250000000 : ℝ)|^2083 ≤ (8488938892411/20000000000000 : ℝ)^1571
        have hw : |(654959099/1250000000 : ℝ)|=(654959099/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5692553079/10000000000 : ℝ)|^2083 ≤ (47376169095561/100000000000000 : ℝ)^1571
        have hw : |(5692553079/10000000000 : ℝ)|=(5692553079/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-446226059/2500000000 : ℝ)|^2083 ≤ (10179136424307/100000000000000 : ℝ)^1571
        have hw : |(-446226059/2500000000 : ℝ)|=(446226059/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s1_7 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (4319298041/10000000000 : ℝ)*x 0 + (2525297259/5000000000 : ℝ)*x 1 + (1847938953/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4319298041/10000000000 : ℝ)^2083 ≤ (6570852900161/20000000000000 : ℝ)^1571 := by
    have hnat : (4319298041 : ℕ)^2083*20000000000000^1571 ≤ 6570852900161^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4319298041 10000000000 6570852900161 20000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2525297259/5000000000 : ℝ)^2083 ≤ (20212951457741/50000000000000 : ℝ)^1571 := by
    have hnat : (2525297259 : ℕ)^2083*50000000000000^1571 ≤ 20212951457741^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2525297259 5000000000 20212951457741 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1847938953/5000000000 : ℝ)^2083 ≤ (13359916284659/50000000000000 : ℝ)^1571 := by
    have hnat : (1847938953 : ℕ)^2083*50000000000000^1571 ≤ 13359916284659^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1847938953 5000000000 13359916284659 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4319298041/10000000000 : ℝ), (2525297259/5000000000 : ℝ), (1847938953/5000000000 : ℝ)] ![(6570852900161/20000000000000 : ℝ), (20212951457741/50000000000000 : ℝ), (13359916284659/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4319298041/10000000000 : ℝ)|^2083 ≤ (6570852900161/20000000000000 : ℝ)^1571
        have hw : |(4319298041/10000000000 : ℝ)|=(4319298041/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2525297259/5000000000 : ℝ)|^2083 ≤ (20212951457741/50000000000000 : ℝ)^1571
        have hw : |(2525297259/5000000000 : ℝ)|=(2525297259/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1847938953/5000000000 : ℝ)|^2083 ≤ (13359916284659/50000000000000 : ℝ)^1571
        have hw : |(1847938953/5000000000 : ℝ)|=(1847938953/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1139_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27827/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (5633/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (20451/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (27827/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (27827/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (401/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (27827/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (27827/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (401/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (27827/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (27827/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (401/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base37 : ((1 : ℝ)*X 0 2+(1 : ℝ)*X 1 2+(1 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    linarith only [(f.column 2).2]
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
  have hpowlo : (401/100000 : ℝ) ^ (8331/2048 : ℝ) ≤ (4444677823/25000000000000000000 : ℝ) := by
    have hpowers : (401/100000 : ℝ)^8331 ≤ (4444677823/25000000000000000000 : ℝ)^2048 := by
      have hnat : (401 : ℕ)^8331*25000000000000000000^2048 ≤ 4444677823^2048*100000^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        401 100000 4444677823 25000000000000000000 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (401/100000 : ℝ)) (X := (4444677823/25000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (27827/100000 : ℝ) ^ (8331/2048 : ℝ) ≤ (27487224058821417/5000000000000000000 : ℝ) := by
    have hpowers : (27827/100000 : ℝ)^8331 ≤ (27487224058821417/5000000000000000000 : ℝ)^2048 := by
      have hnat : (27827 : ℕ)^8331*5000000000000000000^2048 ≤ 27487224058821417^2048*100000^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        27827 100000 27487224058821417 5000000000000000000 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (27827/100000 : ℝ)) (X := (27487224058821417/5000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (12500000004444677823/12500000000000000000 : ℝ) ≤ (1250000000109263/1250000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (12500000004444677823/12500000000000000000 : ℝ)^2048 ≤ (1250000000109263/1250000000000000 : ℝ)^8331 := by
      have hnat : (12500000004444677823 : ℕ)^2048*1250000000000000^8331 ≤ 1250000000109263^8331*12500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        12500000004444677823 12500000000000000000 1250000000109263 1250000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250000000109263/1250000000000000 : ℝ)) (X := (12500000004444677823/12500000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (6284359031184696227/6250000000000000000 : ℝ) ≤ (2503371594818733/2500000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (6284359031184696227/6250000000000000000 : ℝ)^2048 ≤ (2503371594818733/2500000000000000 : ℝ)^8331 := by
      have hnat : (6284359031184696227 : ℕ)^2048*2500000000000000^8331 ≤ 2503371594818733^8331*6250000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        6284359031184696227 6250000000000000000 2503371594818733 2500000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2503371594818733/2500000000000000 : ℝ)) (X := (6284359031184696227/6250000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (2527487224058821417/2500000000000000000 : ℝ) ≤ (125337159470947/125000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (2527487224058821417/2500000000000000000 : ℝ)^2048 ≤ (125337159470947/125000000000000 : ℝ)^8331 := by
      have hnat : (2527487224058821417 : ℕ)^2048*125000000000000^8331 ≤ 125337159470947^8331*2500000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2527487224058821417 2500000000000000000 125337159470947 125000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (125337159470947/125000000000000 : ℝ)) (X := (2527487224058821417/2500000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(4444677823/25000000000000000000 : ℝ) ≤ ((34281147993561964031/34282500000000000000 : ℝ)+2*(3371594600207/685650000000000 : ℝ)*(401/100000 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (34281147993561964031/34282500000000000000 : ℝ)+2*(3371594600207/685650000000000 : ℝ)*(401/100000 : ℝ)=(1250000000109263/1250000000000000 : ℝ) by norm_num, show 1+2*(4444677823/25000000000000000000 : ℝ)=(12500000004444677823/12500000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(27487224058821417/5000000000000000000 : ℝ)+(4444677823/25000000000000000000 : ℝ) ≤ ((34281147993561964031/34282500000000000000 : ℝ)+(3371594600207/685650000000000 : ℝ)*((27827/100000 : ℝ)+(401/100000 : ℝ)))^(8331/2048 : ℝ) := by
    rw [show (34281147993561964031/34282500000000000000 : ℝ)+(3371594600207/685650000000000 : ℝ)*((27827/100000 : ℝ)+(401/100000 : ℝ))=(2503371594818733/2500000000000000 : ℝ) by norm_num, show 1+(27487224058821417/5000000000000000000 : ℝ)+(4444677823/25000000000000000000 : ℝ)=(6284359031184696227/6250000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(27487224058821417/5000000000000000000 : ℝ) ≤ ((34281147993561964031/34282500000000000000 : ℝ)+2*(3371594600207/685650000000000 : ℝ)*(27827/100000 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (34281147993561964031/34282500000000000000 : ℝ)+2*(3371594600207/685650000000000 : ℝ)*(27827/100000 : ℝ)=(125337159470947/125000000000000 : ℝ) by norm_num, show 1+2*(27487224058821417/5000000000000000000 : ℝ)=(2527487224058821417/2500000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (34281147993561964031/34282500000000000000 : ℝ)*(X 1 0+X 2 0)+(3371594600207/685650000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (401/100000 : ℝ)) (hi := (27827/100000 : ℝ)) (c := (34281147993561964031/34282500000000000000 : ℝ)) (alpha := (3371594600207/685650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (34281147993561964031/34282500000000000000 : ℝ)*(X 0 1+X 2 1)+(3371594600207/685650000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (401/100000 : ℝ)) (hi := (27827/100000 : ℝ)) (c := (34281147993561964031/34282500000000000000 : ℝ)) (alpha := (3371594600207/685650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (34281147993561964031/34282500000000000000 : ℝ)*(X 0 2+X 1 2)+(3371594600207/685650000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (401/100000 : ℝ)) (hi := (27827/100000 : ℝ)) (c := (34281147993561964031/34282500000000000000 : ℝ)) (alpha := (3371594600207/685650000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-524409359/2500000000 : ℝ)*X 0 0+(1140464349/2000000000 : ℝ)*X 0 1+(1000326369/2000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((2709645053/5000000000 : ℝ)*X 1 0+(-618956717/2500000000 : ℝ)*X 1 1+(2500815607/5000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2709645997/5000000000 : ℝ)*X 2 0+(1250407383/2500000000 : ℝ)*X 2 1+(-495165309/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((107942247/250000000 : ℝ)*X 0 0+(1838228187/5000000000 : ℝ)*X 0 1+(1013927613/2000000000 : ℝ)*X 0 2+(107942247/250000000 : ℝ)*X 1 0+(1838228187/5000000000 : ℝ)*X 1 1+(1013927613/2000000000 : ℝ)*X 1 2+(107942247/250000000 : ℝ)*X 2 0+(1838228187/5000000000 : ℝ)*X 2 1+(1013927613/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1049224091/5000000000 : ℝ)*X 0 0+(5011210169/10000000000 : ℝ)*X 0 1+(2846276603/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5239672733/10000000000 : ℝ)*X 1 0+(-1784904599/10000000000 : ℝ)*X 1 1+(711569111/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((654959099/1250000000 : ℝ)*X 2 0+(5692553079/10000000000 : ℝ)*X 2 1+(-446226059/2500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4319298041/10000000000 : ℝ)*X 0 0+(2525297259/5000000000 : ℝ)*X 0 1+(1847938953/5000000000 : ℝ)*X 0 2+(4319298041/10000000000 : ℝ)*X 1 0+(2525297259/5000000000 : ℝ)*X 1 1+(1847938953/5000000000 : ℝ)*X 1 2+(4319298041/10000000000 : ℝ)*X 2 0+(2525297259/5000000000 : ℝ)*X 2 1+(1847938953/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (49179145018557593324706063/35710937500000000000000000000000 : ℝ) := by norm_num
    linear_combination (35643841/50000000000000 : ℝ)*(base1) + (212624477/50000000000000 : ℝ)*(base19) + (110003447/25000000000000 : ℝ)*(base23) + (24008871/100000000000000 : ℝ)*(base37) + (464443/195312500000 : ℝ)*(lower2) + (134059104289207/12500000000000 : ℝ)*(major0) + (134059104289207/12500000000000 : ℝ)*(major1) + (134059104289207/12500000000000 : ℝ)*(major2) + (1427164055794683/100000000000000 : ℝ)*(sp0) + (1427164816210201/100000000000000 : ℝ)*(sp1) + (713581742318519/50000000000000 : ℝ)*(sp2) + (17944507149169/2500000000000 : ℝ)*(sp3) + (628476077/50000000000000 : ℝ)*(sp4) + (1316808329/100000000000000 : ℝ)*(sp6) + (44861273828957/6250000000000 : ℝ)*(f.failure) + (285433048291831/20000000000000 : ℝ)*(f.sum) + (11366400022793/2142656250000000000000000000 : ℝ)*base66 + (1217245346777897611/142843750000000000000000000000000 : ℝ)*base68 + (1112003950940960111/142843750000000000000000000000000 : ℝ)*base70 + (715963204242116361/142843750000000000000000000000000 : ℝ)*base72 + (31401280858399/17141250000000000000000000000 : ℝ)*base74 + (710759878956741361/142843750000000000000000000000000 : ℝ)*base76 + (1440750539630053861/142843750000000000000000000000000 : ℝ)*base78 + (512463618545585111/142843750000000000000000000000000 : ℝ)*base80 + (29730791880203/34282500000000000000000000000 : ℝ)*base82 + (854673/312500000000000000000 : ℝ)*base89 + (854673/312500000000000000000 : ℝ)*base91 + (854673/312500000000000000000 : ℝ)*base93 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (809860216237170271195362471/142843750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (18714927/25000000000000 : ℝ)*(base1) + (631337803/50000000000000 : ℝ)*(base19) + (651699409/50000000000000 : ℝ)*(base23) + (56520031/50000000000000 : ℝ)*(upper3) + (124941379/100000000000000 : ℝ)*(upper5) + (275731454921247/25000000000000 : ℝ)*(major0) + (275731454921247/25000000000000 : ℝ)*(major1) + (275731454921247/25000000000000 : ℝ)*(major2) + (617949859/12500000000000 : ℝ)*(sp1) + (5649390059/100000000000000 : ℝ)*(sp2) + (183461211281269/12500000000000 : ℝ)*(sp4) + (733841704557983/50000000000000 : ℝ)*(sp5) + (1467682662601567/100000000000000 : ℝ)*(sp6) + (369080880067359/50000000000000 : ℝ)*(sp7) + (369080917497213/50000000000000 : ℝ)*(f.failure) + (366922403847611/25000000000000 : ℝ)*(f.sum) + (3473126586787/11427500000000000000000000000 : ℝ)*base65 + (2500053627933877781/285687500000000000000000000000000 : ℝ)*base68 + (2844294554606877781/285687500000000000000000000000000 : ℝ)*base70 + (1385852761487377781/285687500000000000000000000000000 : ℝ)*base72 + (50905679150763/11427500000000000000000000000 : ℝ)*base74 + (1633268985755877781/285687500000000000000000000000000 : ℝ)*base76 + (963274439062377781/285687500000000000000000000000000 : ℝ)*base78 + (614945085715315281/285687500000000000000000000000000 : ℝ)*base80 + (89639497166211/22855000000000000000000000000 : ℝ)*base82 + (2550543/2500000000000000000000 : ℝ)*base90 + (2550543/2500000000000000000000 : ℝ)*base92 + (2550543/2500000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1139_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (27827/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (401/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (5633/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (20451/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1139_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1139_s2_0 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-430206829/2000000000 : ℝ)*x 0 + (5511382083/10000000000 : ℝ)*x 1 + (644827579/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (430206829/2000000000 : ℝ)^2083 ≤ (101845624593/781250000000 : ℝ)^1571 := by
    have hnat : (430206829 : ℕ)^2083*781250000000^1571 ≤ 101845624593^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      430206829 2000000000 101845624593 781250000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5511382083/10000000000 : ℝ)^2083 ≤ (45387419890241/100000000000000 : ℝ)^1571 := by
    have hnat : (5511382083 : ℕ)^2083*100000000000000^1571 ≤ 45387419890241^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5511382083 10000000000 45387419890241 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (644827579/1250000000 : ℝ)^2083 ≤ (10394085036517/25000000000000 : ℝ)^1571 := by
    have hnat : (644827579 : ℕ)^2083*25000000000000^1571 ≤ 10394085036517^1571*1250000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      644827579 1250000000 10394085036517 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-430206829/2000000000 : ℝ), (5511382083/10000000000 : ℝ), (644827579/1250000000 : ℝ)] ![(101845624593/781250000000 : ℝ), (45387419890241/100000000000000 : ℝ), (10394085036517/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-430206829/2000000000 : ℝ)|^2083 ≤ (101845624593/781250000000 : ℝ)^1571
        have hw : |(-430206829/2000000000 : ℝ)|=(430206829/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5511382083/10000000000 : ℝ)|^2083 ≤ (45387419890241/100000000000000 : ℝ)^1571
        have hw : |(5511382083/10000000000 : ℝ)|=(5511382083/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(644827579/1250000000 : ℝ)|^2083 ≤ (10394085036517/25000000000000 : ℝ)^1571
        have hw : |(644827579/1250000000 : ℝ)|=(644827579/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s2_1 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (134349849/250000000 : ℝ)*x 0 + (-583614129/2500000000 : ℝ)*x 1 + (40301739/78125000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (134349849/250000000 : ℝ)^2083 ≤ (5486673668539/12500000000000 : ℝ)^1571 := by
    have hnat : (134349849 : ℕ)^2083*12500000000000^1571 ≤ 5486673668539^1571*250000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      134349849 250000000 5486673668539 12500000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (583614129/2500000000 : ℝ)^2083 ≤ (7265124774777/50000000000000 : ℝ)^1571 := by
    have hnat : (583614129 : ℕ)^2083*50000000000000^1571 ≤ 7265124774777^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      583614129 2500000000 7265124774777 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (40301739/78125000 : ℝ)^2083 ≤ (2078818054557/5000000000000 : ℝ)^1571 := by
    have hnat : (40301739 : ℕ)^2083*5000000000000^1571 ≤ 2078818054557^1571*78125000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      40301739 78125000 2078818054557 5000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(134349849/250000000 : ℝ), (-583614129/2500000000 : ℝ), (40301739/78125000 : ℝ)] ![(5486673668539/12500000000000 : ℝ), (7265124774777/50000000000000 : ℝ), (2078818054557/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(134349849/250000000 : ℝ)|^2083 ≤ (5486673668539/12500000000000 : ℝ)^1571
        have hw : |(134349849/250000000 : ℝ)|=(134349849/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-583614129/2500000000 : ℝ)|^2083 ≤ (7265124774777/50000000000000 : ℝ)^1571
        have hw : |(-583614129/2500000000 : ℝ)|=(583614129/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(40301739/78125000 : ℝ)|^2083 ≤ (2078818054557/5000000000000 : ℝ)^1571
        have hw : |(40301739/78125000 : ℝ)|=(40301739/78125000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s2_2 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5373993933/10000000000 : ℝ)*x 0 + (2579311247/5000000000 : ℝ)*x 1 + (-2334456677/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5373993933/10000000000 : ℝ)^2083 ≤ (43893389055911/100000000000000 : ℝ)^1571 := by
    have hnat : (5373993933 : ℕ)^2083*100000000000000^1571 ≤ 43893389055911^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5373993933 10000000000 43893389055911 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2579311247/5000000000 : ℝ)^2083 ≤ (20788180021943/50000000000000 : ℝ)^1571 := by
    have hnat : (2579311247 : ℕ)^2083*50000000000000^1571 ≤ 20788180021943^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2579311247 5000000000 20788180021943 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2334456677/10000000000 : ℝ)^2083 ≤ (3632562719563/25000000000000 : ℝ)^1571 := by
    have hnat : (2334456677 : ℕ)^2083*25000000000000^1571 ≤ 3632562719563^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2334456677 10000000000 3632562719563 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5373993933/10000000000 : ℝ), (2579311247/5000000000 : ℝ), (-2334456677/10000000000 : ℝ)] ![(43893389055911/100000000000000 : ℝ), (20788180021943/50000000000000 : ℝ), (3632562719563/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5373993933/10000000000 : ℝ)|^2083 ≤ (43893389055911/100000000000000 : ℝ)^1571
        have hw : |(5373993933/10000000000 : ℝ)|=(5373993933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(2579311247/5000000000 : ℝ)|^2083 ≤ (20788180021943/50000000000000 : ℝ)^1571
        have hw : |(2579311247/5000000000 : ℝ)|=(2579311247/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2334456677/10000000000 : ℝ)|^2083 ≤ (3632562719563/25000000000000 : ℝ)^1571
        have hw : |(-2334456677/10000000000 : ℝ)|=(2334456677/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s2_3 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (870863039/2000000000 : ℝ)*x 0 + (4017624331/10000000000 : ℝ)*x 1 + (4719016551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (870863039/2000000000 : ℝ)^2083 ≤ (664157820459/2000000000000 : ℝ)^1571 := by
    have hnat : (870863039 : ℕ)^2083*2000000000000^1571 ≤ 664157820459^1571*2000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      870863039 2000000000 664157820459 2000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4017624331/10000000000 : ℝ)^2083 ≤ (29846961851059/100000000000000 : ℝ)^1571 := by
    have hnat : (4017624331 : ℕ)^2083*100000000000000^1571 ≤ 29846961851059^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4017624331 10000000000 29846961851059 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4719016551/10000000000 : ℝ)^2083 ≤ (3694514710641/10000000000000 : ℝ)^1571 := by
    have hnat : (4719016551 : ℕ)^2083*10000000000000^1571 ≤ 3694514710641^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4719016551 10000000000 3694514710641 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(870863039/2000000000 : ℝ), (4017624331/10000000000 : ℝ), (4719016551/10000000000 : ℝ)] ![(664157820459/2000000000000 : ℝ), (29846961851059/100000000000000 : ℝ), (3694514710641/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(870863039/2000000000 : ℝ)|^2083 ≤ (664157820459/2000000000000 : ℝ)^1571
        have hw : |(870863039/2000000000 : ℝ)|=(870863039/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4017624331/10000000000 : ℝ)|^2083 ≤ (29846961851059/100000000000000 : ℝ)^1571
        have hw : |(4017624331/10000000000 : ℝ)|=(4017624331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4719016551/10000000000 : ℝ)|^2083 ≤ (3694514710641/10000000000000 : ℝ)^1571
        have hw : |(4719016551/10000000000 : ℝ)|=(4719016551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s2_4 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (-2151137623/10000000000 : ℝ)*x 0 + (5161058439/10000000000 : ℝ)*x 1 + (5508919751/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2151137623/10000000000 : ℝ)^2083 ≤ (13037071461887/100000000000000 : ℝ)^1571 := by
    have hnat : (2151137623 : ℕ)^2083*100000000000000^1571 ≤ 13037071461887^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2151137623 10000000000 13037071461887 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5161058439/10000000000 : ℝ)^2083 ≤ (10400598298067/25000000000000 : ℝ)^1571 := by
    have hnat : (5161058439 : ℕ)^2083*25000000000000^1571 ≤ 10400598298067^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5161058439 10000000000 10400598298067 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5508919751/10000000000 : ℝ)^2083 ≤ (9072107064637/20000000000000 : ℝ)^1571 := by
    have hnat : (5508919751 : ℕ)^2083*20000000000000^1571 ≤ 9072107064637^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508919751 10000000000 9072107064637 20000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2151137623/10000000000 : ℝ), (5161058439/10000000000 : ℝ), (5508919751/10000000000 : ℝ)] ![(13037071461887/100000000000000 : ℝ), (10400598298067/25000000000000 : ℝ), (9072107064637/20000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2151137623/10000000000 : ℝ)|^2083 ≤ (13037071461887/100000000000000 : ℝ)^1571
        have hw : |(-2151137623/10000000000 : ℝ)|=(2151137623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5161058439/10000000000 : ℝ)|^2083 ≤ (10400598298067/25000000000000 : ℝ)^1571
        have hw : |(5161058439/10000000000 : ℝ)|=(5161058439/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5508919751/10000000000 : ℝ)|^2083 ≤ (9072107064637/20000000000000 : ℝ)^1571
        have hw : |(5508919751/10000000000 : ℝ)|=(5508919751/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s2_5 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (5284506933/10000000000 : ℝ)*x 0 + (-992078681/5000000000 : ℝ)*x 1 + (13772301/25000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5284506933/10000000000 : ℝ)^2083 ≤ (1341466074781/3125000000000 : ℝ)^1571 := by
    have hnat : (5284506933 : ℕ)^2083*3125000000000^1571 ≤ 1341466074781^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5284506933 10000000000 1341466074781 3125000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (992078681/5000000000 : ℝ)^2083 ≤ (5856271588403/50000000000000 : ℝ)^1571 := by
    have hnat : (992078681 : ℕ)^2083*50000000000000^1571 ≤ 5856271588403^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      992078681 5000000000 5856271588403 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (13772301/25000000 : ℝ)^2083 ≤ (45360542408669/100000000000000 : ℝ)^1571 := by
    have hnat : (13772301 : ℕ)^2083*100000000000000^1571 ≤ 45360542408669^1571*25000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      13772301 25000000 45360542408669 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5284506933/10000000000 : ℝ), (-992078681/5000000000 : ℝ), (13772301/25000000 : ℝ)] ![(1341466074781/3125000000000 : ℝ), (5856271588403/50000000000000 : ℝ), (45360542408669/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5284506933/10000000000 : ℝ)|^2083 ≤ (1341466074781/3125000000000 : ℝ)^1571
        have hw : |(5284506933/10000000000 : ℝ)|=(5284506933/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-992078681/5000000000 : ℝ)|^2083 ≤ (5856271588403/50000000000000 : ℝ)^1571
        have hw : |(-992078681/5000000000 : ℝ)|=(992078681/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(13772301/25000000 : ℝ)|^2083 ≤ (45360542408669/100000000000000 : ℝ)^1571
        have hw : |(13772301/25000000 : ℝ)|=(13772301/25000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s2_6 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (1321126371/2500000000 : ℝ)*x 0 + (5508920211/10000000000 : ℝ)*x 1 + (-99207981/500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1321126371/2500000000 : ℝ)^2083 ≤ (42926898786451/100000000000000 : ℝ)^1571 := by
    have hnat : (1321126371 : ℕ)^2083*100000000000000^1571 ≤ 42926898786451^1571*2500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1321126371 2500000000 42926898786451 100000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5508920211/10000000000 : ℝ)^2083 ≤ (22680270172627/50000000000000 : ℝ)^1571 := by
    have hnat : (5508920211 : ℕ)^2083*50000000000000^1571 ≤ 22680270172627^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5508920211 10000000000 22680270172627 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (99207981/500000000 : ℝ)^2083 ≤ (2928140212471/25000000000000 : ℝ)^1571 := by
    have hnat : (99207981 : ℕ)^2083*25000000000000^1571 ≤ 2928140212471^1571*500000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      99207981 500000000 2928140212471 25000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1321126371/2500000000 : ℝ), (5508920211/10000000000 : ℝ), (-99207981/500000000 : ℝ)] ![(42926898786451/100000000000000 : ℝ), (22680270172627/50000000000000 : ℝ), (2928140212471/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1321126371/2500000000 : ℝ)|^2083 ≤ (42926898786451/100000000000000 : ℝ)^1571
        have hw : |(1321126371/2500000000 : ℝ)|=(1321126371/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5508920211/10000000000 : ℝ)|^2083 ≤ (22680270172627/50000000000000 : ℝ)^1571
        have hw : |(5508920211/10000000000 : ℝ)|=(5508920211/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-99207981/500000000 : ℝ)|^2083 ≤ (2928140212471/25000000000000 : ℝ)^1571
        have hw : |(-99207981/500000000 : ℝ)|=(99207981/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1139_s2_7 (p : ℝ) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ)) (x : Fin 3 → ℝ) :
    (2177260073/5000000000 : ℝ)*x 0 + (4714171119/10000000000 : ℝ)*x 1 + (4022518421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2177260073/5000000000 : ℝ)^2083 ≤ (16604981745609/50000000000000 : ℝ)^1571 := by
    have hnat : (2177260073 : ℕ)^2083*50000000000000^1571 ≤ 16604981745609^1571*5000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2177260073 5000000000 16604981745609 50000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4714171119/10000000000 : ℝ)^2083 ≤ (2305928589679/6250000000000 : ℝ)^1571 := by
    have hnat : (4714171119 : ℕ)^2083*6250000000000^1571 ≤ 2305928589679^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4714171119 10000000000 2305928589679 6250000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4022518421/10000000000 : ℝ)^2083 ≤ (2989517905449/10000000000000 : ℝ)^1571 := by
    have hnat : (4022518421 : ℕ)^2083*10000000000000^1571 ≤ 2989517905449^1571*10000000000^2083 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4022518421 10000000000 2989517905449 10000000000000 2083 1571 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (2083/512 : ℝ)) 2083 1571 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2177260073/5000000000 : ℝ), (4714171119/10000000000 : ℝ), (4022518421/10000000000 : ℝ)] ![(16604981745609/50000000000000 : ℝ), (2305928589679/6250000000000 : ℝ), (2989517905449/10000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2177260073/5000000000 : ℝ)|^2083 ≤ (16604981745609/50000000000000 : ℝ)^1571
        have hw : |(2177260073/5000000000 : ℝ)|=(2177260073/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4714171119/10000000000 : ℝ)|^2083 ≤ (2305928589679/6250000000000 : ℝ)^1571
        have hw : |(4714171119/10000000000 : ℝ)|=(4714171119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4022518421/10000000000 : ℝ)|^2083 ≤ (2989517905449/10000000000000 : ℝ)^1571
        have hw : |(4022518421/10000000000 : ℝ)|=(4022518421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1139_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20451/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5633/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (9057/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16511/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (20451/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (5633/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (20451/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (5633/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (20451/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (5633/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (20451/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (5633/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (20451/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (5633/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (20451/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (5633/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base15 : ((1 : ℝ)*X 1 0+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 0).2]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
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
  have hpowlo : (5633/100000 : ℝ) ^ (8331/2048 : ℝ) ≤ (828266975272027/100000000000000000000 : ℝ) := by
    have hpowers : (5633/100000 : ℝ)^8331 ≤ (828266975272027/100000000000000000000 : ℝ)^2048 := by
      have hnat : (5633 : ℕ)^8331*100000000000000000000^2048 ≤ 828266975272027^2048*100000^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        5633 100000 828266975272027 100000000000000000000 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (5633/100000 : ℝ)) (X := (828266975272027/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hpowhi : (20451/100000 : ℝ) ^ (8331/2048 : ℝ) ≤ (78531816246375299/50000000000000000000 : ℝ) := by
    have hpowers : (20451/100000 : ℝ)^8331 ≤ (78531816246375299/50000000000000000000 : ℝ)^2048 := by
      have hnat : (20451 : ℕ)^8331*50000000000000000000^2048 ≤ 78531816246375299^2048*100000^8331 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        20451 100000 78531816246375299 50000000000000000000 8331 2048 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (20451/100000 : ℝ)) (X := (78531816246375299/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000828266975272027/50000000000000000000 : ℝ) ≤ (1250005090265783/1250000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (50000828266975272027/50000000000000000000 : ℝ)^2048 ≤ (1250005090265783/1250000000000000 : ℝ)^8331 := by
      have hnat : (50000828266975272027 : ℕ)^2048*1250000000000000^8331 ≤ 1250005090265783^8331*50000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000828266975272027 50000000000000000000 1250005090265783 1250000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1250005090265783/1250000000000000 : ℝ)) (X := (50000828266975272027/50000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner10 : (801263135195744181/800000000000000000 : ℝ) ≤ (10003879129295141/10000000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (801263135195744181/800000000000000000 : ℝ)^2048 ≤ (10003879129295141/10000000000000000 : ℝ)^8331 := by
      have hnat : (801263135195744181 : ℕ)^2048*10000000000000000^8331 ≤ 10003879129295141^8331*800000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        801263135195744181 800000000000000000 10003879129295141 10000000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10003879129295141/10000000000000000 : ℝ)) (X := (801263135195744181/800000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have hcorner11 : (25078531816246375299/25000000000000000000 : ℝ) ≤ (5003858768232009/5000000000000000 : ℝ) ^ (8331/2048 : ℝ) := by
    have hpowers : (25078531816246375299/25000000000000000000 : ℝ)^2048 ≤ (5003858768232009/5000000000000000 : ℝ)^8331 := by
      have hnat : (25078531816246375299 : ℕ)^2048*5000000000000000^8331 ≤ 5003858768232009^8331*25000000000000000000^2048 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25078531816246375299 25000000000000000000 5003858768232009 5000000000000000 2048 8331 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5003858768232009/5000000000000000 : ℝ)) (X := (25078531816246375299/25000000000000000000 : ℝ)) (by norm_num) 8331 2048 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(828266975272027/100000000000000000000 : ℝ) ≤ ((14813735992530241167/14818000000000000000 : ℝ)+2*(3838407168877/1481800000000000 : ℝ)*(5633/100000 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (14813735992530241167/14818000000000000000 : ℝ)+2*(3838407168877/1481800000000000 : ℝ)*(5633/100000 : ℝ)=(1250005090265783/1250000000000000 : ℝ) by norm_num, show 1+2*(828266975272027/100000000000000000000 : ℝ)=(50000828266975272027/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(78531816246375299/50000000000000000000 : ℝ)+(828266975272027/100000000000000000000 : ℝ) ≤ ((14813735992530241167/14818000000000000000 : ℝ)+(3838407168877/1481800000000000 : ℝ)*((20451/100000 : ℝ)+(5633/100000 : ℝ)))^(8331/2048 : ℝ) := by
    rw [show (14813735992530241167/14818000000000000000 : ℝ)+(3838407168877/1481800000000000 : ℝ)*((20451/100000 : ℝ)+(5633/100000 : ℝ))=(10003879129295141/10000000000000000 : ℝ) by norm_num, show 1+(78531816246375299/50000000000000000000 : ℝ)+(828266975272027/100000000000000000000 : ℝ)=(801263135195744181/800000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(78531816246375299/50000000000000000000 : ℝ) ≤ ((14813735992530241167/14818000000000000000 : ℝ)+2*(3838407168877/1481800000000000 : ℝ)*(20451/100000 : ℝ))^(8331/2048 : ℝ) := by
    rw [show (14813735992530241167/14818000000000000000 : ℝ)+2*(3838407168877/1481800000000000 : ℝ)*(20451/100000 : ℝ)=(5003858768232009/5000000000000000 : ℝ) by norm_num, show 1+2*(78531816246375299/50000000000000000000 : ℝ)=(25078531816246375299/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (14813735992530241167/14818000000000000000 : ℝ)*(X 1 0+X 2 0)+(3838407168877/1481800000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (5633/100000 : ℝ)) (hi := (20451/100000 : ℝ)) (c := (14813735992530241167/14818000000000000000 : ℝ)) (alpha := (3838407168877/1481800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (14813735992530241167/14818000000000000000 : ℝ)*(X 0 1+X 2 1)+(3838407168877/1481800000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (5633/100000 : ℝ)) (hi := (20451/100000 : ℝ)) (c := (14813735992530241167/14818000000000000000 : ℝ)) (alpha := (3838407168877/1481800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (14813735992530241167/14818000000000000000 : ℝ)*(X 0 2+X 1 2)+(3838407168877/1481800000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (8331/2048 : ℝ)) (lo := (5633/100000 : ℝ)) (hi := (20451/100000 : ℝ)) (c := (14813735992530241167/14818000000000000000 : ℝ)) (alpha := (3838407168877/1481800000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-430206829/2000000000 : ℝ)*X 0 0+(5511382083/10000000000 : ℝ)*X 0 1+(644827579/1250000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((134349849/250000000 : ℝ)*X 1 0+(-583614129/2500000000 : ℝ)*X 1 1+(40301739/78125000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5373993933/10000000000 : ℝ)*X 2 0+(2579311247/5000000000 : ℝ)*X 2 1+(-2334456677/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((870863039/2000000000 : ℝ)*X 0 0+(4017624331/10000000000 : ℝ)*X 0 1+(4719016551/10000000000 : ℝ)*X 0 2+(870863039/2000000000 : ℝ)*X 1 0+(4017624331/10000000000 : ℝ)*X 1 1+(4719016551/10000000000 : ℝ)*X 1 2+(870863039/2000000000 : ℝ)*X 2 0+(4017624331/10000000000 : ℝ)*X 2 1+(4719016551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2151137623/10000000000 : ℝ)*X 0 0+(5161058439/10000000000 : ℝ)*X 0 1+(5508919751/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5284506933/10000000000 : ℝ)*X 1 0+(-992078681/5000000000 : ℝ)*X 1 1+(13772301/25000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((1321126371/2500000000 : ℝ)*X 2 0+(5508920211/10000000000 : ℝ)*X 2 1+(-99207981/500000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((2177260073/5000000000 : ℝ)*X 0 0+(4714171119/10000000000 : ℝ)*X 0 1+(4022518421/10000000000 : ℝ)*X 0 2+(2177260073/5000000000 : ℝ)*X 1 0+(4714171119/10000000000 : ℝ)*X 1 1+(4022518421/10000000000 : ℝ)*X 1 2+(2177260073/5000000000 : ℝ)*X 2 0+(4714171119/10000000000 : ℝ)*X 2 1+(4022518421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1139_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (155286855409175992257264681/46306250000000000000000000000000 : ℝ) := by norm_num
    linear_combination (32083247/50000000000000 : ℝ)*(base15) + (87434621/100000000000000 : ℝ)*(base29) + (25712641/20000000000000 : ℝ)*(upper2) + (39557731/50000000000000 : ℝ)*(upper3) + (45612891/50000000000000 : ℝ)*(upper4) + (133141900269931/6250000000000 : ℝ)*(major0) + (2130270491753517/100000000000000 : ℝ)*(major1) + (2130270491753517/100000000000000 : ℝ)*(major2) + (70869761920881/2500000000000 : ℝ)*(sp0) + (1417400850996997/50000000000000 : ℝ)*(sp1) + (354350220770061/12500000000000 : ℝ)*(sp2) + (22277144789897/1562500000000 : ℝ)*(sp3) + (2844189967/25000000000000 : ℝ)*(sp4) + (1751576007/100000000000000 : ℝ)*(sp7) + (712869509064707/50000000000000 : ℝ)*(f.failure) + (708700463398777/25000000000000 : ℝ)*(f.sum) + (99347748563211/74090000000000000000000000000 : ℝ)*base66 + (6319998730059124339/1481800000000000000000000000000000 : ℝ)*base67 + (1064554311649124339/1481800000000000000000000000000000 : ℝ)*base69 + (333393530015009949/46306250000000000000000000000000 : ℝ)*base72 + (422192143161659/148180000000000000000000000000 : ℝ)*base74 + (303453853477045661/1481800000000000000000000000000000 : ℝ)*base76 + (32590124147359949/46306250000000000000000000000000 : ℝ)*base78 + (2983342127827045661/1481800000000000000000000000000000 : ℝ)*base80 + (601942692630019/148180000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (20038577/2500000000000000000000 : ℝ)*base90 + (20038577/2500000000000000000000 : ℝ)*base92 + (20038577/2500000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (1068683043205923841337372937/370450000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (228825271/100000000000000 : ℝ)*(base19) + (186063811/50000000000000 : ℝ)*(upper2) + (7026351/6250000000000 : ℝ)*(upper3) + (6158149/20000000000000 : ℝ)*(lower4) + (2160261828851563/100000000000000 : ℝ)*(major0) + (2160261828851563/100000000000000 : ℝ)*(major1) + (2160261828851563/100000000000000 : ℝ)*(major2) + (6939630751/100000000000000 : ℝ)*(sp0) + (5995028983/50000000000000 : ℝ)*(sp1) + (375713497/50000000000000 : ℝ)*(sp3) + (718676280045859/25000000000000 : ℝ)*(sp4) + (57493996818619/2000000000000 : ℝ)*(sp5) + (2874712059814187/100000000000000 : ℝ)*(sp6) + (722905375150569/50000000000000 : ℝ)*(sp7) + (1445811501728133/100000000000000 : ℝ)*(f.failure) + (2874712059814187/100000000000000 : ℝ)*(f.sum) + (128773618233801/74090000000000000000000000000 : ℝ)*base65 + (15282069815731004021/1481800000000000000000000000000000 : ℝ)*base67 + (1986819822534404021/1481800000000000000000000000000000 : ℝ)*base69 + (3450825802195995979/1481800000000000000000000000000000 : ℝ)*base72 + (418215862717551/74090000000000000000000000000 : ℝ)*base73 + (19250013864767204021/1481800000000000000000000000000000 : ℝ)*base75 + (18125160485127604021/1481800000000000000000000000000000 : ℝ)*base77 + (14725234981235004021/1481800000000000000000000000000000 : ℝ)*base79 + (15466082709929/74090000000000000000000000000 : ℝ)*base82 + (98663/5000000000000000000000 : ℝ)*base90 + (98663/5000000000000000000000 : ℝ)*base92 + (98663/5000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
theorem rectangle_w1139_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (20451/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (5633/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9057/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1139_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1139_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9057/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1139_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1139_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1139_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (8331/2048 : ℝ) ≤ p) (hpb : p ≤ (2083/512 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (74707589/50000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (9057/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16511/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1139_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
