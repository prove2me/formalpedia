-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1363_b0
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-28T21:18:41.222296+00:00
-- url     : https://prove2.me/submissions/0d61a9fc-d0e4-4ae5-aad7-c9fda39712aa

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
theorem support_rectangle_w1363_s0_0 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-449199127/2500000000 : ℝ)*x 0 + (5987896207/10000000000 : ℝ)*x 1 + (300993413/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (449199127/2500000000 : ℝ)^4323 ≤ (2636559216427/25000000000000 : ℝ)^3299 := by
    have hnat : (449199127 : ℕ)^4323*25000000000000^3299 ≤ 2636559216427^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      449199127 2500000000 2636559216427 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5987896207/10000000000 : ℝ)^4323 ≤ (51067058554601/100000000000000 : ℝ)^3299 := by
    have hnat : (5987896207 : ℕ)^4323*100000000000000^3299 ≤ 51067058554601^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5987896207 10000000000 51067058554601 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (300993413/625000000 : ℝ)^4323 ≤ (38386704573253/100000000000000 : ℝ)^3299 := by
    have hnat : (300993413 : ℕ)^4323*100000000000000^3299 ≤ 38386704573253^3299*625000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      300993413 625000000 38386704573253 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-449199127/2500000000 : ℝ), (5987896207/10000000000 : ℝ), (300993413/625000000 : ℝ)] ![(2636559216427/25000000000000 : ℝ), (51067058554601/100000000000000 : ℝ), (38386704573253/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-449199127/2500000000 : ℝ)|^4323 ≤ (2636559216427/25000000000000 : ℝ)^3299
        have hw : |(-449199127/2500000000 : ℝ)|=(449199127/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5987896207/10000000000 : ℝ)|^4323 ≤ (51067058554601/100000000000000 : ℝ)^3299
        have hw : |(5987896207/10000000000 : ℝ)|=(5987896207/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(300993413/625000000 : ℝ)|^4323 ≤ (38386704573253/100000000000000 : ℝ)^3299
        have hw : |(300993413/625000000 : ℝ)|=(300993413/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s0_1 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (343716397/625000000 : ℝ)*x 0 + (-1230973297/5000000000 : ℝ)*x 1 + (601986891/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (343716397/625000000 : ℝ)^4323 ≤ (45678979131139/100000000000000 : ℝ)^3299 := by
    have hnat : (343716397 : ℕ)^4323*100000000000000^3299 ≤ 45678979131139^3299*625000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343716397 625000000 45678979131139 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1230973297/5000000000 : ℝ)^4323 ≤ (15934310846701/100000000000000 : ℝ)^3299 := by
    have hnat : (1230973297 : ℕ)^4323*100000000000000^3299 ≤ 15934310846701^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230973297 5000000000 15934310846701 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (601986891/1250000000 : ℝ)^4323 ≤ (4798338750579/12500000000000 : ℝ)^3299 := by
    have hnat : (601986891 : ℕ)^4323*12500000000000^3299 ≤ 4798338750579^3299*1250000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      601986891 1250000000 4798338750579 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(343716397/625000000 : ℝ), (-1230973297/5000000000 : ℝ), (601986891/1250000000 : ℝ)] ![(45678979131139/100000000000000 : ℝ), (15934310846701/100000000000000 : ℝ), (4798338750579/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(343716397/625000000 : ℝ)|^4323 ≤ (45678979131139/100000000000000 : ℝ)^3299
        have hw : |(343716397/625000000 : ℝ)|=(343716397/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1230973297/5000000000 : ℝ)|^4323 ≤ (15934310846701/100000000000000 : ℝ)^3299
        have hw : |(-1230973297/5000000000 : ℝ)|=(1230973297/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(601986891/1250000000 : ℝ)|^4323 ≤ (4798338750579/12500000000000 : ℝ)^3299
        have hw : |(601986891/1250000000 : ℝ)|=(601986891/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s0_2 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5499462227/10000000000 : ℝ)*x 0 + (4815894587/10000000000 : ℝ)*x 1 + (-2461947421/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5499462227/10000000000 : ℝ)^4323 ≤ (22839488885303/50000000000000 : ℝ)^3299 := by
    have hnat : (5499462227 : ℕ)^4323*50000000000000^3299 ≤ 22839488885303^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5499462227 10000000000 22839488885303 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4815894587/10000000000 : ℝ)^4323 ≤ (38386704353909/100000000000000 : ℝ)^3299 := by
    have hnat : (4815894587 : ℕ)^4323*100000000000000^3299 ≤ 38386704353909^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4815894587 10000000000 38386704353909 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2461947421/10000000000 : ℝ)^4323 ≤ (7967158930329/50000000000000 : ℝ)^3299 := by
    have hnat : (2461947421 : ℕ)^4323*50000000000000^3299 ≤ 7967158930329^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2461947421 10000000000 7967158930329 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5499462227/10000000000 : ℝ), (4815894587/10000000000 : ℝ), (-2461947421/10000000000 : ℝ)] ![(22839488885303/50000000000000 : ℝ), (38386704353909/100000000000000 : ℝ), (7967158930329/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5499462227/10000000000 : ℝ)|^4323 ≤ (22839488885303/50000000000000 : ℝ)^3299
        have hw : |(5499462227/10000000000 : ℝ)|=(5499462227/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4815894587/10000000000 : ℝ)|^4323 ≤ (38386704353909/100000000000000 : ℝ)^3299
        have hw : |(4815894587/10000000000 : ℝ)|=(4815894587/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-2461947421/10000000000 : ℝ)|^4323 ≤ (7967158930329/50000000000000 : ℝ)^3299
        have hw : |(-2461947421/10000000000 : ℝ)|=(2461947421/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s0_3 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (835124001/2000000000 : ℝ)*x 0 + (3105589807/10000000000 : ℝ)*x 1 + (2789920591/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (835124001/2000000000 : ℝ)^4323 ≤ (6368305041263/20000000000000 : ℝ)^3299 := by
    have hnat : (835124001 : ℕ)^4323*20000000000000^3299 ≤ 6368305041263^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      835124001 2000000000 6368305041263 20000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3105589807/10000000000 : ℝ)^4323 ≤ (21602653354879/100000000000000 : ℝ)^3299 := by
    have hnat : (3105589807 : ℕ)^4323*100000000000000^3299 ≤ 21602653354879^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3105589807 10000000000 21602653354879 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2789920591/5000000000 : ℝ)^4323 ≤ (23277910711347/50000000000000 : ℝ)^3299 := by
    have hnat : (2789920591 : ℕ)^4323*50000000000000^3299 ≤ 23277910711347^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2789920591 5000000000 23277910711347 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(835124001/2000000000 : ℝ), (3105589807/10000000000 : ℝ), (2789920591/5000000000 : ℝ)] ![(6368305041263/20000000000000 : ℝ), (21602653354879/100000000000000 : ℝ), (23277910711347/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(835124001/2000000000 : ℝ)|^4323 ≤ (6368305041263/20000000000000 : ℝ)^3299
        have hw : |(835124001/2000000000 : ℝ)|=(835124001/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3105589807/10000000000 : ℝ)|^4323 ≤ (21602653354879/100000000000000 : ℝ)^3299
        have hw : |(3105589807/10000000000 : ℝ)|=(3105589807/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2789920591/5000000000 : ℝ)|^4323 ≤ (23277910711347/50000000000000 : ℝ)^3299
        have hw : |(2789920591/5000000000 : ℝ)|=(2789920591/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s0_4 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1801144137/10000000000 : ℝ)*x 0 + (15143813/31250000 : ℝ)*x 1 + (5956694279/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1801144137/10000000000 : ℝ)^4323 ≤ (5289844236567/50000000000000 : ℝ)^3299 := by
    have hnat : (1801144137 : ℕ)^4323*50000000000000^3299 ≤ 5289844236567^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1801144137 10000000000 5289844236567 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (15143813/31250000 : ℝ)^4323 ≤ (19350834900231/50000000000000 : ℝ)^3299 := by
    have hnat : (15143813 : ℕ)^4323*50000000000000^3299 ≤ 19350834900231^3299*31250000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      15143813 31250000 19350834900231 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5956694279/10000000000 : ℝ)^4323 ≤ (25359320853921/50000000000000 : ℝ)^3299 := by
    have hnat : (5956694279 : ℕ)^4323*50000000000000^3299 ≤ 25359320853921^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5956694279 10000000000 25359320853921 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1801144137/10000000000 : ℝ), (15143813/31250000 : ℝ), (5956694279/10000000000 : ℝ)] ![(5289844236567/50000000000000 : ℝ), (19350834900231/50000000000000 : ℝ), (25359320853921/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1801144137/10000000000 : ℝ)|^4323 ≤ (5289844236567/50000000000000 : ℝ)^3299
        have hw : |(-1801144137/10000000000 : ℝ)|=(1801144137/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(15143813/31250000 : ℝ)|^4323 ≤ (19350834900231/50000000000000 : ℝ)^3299
        have hw : |(15143813/31250000 : ℝ)|=(15143813/31250000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5956694279/10000000000 : ℝ)|^4323 ≤ (25359320853921/50000000000000 : ℝ)^3299
        have hw : |(5956694279/10000000000 : ℝ)|=(5956694279/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s0_5 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (323745337/625000000 : ℝ)*x 0 + (-660574731/5000000000 : ℝ)*x 1 + (238267739/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (323745337/625000000 : ℝ)^4323 ≤ (4223284627719/10000000000000 : ℝ)^3299 := by
    have hnat : (323745337 : ℕ)^4323*10000000000000^3299 ≤ 4223284627719^3299*625000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      323745337 625000000 4223284627719 10000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (660574731/5000000000 : ℝ)^4323 ≤ (3524260485683/50000000000000 : ℝ)^3299 := by
    have hnat : (660574731 : ℕ)^4323*50000000000000^3299 ≤ 3524260485683^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      660574731 5000000000 3524260485683 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (238267739/400000000 : ℝ)^4323 ≤ (50718632737247/100000000000000 : ℝ)^3299 := by
    have hnat : (238267739 : ℕ)^4323*100000000000000^3299 ≤ 50718632737247^3299*400000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      238267739 400000000 50718632737247 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(323745337/625000000 : ℝ), (-660574731/5000000000 : ℝ), (238267739/400000000 : ℝ)] ![(4223284627719/10000000000000 : ℝ), (3524260485683/50000000000000 : ℝ), (50718632737247/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(323745337/625000000 : ℝ)|^4323 ≤ (4223284627719/10000000000000 : ℝ)^3299
        have hw : |(323745337/625000000 : ℝ)|=(323745337/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-660574731/5000000000 : ℝ)|^4323 ≤ (3524260485683/50000000000000 : ℝ)^3299
        have hw : |(-660574731/5000000000 : ℝ)|=(660574731/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(238267739/400000000 : ℝ)|^4323 ≤ (50718632737247/100000000000000 : ℝ)^3299
        have hw : |(238267739/400000000 : ℝ)|=(238267739/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s0_6 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (80936329/156250000 : ℝ)*x 0 + (5956694623/10000000000 : ℝ)*x 1 + (-82571759/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (80936329/156250000 : ℝ)^4323 ≤ (211164213437/500000000000 : ℝ)^3299 := by
    have hnat : (80936329 : ℕ)^4323*500000000000^3299 ≤ 211164213437^3299*156250000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      80936329 156250000 211164213437 500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5956694623/10000000000 : ℝ)^4323 ≤ (6339830693251/12500000000000 : ℝ)^3299 := by
    have hnat : (5956694623 : ℕ)^4323*12500000000000^3299 ≤ 6339830693251^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5956694623 10000000000 6339830693251 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (82571759/625000000 : ℝ)^4323 ≤ (281940470281/4000000000000 : ℝ)^3299 := by
    have hnat : (82571759 : ℕ)^4323*4000000000000^3299 ≤ 281940470281^3299*625000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      82571759 625000000 281940470281 4000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(80936329/156250000 : ℝ), (5956694623/10000000000 : ℝ), (-82571759/625000000 : ℝ)] ![(211164213437/500000000000 : ℝ), (6339830693251/12500000000000 : ℝ), (281940470281/4000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(80936329/156250000 : ℝ)|^4323 ≤ (211164213437/500000000000 : ℝ)^3299
        have hw : |(80936329/156250000 : ℝ)|=(80936329/156250000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5956694623/10000000000 : ℝ)|^4323 ≤ (6339830693251/12500000000000 : ℝ)^3299
        have hw : |(5956694623/10000000000 : ℝ)|=(5956694623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-82571759/625000000 : ℝ)|^4323 ≤ (281940470281/4000000000000 : ℝ)^3299
        have hw : |(-82571759/625000000 : ℝ)|=(82571759/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s0_7 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4184793563/10000000000 : ℝ)*x 0 + (1103248809/2000000000 : ℝ)*x 1 + (3171461591/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4184793563/10000000000 : ℝ)^4323 ≤ (1995826473327/6250000000000 : ℝ)^3299 := by
    have hnat : (4184793563 : ℕ)^4323*6250000000000^3299 ≤ 1995826473327^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4184793563 10000000000 1995826473327 6250000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1103248809/2000000000 : ℝ)^4323 ≤ (11465430488911/25000000000000 : ℝ)^3299 := by
    have hnat : (1103248809 : ℕ)^4323*25000000000000^3299 ≤ 11465430488911^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1103248809 2000000000 11465430488911 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (3171461591/10000000000 : ℝ)^4323 ≤ (5551263614227/25000000000000 : ℝ)^3299 := by
    have hnat : (3171461591 : ℕ)^4323*25000000000000^3299 ≤ 5551263614227^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3171461591 10000000000 5551263614227 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4184793563/10000000000 : ℝ), (1103248809/2000000000 : ℝ), (3171461591/10000000000 : ℝ)] ![(1995826473327/6250000000000 : ℝ), (11465430488911/25000000000000 : ℝ), (5551263614227/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4184793563/10000000000 : ℝ)|^4323 ≤ (1995826473327/6250000000000 : ℝ)^3299
        have hw : |(4184793563/10000000000 : ℝ)|=(4184793563/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1103248809/2000000000 : ℝ)|^4323 ≤ (11465430488911/25000000000000 : ℝ)^3299
        have hw : |(1103248809/2000000000 : ℝ)|=(1103248809/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(3171461591/10000000000 : ℝ)|^4323 ≤ (5551263614227/25000000000000 : ℝ)^3299
        have hw : |(3171461591/10000000000 : ℝ)|=(3171461591/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1363_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    (1571/100000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (26721/100000 : ℝ)*pair X 0 0 := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
  have base19 : ((1 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 2).2]
  have base23 : ((1 : ℝ)*X 2 1+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    linarith only [(f.coord 2 1).2]
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
  have hpowlo : (0 : ℝ) ^ (2161/512 : ℝ) ≤ (0 : ℝ) := by
    have hpowers : (0 : ℝ)^2161 ≤ (0 : ℝ)^512 := by
      have hnat : (0 : ℕ)^2161*1^512 ≤ 0^512*1^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        0 1 0 1 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (0 : ℝ)) (X := (0 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hpowhi : (2/5 : ℝ) ^ (2161/512 : ℝ) ≤ (2091285671256144599/100000000000000000000 : ℝ) := by
    have hpowers : (2/5 : ℝ)^2161 ≤ (2091285671256144599/100000000000000000000 : ℝ)^512 := by
      have hnat : (2 : ℕ)^2161*100000000000000000000^512 ≤ 2091285671256144599^512*5^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        2 5 2091285671256144599 100000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (2/5 : ℝ)) (X := (2091285671256144599/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (1 : ℝ) ≤ (1 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (1 : ℝ)^512 ≤ (1 : ℝ)^2161 := by
      have hnat : (1 : ℕ)^512*1^2161 ≤ 1^2161*1^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1 1 1 1 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1 : ℝ)) (X := (1 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (102091285671256144599/100000000000000000000 : ℝ) ≤ (5024578860146539/5000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (102091285671256144599/100000000000000000000 : ℝ)^512 ≤ (5024578860146539/5000000000000000 : ℝ)^2161 := by
      have hnat : (102091285671256144599 : ℕ)^512*5000000000000000^2161 ≤ 5024578860146539^2161*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        102091285671256144599 100000000000000000000 5024578860146539 5000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5024578860146539/5000000000000000 : ℝ)) (X := (102091285671256144599/100000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (52091285671256144599/50000000000000000000 : ℝ) ≤ (2524578860146539/2500000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (52091285671256144599/50000000000000000000 : ℝ)^512 ≤ (2524578860146539/2500000000000000 : ℝ)^2161 := by
      have hnat : (52091285671256144599 : ℕ)^512*2500000000000000^2161 ≤ 2524578860146539^2161*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        52091285671256144599 50000000000000000000 2524578860146539 2500000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (2524578860146539/2500000000000000 : ℝ)) (X := (52091285671256144599/50000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(0 : ℝ) ≤ ((1 : ℝ)+2*(24578860146539/2000000000000000 : ℝ)*(0 : ℝ))^(2161/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(24578860146539/2000000000000000 : ℝ)*(0 : ℝ)=(1 : ℝ) by norm_num, show 1+2*(0 : ℝ)=(1 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(2091285671256144599/100000000000000000000 : ℝ)+(0 : ℝ) ≤ ((1 : ℝ)+(24578860146539/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ)))^(2161/512 : ℝ) := by
    rw [show (1 : ℝ)+(24578860146539/2000000000000000 : ℝ)*((2/5 : ℝ)+(0 : ℝ))=(5024578860146539/5000000000000000 : ℝ) by norm_num, show 1+(2091285671256144599/100000000000000000000 : ℝ)+(0 : ℝ)=(102091285671256144599/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(2091285671256144599/100000000000000000000 : ℝ) ≤ ((1 : ℝ)+2*(24578860146539/2000000000000000 : ℝ)*(2/5 : ℝ))^(2161/512 : ℝ) := by
    rw [show (1 : ℝ)+2*(24578860146539/2000000000000000 : ℝ)*(2/5 : ℝ)=(2524578860146539/2500000000000000 : ℝ) by norm_num, show 1+2*(2091285671256144599/100000000000000000000 : ℝ)=(52091285671256144599/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (1 : ℝ)*(X 1 0+X 2 0)+(24578860146539/2000000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24578860146539/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (1 : ℝ)*(X 0 1+X 2 1)+(24578860146539/2000000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24578860146539/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (1 : ℝ)*(X 0 2+X 1 2)+(24578860146539/2000000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (0 : ℝ)) (hi := (2/5 : ℝ)) (c := (1 : ℝ)) (alpha := (24578860146539/2000000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-449199127/2500000000 : ℝ)*X 0 0+(5987896207/10000000000 : ℝ)*X 0 1+(300993413/625000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s0_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((343716397/625000000 : ℝ)*X 1 0+(-1230973297/5000000000 : ℝ)*X 1 1+(601986891/1250000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s0_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((5499462227/10000000000 : ℝ)*X 2 0+(4815894587/10000000000 : ℝ)*X 2 1+(-2461947421/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s0_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((835124001/2000000000 : ℝ)*X 0 0+(3105589807/10000000000 : ℝ)*X 0 1+(2789920591/5000000000 : ℝ)*X 0 2+(835124001/2000000000 : ℝ)*X 1 0+(3105589807/10000000000 : ℝ)*X 1 1+(2789920591/5000000000 : ℝ)*X 1 2+(835124001/2000000000 : ℝ)*X 2 0+(3105589807/10000000000 : ℝ)*X 2 1+(2789920591/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s0_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-1801144137/10000000000 : ℝ)*X 0 0+(15143813/31250000 : ℝ)*X 0 1+(5956694279/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s0_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((323745337/625000000 : ℝ)*X 1 0+(-660574731/5000000000 : ℝ)*X 1 1+(238267739/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s0_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((80936329/156250000 : ℝ)*X 2 0+(5956694623/10000000000 : ℝ)*X 2 1+(-82571759/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s0_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4184793563/10000000000 : ℝ)*X 0 0+(1103248809/2000000000 : ℝ)*X 0 1+(3171461591/10000000000 : ℝ)*X 0 2+(4184793563/10000000000 : ℝ)*X 1 0+(1103248809/2000000000 : ℝ)*X 1 1+(3171461591/10000000000 : ℝ)*X 1 2+(4184793563/10000000000 : ℝ)*X 2 0+(1103248809/2000000000 : ℝ)*X 2 1+(3171461591/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s0_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (68138558005209753331971/25000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (70187951/50000000000000 : ℝ)*(base1) + (93757/250000000000 : ℝ)*(base16) + (294172297/50000000000000 : ℝ)*(base19) + (60645359/10000000000000 : ℝ)*(base23) + (5890289/6250000000000 : ℝ)*(upper3) + (314352207171637/50000000000000 : ℝ)*(major0) + (314352207171637/50000000000000 : ℝ)*(major1) + (314352207171637/50000000000000 : ℝ)*(major2) + (213310802235247/25000000000000 : ℝ)*(sp0) + (853243928198403/100000000000000 : ℝ)*(sp1) + (426621973796103/50000000000000 : ℝ)*(sp2) + (101040803123117/25000000000000 : ℝ)*(sp3) + (148548071/10000000000000 : ℝ)*(sp4) + (830920961/100000000000000 : ℝ)*(sp7) + (40416418378933/10000000000000 : ℝ)*(f.failure) + (213311138511449/25000000000000 : ℝ)*(f.sum) + (39500915935657/50000000000000000000000000000 : ℝ)*base66 + (604865840814343/100000000000000000000000000000 : ℝ)*base67 + (409802852414343/100000000000000000000000000000 : ℝ)*base69 + (246658520614343/100000000000000000000000000000 : ℝ)*base71 + (127634967564343/50000000000000000000000000000 : ℝ)*base73 + (159419873414343/100000000000000000000000000000 : ℝ)*base75 + (645500630014343/100000000000000000000000000000 : ℝ)*base77 + (797301560214343/100000000000000000000000000000 : ℝ)*base79 + (83025725535657/50000000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (11925029/1000000000000000000000 : ℝ)*base90 + (11925029/1000000000000000000000 : ℝ)*base92 + (11925029/1000000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base95 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (41861678505873659764749/5000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (1101548071/100000000000000 : ℝ)*(base19) + (1493322881/100000000000000 : ℝ)*(base23) + (448205011/100000000000000 : ℝ)*(base39) + (69066649/100000000000000 : ℝ)*(upper3) + (301771439/100000000000000 : ℝ)*(upper5) + (82926911253149/12500000000000 : ℝ)*(major0) + (82926911253149/12500000000000 : ℝ)*(major1) + (331707420910091/50000000000000 : ℝ)*(major2) + (532845663/20000000000000 : ℝ)*(sp1) + (1434285159/50000000000000 : ℝ)*(sp2) + (28135990528547/3125000000000 : ℝ)*(sp4) + (450173965568559/50000000000000 : ℝ)*(sp5) + (225086945806329/25000000000000 : ℝ)*(sp6) + (426478155854009/100000000000000 : ℝ)*(sp7) + (426478155854009/100000000000000 : ℝ)*(f.failure) + (180070429023703/20000000000000 : ℝ)*(f.sum) + (215579737269707/100000000000000000000000000000 : ℝ)*base66 + (46557700674951/100000000000000000000000000000 : ℝ)*base68 + (64059533173689/25000000000000000000000000000 : ℝ)*base70 + (533745116474951/100000000000000000000000000000 : ℝ)*base72 + (3966613269707/100000000000000000000000000000 : ℝ)*base74 + (161580197976311/25000000000000000000000000000 : ℝ)*base75 + (94702733523689/25000000000000000000000000000 : ℝ)*base78 + (132906008273689/25000000000000000000000000000 : ℝ)*base80 + (79801796511189/12500000000000000000000000000 : ℝ)*base82 + (95708183/10000000000000000000000 : ℝ)*base89 + (95708183/10000000000000000000000 : ℝ)*base91 + (4291817/10000000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1363_s0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (1571/100000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (26721/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1363_s0 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1363_s1_0 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-989291799/5000000000 : ℝ)*x 0 + (352052633/625000000 : ℝ)*x 1 + (1263626927/2500000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989291799/5000000000 : ℝ)^4323 ≤ (1495735744329/12500000000000 : ℝ)^3299 := by
    have hnat : (989291799 : ℕ)^4323*12500000000000^3299 ≤ 1495735744329^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989291799 5000000000 1495735744329 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (352052633/625000000 : ℝ)^4323 ≤ (4713615414883/10000000000000 : ℝ)^3299 := by
    have hnat : (352052633 : ℕ)^4323*10000000000000^3299 ≤ 4713615414883^3299*625000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      352052633 625000000 4713615414883 10000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (1263626927/2500000000 : ℝ)^4323 ≤ (10224489970529/25000000000000 : ℝ)^3299 := by
    have hnat : (1263626927 : ℕ)^4323*25000000000000^3299 ≤ 10224489970529^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1263626927 2500000000 10224489970529 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989291799/5000000000 : ℝ), (352052633/625000000 : ℝ), (1263626927/2500000000 : ℝ)] ![(1495735744329/12500000000000 : ℝ), (4713615414883/10000000000000 : ℝ), (10224489970529/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989291799/5000000000 : ℝ)|^4323 ≤ (1495735744329/12500000000000 : ℝ)^3299
        have hw : |(-989291799/5000000000 : ℝ)|=(989291799/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(352052633/625000000 : ℝ)|^4323 ≤ (4713615414883/10000000000000 : ℝ)^3299
        have hw : |(352052633/625000000 : ℝ)|=(352052633/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(1263626927/2500000000 : ℝ)|^4323 ≤ (10224489970529/25000000000000 : ℝ)^3299
        have hw : |(1263626927/2500000000 : ℝ)|=(1263626927/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s1_1 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5403537203/10000000000 : ℝ)*x 0 + (-285831193/1250000000 : ℝ)*x 1 + (202180349/400000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5403537203/10000000000 : ℝ)^4323 ≤ (44637742266247/100000000000000 : ℝ)^3299 := by
    have hnat : (5403537203 : ℕ)^4323*100000000000000^3299 ≤ 44637742266247^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5403537203 10000000000 44637742266247 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (285831193/1250000000 : ℝ)^4323 ≤ (1808035882549/12500000000000 : ℝ)^3299 := by
    have hnat : (285831193 : ℕ)^4323*12500000000000^3299 ≤ 1808035882549^3299*1250000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      285831193 1250000000 1808035882549 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (202180349/400000000 : ℝ)^4323 ≤ (40897970665291/100000000000000 : ℝ)^3299 := by
    have hnat : (202180349 : ℕ)^4323*100000000000000^3299 ≤ 40897970665291^3299*400000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      202180349 400000000 40897970665291 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5403537203/10000000000 : ℝ), (-285831193/1250000000 : ℝ), (202180349/400000000 : ℝ)] ![(44637742266247/100000000000000 : ℝ), (1808035882549/12500000000000 : ℝ), (40897970665291/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5403537203/10000000000 : ℝ)|^4323 ≤ (44637742266247/100000000000000 : ℝ)^3299
        have hw : |(5403537203/10000000000 : ℝ)|=(5403537203/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-285831193/1250000000 : ℝ)|^4323 ≤ (1808035882549/12500000000000 : ℝ)^3299
        have hw : |(-285831193/1250000000 : ℝ)|=(285831193/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(202180349/400000000 : ℝ)|^4323 ≤ (40897970665291/100000000000000 : ℝ)^3299
        have hw : |(202180349/400000000 : ℝ)|=(202180349/400000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s1_2 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (2701768723/5000000000 : ℝ)*x 0 + (1010901579/2000000000 : ℝ)*x 1 + (-142915643/625000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2701768723/5000000000 : ℝ)^4323 ≤ (44637744896717/100000000000000 : ℝ)^3299 := by
    have hnat : (2701768723 : ℕ)^4323*100000000000000^3299 ≤ 44637744896717^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2701768723 5000000000 44637744896717 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1010901579/2000000000 : ℝ)^4323 ≤ (40897961864863/100000000000000 : ℝ)^3299 := by
    have hnat : (1010901579 : ℕ)^4323*100000000000000^3299 ≤ 40897961864863^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1010901579 2000000000 40897961864863 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (142915643/625000000 : ℝ)^4323 ≤ (7232146613691/50000000000000 : ℝ)^3299 := by
    have hnat : (142915643 : ℕ)^4323*50000000000000^3299 ≤ 7232146613691^3299*625000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      142915643 625000000 7232146613691 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(2701768723/5000000000 : ℝ), (1010901579/2000000000 : ℝ), (-142915643/625000000 : ℝ)] ![(44637744896717/100000000000000 : ℝ), (40897961864863/100000000000000 : ℝ), (7232146613691/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(2701768723/5000000000 : ℝ)|^4323 ≤ (44637744896717/100000000000000 : ℝ)^3299
        have hw : |(2701768723/5000000000 : ℝ)|=(2701768723/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1010901579/2000000000 : ℝ)|^4323 ≤ (40897961864863/100000000000000 : ℝ)^3299
        have hw : |(1010901579/2000000000 : ℝ)|=(1010901579/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-142915643/625000000 : ℝ)|^4323 ≤ (7232146613691/50000000000000 : ℝ)^3299
        have hw : |(-142915643/625000000 : ℝ)|=(142915643/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s1_3 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1072138691/2500000000 : ℝ)*x 0 + (3717987419/10000000000 : ℝ)*x 1 + (4938924333/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1072138691/2500000000 : ℝ)^4323 ≤ (824368447707/2500000000000 : ℝ)^3299 := by
    have hnat : (1072138691 : ℕ)^4323*2500000000000^3299 ≤ 824368447707^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1072138691 2500000000 824368447707 2500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (3717987419/10000000000 : ℝ)^4323 ≤ (27348451639521/100000000000000 : ℝ)^3299 := by
    have hnat : (3717987419 : ℕ)^4323*100000000000000^3299 ≤ 27348451639521^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      3717987419 10000000000 27348451639521 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4938924333/10000000000 : ℝ)^4323 ≤ (19838405218263/50000000000000 : ℝ)^3299 := by
    have hnat : (4938924333 : ℕ)^4323*50000000000000^3299 ≤ 19838405218263^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4938924333 10000000000 19838405218263 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1072138691/2500000000 : ℝ), (3717987419/10000000000 : ℝ), (4938924333/10000000000 : ℝ)] ![(824368447707/2500000000000 : ℝ), (27348451639521/100000000000000 : ℝ), (19838405218263/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1072138691/2500000000 : ℝ)|^4323 ≤ (824368447707/2500000000000 : ℝ)^3299
        have hw : |(1072138691/2500000000 : ℝ)|=(1072138691/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(3717987419/10000000000 : ℝ)|^4323 ≤ (27348451639521/100000000000000 : ℝ)^3299
        have hw : |(3717987419/10000000000 : ℝ)|=(3717987419/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4938924333/10000000000 : ℝ)|^4323 ≤ (19838405218263/50000000000000 : ℝ)^3299
        have hw : |(4938924333/10000000000 : ℝ)|=(4938924333/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s1_4 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-989541501/5000000000 : ℝ)*x 0 + (1265412083/2500000000 : ℝ)*x 1 + (2812786859/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (989541501/5000000000 : ℝ)^4323 ≤ (5984921916313/50000000000000 : ℝ)^3299 := by
    have hnat : (989541501 : ℕ)^4323*50000000000000^3299 ≤ 5984921916313^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      989541501 5000000000 5984921916313 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1265412083/2500000000 : ℝ)^4323 ≤ (40973687979493/100000000000000 : ℝ)^3299 := by
    have hnat : (1265412083 : ℕ)^4323*100000000000000^3299 ≤ 40973687979493^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1265412083 2500000000 40973687979493 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2812786859/5000000000 : ℝ)^4323 ≤ (47056468172911/100000000000000 : ℝ)^3299 := by
    have hnat : (2812786859 : ℕ)^4323*100000000000000^3299 ≤ 47056468172911^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2812786859 5000000000 47056468172911 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-989541501/5000000000 : ℝ), (1265412083/2500000000 : ℝ), (2812786859/5000000000 : ℝ)] ![(5984921916313/50000000000000 : ℝ), (40973687979493/100000000000000 : ℝ), (47056468172911/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-989541501/5000000000 : ℝ)|^4323 ≤ (5984921916313/50000000000000 : ℝ)^3299
        have hw : |(-989541501/5000000000 : ℝ)|=(989541501/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1265412083/2500000000 : ℝ)|^4323 ≤ (40973687979493/100000000000000 : ℝ)^3299
        have hw : |(1265412083/2500000000 : ℝ)|=(1265412083/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2812786859/5000000000 : ℝ)|^4323 ≤ (47056468172911/100000000000000 : ℝ)^3299
        have hw : |(2812786859/5000000000 : ℝ)|=(2812786859/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s1_5 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5253207247/10000000000 : ℝ)*x 0 + (-1715584363/10000000000 : ℝ)*x 1 + (5625573791/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5253207247/10000000000 : ℝ)^4323 ≤ (8603499137727/20000000000000 : ℝ)^3299 := by
    have hnat : (5253207247 : ℕ)^4323*20000000000000^3299 ≤ 8603499137727^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5253207247 10000000000 8603499137727 20000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1715584363/10000000000 : ℝ)^4323 ≤ (9926035322519/100000000000000 : ℝ)^3299 := by
    have hnat : (1715584363 : ℕ)^4323*100000000000000^3299 ≤ 9926035322519^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1715584363 10000000000 9926035322519 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5625573791/10000000000 : ℝ)^4323 ≤ (23528234486537/50000000000000 : ℝ)^3299 := by
    have hnat : (5625573791 : ℕ)^4323*50000000000000^3299 ≤ 23528234486537^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5625573791 10000000000 23528234486537 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5253207247/10000000000 : ℝ), (-1715584363/10000000000 : ℝ), (5625573791/10000000000 : ℝ)] ![(8603499137727/20000000000000 : ℝ), (9926035322519/100000000000000 : ℝ), (23528234486537/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5253207247/10000000000 : ℝ)|^4323 ≤ (8603499137727/20000000000000 : ℝ)^3299
        have hw : |(5253207247/10000000000 : ℝ)|=(5253207247/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-1715584363/10000000000 : ℝ)|^4323 ≤ (9926035322519/100000000000000 : ℝ)^3299
        have hw : |(-1715584363/10000000000 : ℝ)|=(1715584363/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5625573791/10000000000 : ℝ)|^4323 ≤ (23528234486537/50000000000000 : ℝ)^3299
        have hw : |(5625573791/10000000000 : ℝ)|=(5625573791/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s1_6 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (262660357/500000000 : ℝ)*x 0 + (5625573881/10000000000 : ℝ)*x 1 + (-343116877/2000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (262660357/500000000 : ℝ)^4323 ≤ (43017494540463/100000000000000 : ℝ)^3299 := by
    have hnat : (262660357 : ℕ)^4323*100000000000000^3299 ≤ 43017494540463^3299*500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      262660357 500000000 43017494540463 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5625573881/10000000000 : ℝ)^4323 ≤ (1882258798383/4000000000000 : ℝ)^3299 := by
    have hnat : (5625573881 : ℕ)^4323*4000000000000^3299 ≤ 1882258798383^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5625573881 10000000000 1882258798383 4000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (343116877/2000000000 : ℝ)^4323 ≤ (2481508872329/25000000000000 : ℝ)^3299 := by
    have hnat : (343116877 : ℕ)^4323*25000000000000^3299 ≤ 2481508872329^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      343116877 2000000000 2481508872329 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(262660357/500000000 : ℝ), (5625573881/10000000000 : ℝ), (-343116877/2000000000 : ℝ)] ![(43017494540463/100000000000000 : ℝ), (1882258798383/4000000000000 : ℝ), (2481508872329/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(262660357/500000000 : ℝ)|^4323 ≤ (43017494540463/100000000000000 : ℝ)^3299
        have hw : |(262660357/500000000 : ℝ)|=(262660357/500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5625573881/10000000000 : ℝ)|^4323 ≤ (1882258798383/4000000000000 : ℝ)^3299
        have hw : |(5625573881/10000000000 : ℝ)|=(5625573881/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-343116877/2000000000 : ℝ)|^4323 ≤ (2481508872329/25000000000000 : ℝ)^3299
        have hw : |(-343116877/2000000000 : ℝ)|=(343116877/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s1_7 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (4289609749/10000000000 : ℝ)*x 0 + (1230962783/2500000000 : ℝ)*x 1 + (466666133/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (4289609749/10000000000 : ℝ)^4323 ≤ (32985367979553/100000000000000 : ℝ)^3299 := by
    have hnat : (4289609749 : ℕ)^4323*100000000000000^3299 ≤ 32985367979553^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4289609749 10000000000 32985367979553 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1230962783/2500000000 : ℝ)^4323 ≤ (19759104541007/50000000000000 : ℝ)^3299 := by
    have hnat : (1230962783 : ℕ)^4323*50000000000000^3299 ≤ 19759104541007^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1230962783 2500000000 19759104541007 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (466666133/1250000000 : ℝ)^4323 ≤ (3437052865629/12500000000000 : ℝ)^3299 := by
    have hnat : (466666133 : ℕ)^4323*12500000000000^3299 ≤ 3437052865629^3299*1250000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      466666133 1250000000 3437052865629 12500000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(4289609749/10000000000 : ℝ), (1230962783/2500000000 : ℝ), (466666133/1250000000 : ℝ)] ![(32985367979553/100000000000000 : ℝ), (19759104541007/50000000000000 : ℝ), (3437052865629/12500000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(4289609749/10000000000 : ℝ)|^4323 ≤ (32985367979553/100000000000000 : ℝ)^3299
        have hw : |(4289609749/10000000000 : ℝ)|=(4289609749/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1230962783/2500000000 : ℝ)|^4323 ≤ (19759104541007/50000000000000 : ℝ)^3299
        have hw : |(1230962783/2500000000 : ℝ)|=(1230962783/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(466666133/1250000000 : ℝ)|^4323 ≤ (3437052865629/12500000000000 : ℝ)^3299
        have hw : |(466666133/1250000000 : ℝ)|=(466666133/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1363_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1571/100000 : ℝ)*pair X i i ≤ pair X i h) :
    (3541/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (9653/50000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (26721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (1571/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (26721/100000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (1571/100000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (26721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (1571/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (26721/100000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (1571/100000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (26721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (1571/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (26721/100000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (1571/100000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have base16 : ((-1 : ℝ)*X 1 1+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    linarith only [(f.coord 1 1).1]
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
  have hpowlo : (1571/100000 : ℝ) ^ (2161/512 : ℝ) ≤ (2435539555077/100000000000000000000 : ℝ) := by
    have hpowers : (1571/100000 : ℝ)^2161 ≤ (2435539555077/100000000000000000000 : ℝ)^512 := by
      have hnat : (1571 : ℕ)^2161*100000000000000000000^512 ≤ 2435539555077^512*100000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        1571 100000 2435539555077 100000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (1571/100000 : ℝ)) (X := (2435539555077/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hpowhi : (26721/100000 : ℝ) ^ (2161/512 : ℝ) ≤ (190495812687575967/50000000000000000000 : ℝ) := by
    have hpowers : (26721/100000 : ℝ)^2161 ≤ (190495812687575967/50000000000000000000 : ℝ)^512 := by
      have hnat : (26721 : ℕ)^2161*50000000000000000000^512 ≤ 190495812687575967^512*100000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        26721 100000 190495812687575967 50000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (26721/100000 : ℝ)) (X := (190495812687575967/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (50000002435539555077/50000000000000000000 : ℝ) ≤ (312500003606537/312500000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (50000002435539555077/50000000000000000000 : ℝ)^512 ≤ (312500003606537/312500000000000 : ℝ)^2161 := by
      have hnat : (50000002435539555077 : ℕ)^512*312500000000000^2161 ≤ 312500003606537^2161*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50000002435539555077 50000000000000000000 312500003606537 312500000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (312500003606537/312500000000000 : ℝ)) (X := (50000002435539555077/50000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100380994060914707011/100000000000000000000 : ℝ) ≤ (10009013698944581/10000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (100380994060914707011/100000000000000000000 : ℝ)^512 ≤ (10009013698944581/10000000000000000 : ℝ)^2161 := by
      have hnat : (100380994060914707011 : ℕ)^512*10000000000000000^2161 ≤ 10009013698944581^2161*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100380994060914707011 100000000000000000000 10009013698944581 10000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (10009013698944581/10000000000000000 : ℝ)) (X := (100380994060914707011/100000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (25190495812687575967/25000000000000000000 : ℝ) ≤ (5009013641239989/5000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (25190495812687575967/25000000000000000000 : ℝ)^512 ≤ (5009013641239989/5000000000000000 : ℝ)^2161 := by
      have hnat : (25190495812687575967 : ℕ)^512*5000000000000000^2161 ≤ 5009013641239989^2161*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25190495812687575967 25000000000000000000 5009013641239989 5000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5009013641239989/5000000000000000 : ℝ)) (X := (25190495812687575967/25000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(2435539555077/100000000000000000000 : ℝ) ≤ ((125735841111536380113/125750000000000000000 : ℝ)+2*(9013583535397/2515000000000000 : ℝ)*(1571/100000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (125735841111536380113/125750000000000000000 : ℝ)+2*(9013583535397/2515000000000000 : ℝ)*(1571/100000 : ℝ)=(312500003606537/312500000000000 : ℝ) by norm_num, show 1+2*(2435539555077/100000000000000000000 : ℝ)=(50000002435539555077/50000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(190495812687575967/50000000000000000000 : ℝ)+(2435539555077/100000000000000000000 : ℝ) ≤ ((125735841111536380113/125750000000000000000 : ℝ)+(9013583535397/2515000000000000 : ℝ)*((26721/100000 : ℝ)+(1571/100000 : ℝ)))^(2161/512 : ℝ) := by
    rw [show (125735841111536380113/125750000000000000000 : ℝ)+(9013583535397/2515000000000000 : ℝ)*((26721/100000 : ℝ)+(1571/100000 : ℝ))=(10009013698944581/10000000000000000 : ℝ) by norm_num, show 1+(190495812687575967/50000000000000000000 : ℝ)+(2435539555077/100000000000000000000 : ℝ)=(100380994060914707011/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(190495812687575967/50000000000000000000 : ℝ) ≤ ((125735841111536380113/125750000000000000000 : ℝ)+2*(9013583535397/2515000000000000 : ℝ)*(26721/100000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (125735841111536380113/125750000000000000000 : ℝ)+2*(9013583535397/2515000000000000 : ℝ)*(26721/100000 : ℝ)=(5009013641239989/5000000000000000 : ℝ) by norm_num, show 1+2*(190495812687575967/50000000000000000000 : ℝ)=(25190495812687575967/25000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (125735841111536380113/125750000000000000000 : ℝ)*(X 1 0+X 2 0)+(9013583535397/2515000000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (1571/100000 : ℝ)) (hi := (26721/100000 : ℝ)) (c := (125735841111536380113/125750000000000000000 : ℝ)) (alpha := (9013583535397/2515000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (125735841111536380113/125750000000000000000 : ℝ)*(X 0 1+X 2 1)+(9013583535397/2515000000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (1571/100000 : ℝ)) (hi := (26721/100000 : ℝ)) (c := (125735841111536380113/125750000000000000000 : ℝ)) (alpha := (9013583535397/2515000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (125735841111536380113/125750000000000000000 : ℝ)*(X 0 2+X 1 2)+(9013583535397/2515000000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (1571/100000 : ℝ)) (hi := (26721/100000 : ℝ)) (c := (125735841111536380113/125750000000000000000 : ℝ)) (alpha := (9013583535397/2515000000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-989291799/5000000000 : ℝ)*X 0 0+(352052633/625000000 : ℝ)*X 0 1+(1263626927/2500000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s1_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5403537203/10000000000 : ℝ)*X 1 0+(-285831193/1250000000 : ℝ)*X 1 1+(202180349/400000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s1_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((2701768723/5000000000 : ℝ)*X 2 0+(1010901579/2000000000 : ℝ)*X 2 1+(-142915643/625000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s1_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1072138691/2500000000 : ℝ)*X 0 0+(3717987419/10000000000 : ℝ)*X 0 1+(4938924333/10000000000 : ℝ)*X 0 2+(1072138691/2500000000 : ℝ)*X 1 0+(3717987419/10000000000 : ℝ)*X 1 1+(4938924333/10000000000 : ℝ)*X 1 2+(1072138691/2500000000 : ℝ)*X 2 0+(3717987419/10000000000 : ℝ)*X 2 1+(4938924333/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s1_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-989541501/5000000000 : ℝ)*X 0 0+(1265412083/2500000000 : ℝ)*X 0 1+(2812786859/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s1_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5253207247/10000000000 : ℝ)*X 1 0+(-1715584363/10000000000 : ℝ)*X 1 1+(5625573791/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s1_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((262660357/500000000 : ℝ)*X 2 0+(5625573881/10000000000 : ℝ)*X 2 1+(-343116877/2000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s1_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((4289609749/10000000000 : ℝ)*X 0 0+(1230962783/2500000000 : ℝ)*X 0 1+(466666133/1250000000 : ℝ)*X 0 2+(4289609749/10000000000 : ℝ)*X 1 0+(1230962783/2500000000 : ℝ)*X 1 1+(466666133/1250000000 : ℝ)*X 1 2+(4289609749/10000000000 : ℝ)*X 2 0+(1230962783/2500000000 : ℝ)*X 2 1+(466666133/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s1_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (336538114321192149557587863/39296875000000000000000000000000 : ℝ) := by norm_num
    linear_combination (31659/2000000000000 : ℝ)*(base1) + (10018373/100000000000000 : ℝ)*(base16) + (681137433/50000000000000 : ℝ)*(base19) + (1450052921/100000000000000 : ℝ)*(base23) + (53464323/20000000000000 : ℝ)*(upper3) + (3981527741677/312500000000 : ℝ)*(major0) + (3981527741677/312500000000 : ℝ)*(major1) + (3981527741677/312500000000 : ℝ)*(major2) + (1729116199759201/100000000000000 : ℝ)*(sp0) + (1729124918910193/100000000000000 : ℝ)*(sp1) + (1729124841150511/100000000000000 : ℝ)*(sp2) + (819046415615053/100000000000000 : ℝ)*(sp3) + (10093027181/100000000000000 : ℝ)*(sp4) + (2380402723/50000000000000 : ℝ)*(sp7) + (16381023560069/2000000000000 : ℝ)*(f.failure) + (216140786400429/12500000000000 : ℝ)*(f.sum) + (21156524102829/6287500000000000000000000000 : ℝ)*base65 + (61050965865219719/9824218750000000000000000000000 : ℝ)*base67 + (21266784465219719/9824218750000000000000000000000 : ℝ)*base69 + (39333854953955063/19648437500000000000000000000000 : ℝ)*base71 + (11861577835583/12575000000000000000000000000 : ℝ)*base73 + (84627915301386749/39296875000000000000000000000000 : ℝ)*base76 + (7181792901582001/39296875000000000000000000000000 : ℝ)*base77 + (152050627517519501/39296875000000000000000000000000 : ℝ)*base79 + (26007334440233/12575000000000000000000000000 : ℝ)*base81 + (868597/200000000000000000000 : ℝ)*base90 + (868597/200000000000000000000 : ℝ)*base92 + (868597/200000000000000000000 : ℝ)*base94 + (1/100000000000000 : ℝ)*base96 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (689162880888779192104521/125750000000000000000000000000 : ℝ) := by norm_num
    linear_combination (28763149/50000000000000 : ℝ)*(base1) + (1115959903/100000000000000 : ℝ)*(base19) + (1079218479/100000000000000 : ℝ)*(base23) + (4080983/3125000000000 : ℝ)*(upper3) + (23980437/20000000000000 : ℝ)*(upper5) + (1306625929254619/100000000000000 : ℝ)*(major0) + (1306625929254619/100000000000000 : ℝ)*(major1) + (1306625929254619/100000000000000 : ℝ)*(major2) + (5921568649/100000000000000 : ℝ)*(sp1) + (1474952283/25000000000000 : ℝ)*(sp2) + (886642015628121/50000000000000 : ℝ)*(sp4) + (110829808512587/6250000000000 : ℝ)*(sp5) + (443319248675583/25000000000000 : ℝ)*(sp6) + (839967644572307/100000000000000 : ℝ)*(sp7) + (167993540419721/20000000000000 : ℝ)*(f.failure) + (221660496716243/12500000000000 : ℝ)*(f.sum) + (12536688029493/125750000000000000000000000000 : ℝ)*base65 + (17765255446117858053/12575000000000000000000000000000000 : ℝ)*base68 + (161984013786317858053/12575000000000000000000000000000000 : ℝ)*base70 + (6701071405432141947/12575000000000000000000000000000000 : ℝ)*base71 + (18924824119743/125750000000000000000000000000 : ℝ)*base73 + (117609754186892858053/12575000000000000000000000000000000 : ℝ)*base76 + (37434738834357141947/12575000000000000000000000000000000 : ℝ)*base77 + (10249338507282141947/12575000000000000000000000000000000 : ℝ)*base79 + (797732475360257/125750000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base88 + (8224327/2000000000000000000000 : ℝ)*base89 + (8224327/2000000000000000000000 : ℝ)*base91 + (8224327/2000000000000000000000 : ℝ)*base93 + hcertificate_margin
theorem rectangle_w1363_s1 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (26721/100000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (1571/100000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (3541/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (9653/50000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1363_s1 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
set_option exponentiation.threshold 40000
set_option linter.unusedSimpArgs false
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalRealBundle HlawkaSchatten.DiagonalCutoff6
theorem support_rectangle_w1363_s2_0 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-1008472739/5000000000 : ℝ)*x 0 + (5474139119/10000000000 : ℝ)*x 1 + (2594304161/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1008472739/5000000000 : ℝ)^4323 ≤ (12270810482639/100000000000000 : ℝ)^3299 := by
    have hnat : (1008472739 : ℕ)^4323*100000000000000^3299 ≤ 12270810482639^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1008472739 5000000000 12270810482639 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5474139119/10000000000 : ℝ)^4323 ≤ (45403551553191/100000000000000 : ℝ)^3299 := by
    have hnat : (5474139119 : ℕ)^4323*100000000000000^3299 ≤ 45403551553191^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5474139119 10000000000 45403551553191 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (2594304161/5000000000 : ℝ)^4323 ≤ (2116281897373/5000000000000 : ℝ)^3299 := by
    have hnat : (2594304161 : ℕ)^4323*5000000000000^3299 ≤ 2116281897373^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2594304161 5000000000 2116281897373 5000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-1008472739/5000000000 : ℝ), (5474139119/10000000000 : ℝ), (2594304161/5000000000 : ℝ)] ![(12270810482639/100000000000000 : ℝ), (45403551553191/100000000000000 : ℝ), (2116281897373/5000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-1008472739/5000000000 : ℝ)|^4323 ≤ (12270810482639/100000000000000 : ℝ)^3299
        have hw : |(-1008472739/5000000000 : ℝ)|=(1008472739/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5474139119/10000000000 : ℝ)|^4323 ≤ (45403551553191/100000000000000 : ℝ)^3299
        have hw : |(5474139119/10000000000 : ℝ)|=(5474139119/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(2594304161/5000000000 : ℝ)|^4323 ≤ (2116281897373/5000000000000 : ℝ)^3299
        have hw : |(2594304161/5000000000 : ℝ)|=(2594304161/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s2_1 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5364493383/10000000000 : ℝ)*x 0 + (-2164315543/10000000000 : ℝ)*x 1 + (5188608639/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5364493383/10000000000 : ℝ)^4323 ≤ (44215568549957/100000000000000 : ℝ)^3299 := by
    have hnat : (5364493383 : ℕ)^4323*100000000000000^3299 ≤ 44215568549957^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5364493383 10000000000 44215568549957 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (2164315543/10000000000 : ℝ)^4323 ≤ (2691758020133/20000000000000 : ℝ)^3299 := by
    have hnat : (2164315543 : ℕ)^4323*20000000000000^3299 ≤ 2691758020133^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2164315543 10000000000 2691758020133 20000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5188608639/10000000000 : ℝ)^4323 ≤ (21162820668009/50000000000000 : ℝ)^3299 := by
    have hnat : (5188608639 : ℕ)^4323*50000000000000^3299 ≤ 21162820668009^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5188608639 10000000000 21162820668009 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5364493383/10000000000 : ℝ), (-2164315543/10000000000 : ℝ), (5188608639/10000000000 : ℝ)] ![(44215568549957/100000000000000 : ℝ), (2691758020133/20000000000000 : ℝ), (21162820668009/50000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5364493383/10000000000 : ℝ)|^4323 ≤ (44215568549957/100000000000000 : ℝ)^3299
        have hw : |(5364493383/10000000000 : ℝ)|=(5364493383/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-2164315543/10000000000 : ℝ)|^4323 ≤ (2691758020133/20000000000000 : ℝ)^3299
        have hw : |(-2164315543/10000000000 : ℝ)|=(2164315543/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5188608639/10000000000 : ℝ)|^4323 ≤ (21162820668009/50000000000000 : ℝ)^3299
        have hw : |(5188608639/10000000000 : ℝ)|=(5188608639/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s2_2 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (335280839/625000000 : ℝ)*x 0 + (1037721717/2000000000 : ℝ)*x 1 + (-54107889/250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (335280839/625000000 : ℝ)^4323 ≤ (44215568992783/100000000000000 : ℝ)^3299 := by
    have hnat : (335280839 : ℕ)^4323*100000000000000^3299 ≤ 44215568992783^3299*625000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      335280839 625000000 44215568992783 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1037721717/2000000000 : ℝ)^4323 ≤ (42325640758787/100000000000000 : ℝ)^3299 := by
    have hnat : (1037721717 : ℕ)^4323*100000000000000^3299 ≤ 42325640758787^3299*2000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1037721717 2000000000 42325640758787 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (54107889/250000000 : ℝ)^4323 ≤ (13458790239193/100000000000000 : ℝ)^3299 := by
    have hnat : (54107889 : ℕ)^4323*100000000000000^3299 ≤ 13458790239193^3299*250000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      54107889 250000000 13458790239193 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(335280839/625000000 : ℝ), (1037721717/2000000000 : ℝ), (-54107889/250000000 : ℝ)] ![(44215568992783/100000000000000 : ℝ), (42325640758787/100000000000000 : ℝ), (13458790239193/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(335280839/625000000 : ℝ)|^4323 ≤ (44215568992783/100000000000000 : ℝ)^3299
        have hw : |(335280839/625000000 : ℝ)|=(335280839/625000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1037721717/2000000000 : ℝ)|^4323 ≤ (42325640758787/100000000000000 : ℝ)^3299
        have hw : |(1037721717/2000000000 : ℝ)|=(1037721717/2000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-54107889/250000000 : ℝ)|^4323 ≤ (13458790239193/100000000000000 : ℝ)^3299
        have hw : |(-54107889/250000000 : ℝ)|=(54107889/250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s2_3 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078860777/2500000000 : ℝ)*x 0 + (4023768331/10000000000 : ℝ)*x 1 + (578320161/1250000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078860777/2500000000 : ℝ)^4323 ≤ (33245918841589/100000000000000 : ℝ)^3299 := by
    have hnat : (1078860777 : ℕ)^4323*100000000000000^3299 ≤ 33245918841589^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078860777 2500000000 33245918841589 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (4023768331/10000000000 : ℝ)^4323 ≤ (30332778380223/100000000000000 : ℝ)^3299 := by
    have hnat : (4023768331 : ℕ)^4323*100000000000000^3299 ≤ 30332778380223^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4023768331 10000000000 30332778380223 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (578320161/1250000000 : ℝ)^4323 ≤ (364213027639/1000000000000 : ℝ)^3299 := by
    have hnat : (578320161 : ℕ)^4323*1000000000000^3299 ≤ 364213027639^3299*1250000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      578320161 1250000000 364213027639 1000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078860777/2500000000 : ℝ), (4023768331/10000000000 : ℝ), (578320161/1250000000 : ℝ)] ![(33245918841589/100000000000000 : ℝ), (30332778380223/100000000000000 : ℝ), (364213027639/1000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078860777/2500000000 : ℝ)|^4323 ≤ (33245918841589/100000000000000 : ℝ)^3299
        have hw : |(1078860777/2500000000 : ℝ)|=(1078860777/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(4023768331/10000000000 : ℝ)|^4323 ≤ (30332778380223/100000000000000 : ℝ)^3299
        have hw : |(4023768331/10000000000 : ℝ)|=(4023768331/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(578320161/1250000000 : ℝ)|^4323 ≤ (364213027639/1000000000000 : ℝ)^3299
        have hw : |(578320161/1250000000 : ℝ)|=(578320161/1250000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s2_4 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (-2017005623/10000000000 : ℝ)*x 0 + (5190358657/10000000000 : ℝ)*x 1 + (5472373353/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (2017005623/10000000000 : ℝ)^4323 ≤ (12271289977049/100000000000000 : ℝ)^3299 := by
    have hnat : (2017005623 : ℕ)^4323*100000000000000^3299 ≤ 12271289977049^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      2017005623 10000000000 12271289977049 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (5190358657/10000000000 : ℝ)^4323 ≤ (4234434905337/10000000000000 : ℝ)^3299 := by
    have hnat : (5190358657 : ℕ)^4323*10000000000000^3299 ≤ 4234434905337^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5190358657 10000000000 4234434905337 10000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5472373353/10000000000 : ℝ)^4323 ≤ (45384360963423/100000000000000 : ℝ)^3299 := by
    have hnat : (5472373353 : ℕ)^4323*100000000000000^3299 ≤ 45384360963423^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472373353 10000000000 45384360963423 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(-2017005623/10000000000 : ℝ), (5190358657/10000000000 : ℝ), (5472373353/10000000000 : ℝ)] ![(12271289977049/100000000000000 : ℝ), (4234434905337/10000000000000 : ℝ), (45384360963423/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(-2017005623/10000000000 : ℝ)|^4323 ≤ (12271289977049/100000000000000 : ℝ)^3299
        have hw : |(-2017005623/10000000000 : ℝ)|=(2017005623/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(5190358657/10000000000 : ℝ)|^4323 ≤ (4234434905337/10000000000000 : ℝ)^3299
        have hw : |(5190358657/10000000000 : ℝ)|=(5190358657/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5472373353/10000000000 : ℝ)|^4323 ≤ (45384360963423/100000000000000 : ℝ)^3299
        have hw : |(5472373353/10000000000 : ℝ)|=(5472373353/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s2_5 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290732687/10000000000 : ℝ)*x 0 + (-37611011/200000000 : ℝ)*x 1 + (5472373301/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290732687/10000000000 : ℝ)^4323 ≤ (21710305698923/50000000000000 : ℝ)^3299 := by
    have hnat : (5290732687 : ℕ)^4323*50000000000000^3299 ≤ 21710305698923^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290732687 10000000000 21710305698923 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (37611011/200000000 : ℝ)^4323 ≤ (5597514094307/50000000000000 : ℝ)^3299 := by
    have hnat : (37611011 : ℕ)^4323*50000000000000^3299 ≤ 5597514094307^3299*200000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      37611011 200000000 5597514094307 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (5472373301/10000000000 : ℝ)^4323 ≤ (11346090099577/25000000000000 : ℝ)^3299 := by
    have hnat : (5472373301 : ℕ)^4323*25000000000000^3299 ≤ 11346090099577^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5472373301 10000000000 11346090099577 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290732687/10000000000 : ℝ), (-37611011/200000000 : ℝ), (5472373301/10000000000 : ℝ)] ![(21710305698923/50000000000000 : ℝ), (5597514094307/50000000000000 : ℝ), (11346090099577/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290732687/10000000000 : ℝ)|^4323 ≤ (21710305698923/50000000000000 : ℝ)^3299
        have hw : |(5290732687/10000000000 : ℝ)|=(5290732687/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(-37611011/200000000 : ℝ)|^4323 ≤ (5597514094307/50000000000000 : ℝ)^3299
        have hw : |(-37611011/200000000 : ℝ)|=(37611011/200000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(5472373301/10000000000 : ℝ)|^4323 ≤ (11346090099577/25000000000000 : ℝ)^3299
        have hw : |(5472373301/10000000000 : ℝ)|=(5472373301/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s2_6 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (5290732649/10000000000 : ℝ)*x 0 + (1368093339/2500000000 : ℝ)*x 1 + (-940275263/5000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (5290732649/10000000000 : ℝ)^4323 ≤ (21710305494591/50000000000000 : ℝ)^3299 := by
    have hnat : (5290732649 : ℕ)^4323*50000000000000^3299 ≤ 21710305494591^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      5290732649 10000000000 21710305494591 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1368093339/2500000000 : ℝ)^4323 ≤ (22692180498013/50000000000000 : ℝ)^3299 := by
    have hnat : (1368093339 : ℕ)^4323*50000000000000^3299 ≤ 22692180498013^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1368093339 2500000000 22692180498013 50000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (940275263/5000000000 : ℝ)^4323 ≤ (11195028001393/100000000000000 : ℝ)^3299 := by
    have hnat : (940275263 : ℕ)^4323*100000000000000^3299 ≤ 11195028001393^3299*5000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      940275263 5000000000 11195028001393 100000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(5290732649/10000000000 : ℝ), (1368093339/2500000000 : ℝ), (-940275263/5000000000 : ℝ)] ![(21710305494591/50000000000000 : ℝ), (22692180498013/50000000000000 : ℝ), (11195028001393/100000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(5290732649/10000000000 : ℝ)|^4323 ≤ (21710305494591/50000000000000 : ℝ)^3299
        have hw : |(5290732649/10000000000 : ℝ)|=(5290732649/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1368093339/2500000000 : ℝ)|^4323 ≤ (22692180498013/50000000000000 : ℝ)^3299
        have hw : |(1368093339/2500000000 : ℝ)|=(1368093339/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(-940275263/5000000000 : ℝ)|^4323 ≤ (11195028001393/100000000000000 : ℝ)^3299
        have hw : |(-940275263/5000000000 : ℝ)|=(940275263/5000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem support_rectangle_w1363_s2_7 (p : ℝ) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ)) (x : Fin 3 → ℝ) :
    (1078892587/2500000000 : ℝ)*x 0 + (1155716657/2500000000 : ℝ)*x 1 + (4027495551/10000000000 : ℝ)*x 2 ≤ lpNorm p x := by
  have power0 : (1078892587/2500000000 : ℝ)^4323 ≤ (1038975105109/3125000000000 : ℝ)^3299 := by
    have hnat : (1078892587 : ℕ)^4323*3125000000000^3299 ≤ 1038975105109^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1078892587 2500000000 1038975105109 3125000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power1 : (1155716657/2500000000 : ℝ)^4323 ≤ (1455327774551/4000000000000 : ℝ)^3299 := by
    have hnat : (1155716657 : ℕ)^4323*4000000000000^3299 ≤ 1455327774551^3299*2500000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      1155716657 2500000000 1455327774551 4000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have power2 : (4027495551/10000000000 : ℝ)^4323 ≤ (7592400565939/25000000000000 : ℝ)^3299 := by
    have hnat : (4027495551 : ℕ)^4323*25000000000000^3299 ≤ 7592400565939^3299*10000000000^4323 := by decide +kernel
    have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
      4027495551 10000000000 7592400565939 25000000000000 4323 3299 (by decide) (by decide) hnat
    simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
  have h := HlawkaSchatten.DiagonalCutoff12.norm_support_interval_cert
    (p := p) (b := (4323/1024 : ℝ)) 4323 3299 (by norm_num)
    (by linarith only [hpa]) (by norm_num) hpb (by norm_num) ![(1078892587/2500000000 : ℝ), (1155716657/2500000000 : ℝ), (4027495551/10000000000 : ℝ)] ![(1038975105109/3125000000000 : ℝ), (1455327774551/4000000000000 : ℝ), (7592400565939/25000000000000 : ℝ)] x
    (by intro i; fin_cases i <;> norm_num)
    (by intro i; fin_cases i <;> norm_num)
    (by
      intro i
      fin_cases i
      · change |(1078892587/2500000000 : ℝ)|^4323 ≤ (1038975105109/3125000000000 : ℝ)^3299
        have hw : |(1078892587/2500000000 : ℝ)|=(1078892587/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power0
      · change |(1155716657/2500000000 : ℝ)|^4323 ≤ (1455327774551/4000000000000 : ℝ)^3299
        have hw : |(1155716657/2500000000 : ℝ)|=(1155716657/2500000000 : ℝ) := by norm_num
        rw [hw]
        exact power1
      · change |(4027495551/10000000000 : ℝ)|^4323 ≤ (7592400565939/25000000000000 : ℝ)^3299
        have hw : |(4027495551/10000000000 : ℝ)|=(4027495551/10000000000 : ℝ) := by norm_num
        rw [hw]
        exact power2
      )
    (by norm_num [Fin.sum_univ_succ])
  simpa [Fin.sum_univ_succ,add_assoc] using h
theorem base_rectangle_w1363_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9653/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3541/50000 : ℝ)*pair X i i ≤ pair X i h) :
    (4993/50000 : ℝ)*pair X 0 0 ≤ pair X 0 1 ∧ pair X 0 1 ≤ (16023/100000 : ℝ)*pair X 0 0 := by
  let N : Fin 3 → ℝ := fun j => lpNorm p (X j)
  let P : Fin 3 → ℝ := fun i => lpNorm p (pair X i)
  let T : ℝ := lpNorm p (total X)
  have f : LinearData _ _ _ X N P T := frame_linear_data (by linarith only [hpa] : (1 : ℝ) ≤ p) X hX
  have bounds := linear_data_bounds f hA
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have sign0 : 0 ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hsign 0 1 (by decide)
  have upper0 : (X 1 1+X 2 1) ≤ (9653/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign0] using hh
  have lower0 : (3541/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 1+X 2 1) := by
    simpa [pair0,pair1,pair2] using hlower 0 1 (by decide)
  have sign1 : 0 ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 0 2 (by decide)
  have upper1 : (X 1 2+X 2 2) ≤ (9653/50000 : ℝ)*(X 1 0+X 2 0) := by
    have hh := hratio 0 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign1] using hh
  have lower1 : (3541/50000 : ℝ)*(X 1 0+X 2 0) ≤ (X 1 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 0 2 (by decide)
  have sign2 : 0 ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hsign 1 0 (by decide)
  have upper2 : (X 0 0+X 2 0) ≤ (9653/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign2] using hh
  have lower2 : (3541/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 0+X 2 0) := by
    simpa [pair0,pair1,pair2] using hlower 1 0 (by decide)
  have sign3 : 0 ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hsign 1 2 (by decide)
  have upper3 : (X 0 2+X 2 2) ≤ (9653/50000 : ℝ)*(X 0 1+X 2 1) := by
    have hh := hratio 1 2 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign3] using hh
  have lower3 : (3541/50000 : ℝ)*(X 0 1+X 2 1) ≤ (X 0 2+X 2 2) := by
    simpa [pair0,pair1,pair2] using hlower 1 2 (by decide)
  have sign4 : 0 ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hsign 2 0 (by decide)
  have upper4 : (X 0 0+X 1 0) ≤ (9653/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 0 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign4] using hh
  have lower4 : (3541/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 0+X 1 0) := by
    simpa [pair0,pair1,pair2] using hlower 2 0 (by decide)
  have sign5 : 0 ≤ (X 0 1+X 1 1) := by
    simpa [pair0,pair1,pair2] using hsign 2 1 (by decide)
  have upper5 : (X 0 1+X 1 1) ≤ (9653/50000 : ℝ)*(X 0 2+X 1 2) := by
    have hh := hratio 2 1 (by decide)
    simpa [pair0,pair1,pair2,abs_of_nonneg sign5] using hh
  have lower5 : (3541/50000 : ℝ)*(X 0 2+X 1 2) ≤ (X 0 1+X 1 1) := by
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
  have hpowlo : (3541/50000 : ℝ) ^ (2161/512 : ℝ) ≤ (701163843252953/50000000000000000000 : ℝ) := by
    have hpowers : (3541/50000 : ℝ)^2161 ≤ (701163843252953/50000000000000000000 : ℝ)^512 := by
      have hnat : (3541 : ℕ)^2161*50000000000000000000^512 ≤ 701163843252953^512*50000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        3541 50000 701163843252953 50000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (3541/50000 : ℝ)) (X := (701163843252953/50000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hpowhi : (9653/50000 : ℝ) ^ (2161/512 : ℝ) ≤ (96631621292171083/100000000000000000000 : ℝ) := by
    have hpowers : (9653/50000 : ℝ)^2161 ≤ (96631621292171083/100000000000000000000 : ℝ)^512 := by
      have hnat : (9653 : ℕ)^2161*100000000000000000000^512 ≤ 96631621292171083^512*50000^2161 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        9653 50000 96631621292171083 100000000000000000000 2161 512 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := rpow_le_of_pow_le (x := (9653/50000 : ℝ)) (X := (96631621292171083/100000000000000000000 : ℝ)) (by norm_num) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner00 : (25000701163843252953/25000000000000000000 : ℝ) ≤ (1000006644924503/1000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (25000701163843252953/25000000000000000000 : ℝ)^512 ≤ (1000006644924503/1000000000000000 : ℝ)^2161 := by
      have hnat : (25000701163843252953 : ℕ)^512*1000000000000000^2161 ≤ 1000006644924503^2161*25000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        25000701163843252953 25000000000000000000 1000006644924503 1000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (1000006644924503/1000000000000000 : ℝ)) (X := (25000701163843252953/25000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner10 : (100098033948978676989/100000000000000000000 : ℝ) ≤ (5001160912045309/5000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (100098033948978676989/100000000000000000000 : ℝ)^512 ≤ (5001160912045309/5000000000000000 : ℝ)^2161 := by
      have hnat : (100098033948978676989 : ℕ)^512*5000000000000000^2161 ≤ 5001160912045309^2161*100000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        100098033948978676989 100000000000000000000 5001160912045309 5000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5001160912045309/5000000000000000 : ℝ)) (X := (100098033948978676989/100000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have hcorner11 : (50096631621292171083/50000000000000000000 : ℝ) ≤ (5002288599468103/5000000000000000 : ℝ) ^ (2161/512 : ℝ) := by
    have hpowers : (50096631621292171083/50000000000000000000 : ℝ)^512 ≤ (5002288599468103/5000000000000000 : ℝ)^2161 := by
      have hnat : (50096631621292171083 : ℕ)^512*5000000000000000^2161 ≤ 5002288599468103^2161*50000000000000000000^512 := by decide +kernel
      have hreal := HlawkaSchatten.DiagonalCutoff4.rational_powers_le
        50096631621292171083 50000000000000000000 5002288599468103 5000000000000000 512 2161 (by decide) (by decide) hnat
      simpa only [Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, div_one] using hreal
    have h := le_rpow_of_pow_le (x := (5002288599468103/5000000000000000 : ℝ)) (X := (50096631621292171083/50000000000000000000 : ℝ)) (by norm_num) 2161 512 (by norm_num) hpowers
    exact h
  have budget00 : 1+2*(701163843252953/50000000000000000000 : ℝ) ≤ ((7638054196641146143/7640000000000000000 : ℝ)+2*(563843711397/305600000000000 : ℝ)*(3541/50000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (7638054196641146143/7640000000000000000 : ℝ)+2*(563843711397/305600000000000 : ℝ)*(3541/50000 : ℝ)=(1000006644924503/1000000000000000 : ℝ) by norm_num, show 1+2*(701163843252953/50000000000000000000 : ℝ)=(25000701163843252953/25000000000000000000 : ℝ) by norm_num]
    exact hcorner00
  have budget10 : 1+(96631621292171083/100000000000000000000 : ℝ)+(701163843252953/50000000000000000000 : ℝ) ≤ ((7638054196641146143/7640000000000000000 : ℝ)+(563843711397/305600000000000 : ℝ)*((9653/50000 : ℝ)+(3541/50000 : ℝ)))^(2161/512 : ℝ) := by
    rw [show (7638054196641146143/7640000000000000000 : ℝ)+(563843711397/305600000000000 : ℝ)*((9653/50000 : ℝ)+(3541/50000 : ℝ))=(5001160912045309/5000000000000000 : ℝ) by norm_num, show 1+(96631621292171083/100000000000000000000 : ℝ)+(701163843252953/50000000000000000000 : ℝ)=(100098033948978676989/100000000000000000000 : ℝ) by norm_num]
    exact hcorner10
  have budget11 : 1+2*(96631621292171083/100000000000000000000 : ℝ) ≤ ((7638054196641146143/7640000000000000000 : ℝ)+2*(563843711397/305600000000000 : ℝ)*(9653/50000 : ℝ))^(2161/512 : ℝ) := by
    rw [show (7638054196641146143/7640000000000000000 : ℝ)+2*(563843711397/305600000000000 : ℝ)*(9653/50000 : ℝ)=(5002288599468103/5000000000000000 : ℝ) by norm_num, show 1+2*(96631621292171083/100000000000000000000 : ℝ)=(50096631621292171083/50000000000000000000 : ℝ) by norm_num]
    exact hcorner11
  have corners := rectangle_budgets hpowlo hpowhi budget00 budget10 budget11
  have major0 : P 0 ≤ (7638054196641146143/7640000000000000000 : ℝ)*(X 1 0+X 2 0)+(563843711397/305600000000000 : ℝ)*((X 1 1+X 2 1)+(X 1 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (3541/50000 : ℝ)) (hi := (9653/50000 : ℝ)) (c := (7638054196641146143/7640000000000000000 : ℝ)) (alpha := (563843711397/305600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 0 1 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 0) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major1 : P 1 ≤ (7638054196641146143/7640000000000000000 : ℝ)*(X 0 1+X 2 1)+(563843711397/305600000000000 : ℝ)*((X 0 0+X 2 0)+(X 0 2+X 2 2)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (3541/50000 : ℝ)) (hi := (9653/50000 : ℝ)) (c := (7638054196641146143/7640000000000000000 : ℝ)) (alpha := (563843711397/305600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 1 0 2 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 1) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have major2 : P 2 ≤ (7638054196641146143/7640000000000000000 : ℝ)*(X 0 2+X 1 2)+(563843711397/305600000000000 : ℝ)*((X 0 0+X 1 0)+(X 0 1+X 1 1)) := by
    have hh := rectangle_pair_majorant (p := p) (a := (2161/512 : ℝ)) (lo := (3541/50000 : ℝ)) (hi := (9653/50000 : ℝ)) (c := (7638054196641146143/7640000000000000000 : ℝ)) (alpha := (563843711397/305600000000000 : ℝ))
      (by linarith only [hpa]) (by norm_num) hpa (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      corners.1 corners.2.1 corners.2.2
      X hmain hlower hratio 2 0 1 (by decide) (by decide) (by decide)
    change lpNorm p (pair X 2) ≤ _
    simpa only [pair0,pair1,pair2,Pi.add_apply] using hh
  have sp0 : ((-1008472739/5000000000 : ℝ)*X 0 0+(5474139119/10000000000 : ℝ)*X 0 1+(2594304161/5000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s2_0 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp1 : ((5364493383/10000000000 : ℝ)*X 1 0+(-2164315543/10000000000 : ℝ)*X 1 1+(5188608639/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s2_1 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp2 : ((335280839/625000000 : ℝ)*X 2 0+(1037721717/2000000000 : ℝ)*X 2 1+(-54107889/250000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s2_2 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp3 : ((1078860777/2500000000 : ℝ)*X 0 0+(4023768331/10000000000 : ℝ)*X 0 1+(578320161/1250000000 : ℝ)*X 0 2+(1078860777/2500000000 : ℝ)*X 1 0+(4023768331/10000000000 : ℝ)*X 1 1+(578320161/1250000000 : ℝ)*X 1 2+(1078860777/2500000000 : ℝ)*X 2 0+(4023768331/10000000000 : ℝ)*X 2 1+(578320161/1250000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s2_3 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp4 : ((-2017005623/10000000000 : ℝ)*X 0 0+(5190358657/10000000000 : ℝ)*X 0 1+(5472373353/10000000000 : ℝ)*X 0 2+(-1 : ℝ)*N 0) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s2_4 p hpa hpb (X 0)
    change _ ≤ N 0 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp5 : ((5290732687/10000000000 : ℝ)*X 1 0+(-37611011/200000000 : ℝ)*X 1 1+(5472373301/10000000000 : ℝ)*X 1 2+(-1 : ℝ)*N 1) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s2_5 p hpa hpb (X 1)
    change _ ≤ N 1 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp6 : ((5290732649/10000000000 : ℝ)*X 2 0+(1368093339/2500000000 : ℝ)*X 2 1+(-940275263/5000000000 : ℝ)*X 2 2+(-1 : ℝ)*N 2) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s2_6 p hpa hpb (X 2)
    change _ ≤ N 2 at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  have sp7 : ((1078892587/2500000000 : ℝ)*X 0 0+(1155716657/2500000000 : ℝ)*X 0 1+(4027495551/10000000000 : ℝ)*X 0 2+(1078892587/2500000000 : ℝ)*X 1 0+(1155716657/2500000000 : ℝ)*X 1 1+(4027495551/10000000000 : ℝ)*X 1 2+(1078892587/2500000000 : ℝ)*X 2 0+(1155716657/2500000000 : ℝ)*X 2 1+(4027495551/10000000000 : ℝ)*X 2 2+(-1 : ℝ)*T) ≤ (0 : ℝ) := by
    have hh := support_rectangle_w1363_s2_7 p hpa hpb (total X)
    change _ ≤ T at hh
    try simp only [pair0,pair1,pair2,total_eq,Pi.add_apply] at hh
    linarith only [hh]
  simp only [pair0,Pi.add_apply]
  constructor
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (241608487410917311977346263/38200000000000000000000000000000 : ℝ) := by norm_num
    linear_combination (102119623/10000000000000 : ℝ)*(base19) + (50787679/5000000000000 : ℝ)*(base23) + (8639529/50000000000000 : ℝ)*(lower2) + (71367367/50000000000000 : ℝ)*(upper3) + (27182703/25000000000000 : ℝ)*(upper5) + (258061996876947/10000000000000 : ℝ)*(major0) + (258061996876947/10000000000000 : ℝ)*(major1) + (258061996876947/10000000000000 : ℝ)*(major2) + (3502265615954547/100000000000000 : ℝ)*(sp0) + (3502280792140703/100000000000000 : ℝ)*(sp1) + (3502280797583353/100000000000000 : ℝ)*(sp2) + (829475445121953/50000000000000 : ℝ)*(sp3) + (8098691193/50000000000000 : ℝ)*(sp4) + (1404626089/20000000000000 : ℝ)*(sp7) + (1658957913374351/100000000000000 : ℝ)*(f.failure) + (875570453334233/25000000000000 : ℝ)*(f.sum) + (6797091625567/1528000000000000000000000000 : ℝ)*base65 + (28529355106240421/76400000000000000000000000000000 : ℝ)*base67 + (307500113507359579/76400000000000000000000000000000 : ℝ)*base70 + (515067563676159579/76400000000000000000000000000000 : ℝ)*base72 + (6999423498183/1528000000000000000000000000 : ℝ)*base73 + (219902381337359579/76400000000000000000000000000000 : ℝ)*base76 + (49383091206640421/76400000000000000000000000000000 : ℝ)*base77 + (617497264777759579/76400000000000000000000000000000 : ℝ)*base80 + (162569944811/305600000000000000000000000 : ℝ)*base81 + (1/100000000000000 : ℝ)*base83 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base87 + (32335137/10000000000000000000000 : ℝ)*base89 + (32335137/10000000000000000000000 : ℝ)*base91 + (32335137/10000000000000000000000 : ℝ)*base93 + hcertificate_margin
  ·
    have hcertificate_margin : (0 : ℝ) ≤ (63796544796732558578163/15280000000000000000000000000 : ℝ) := by norm_num
    linear_combination (476261747/50000000000000 : ℝ)*(base19) + (1046596213/100000000000000 : ℝ)*(base23) + (25662693/25000000000000 : ℝ)*(upper3) + (11793943/25000000000000 : ℝ)*(lower4) + (54703653/100000000000000 : ℝ)*(upper5) + (2612768946666653/100000000000000 : ℝ)*(major0) + (2612768946666653/100000000000000 : ℝ)*(major1) + (2612768946666653/100000000000000 : ℝ)*(major2) + (2732700751/25000000000000 : ℝ)*(sp1) + (524378531/4000000000000 : ℝ)*(sp2) + (3545912791033227/100000000000000 : ℝ)*(sp4) + (354590090770673/10000000000000 : ℝ)*(sp5) + (1772949317486869/50000000000000 : ℝ)*(sp6) + (209953120390981/12500000000000 : ℝ)*(sp7) + (209953120390981/12500000000000 : ℝ)*(f.failure) + (3545912791033227/100000000000000 : ℝ)*(f.sum) + (29836383691999/15280000000000000000000000000 : ℝ)*base66 + (10541863634071694379/764000000000000000000000000000000 : ℝ)*base67 + (580182261672305621/764000000000000000000000000000000 : ℝ)*base70 + (1903470575660305621/764000000000000000000000000000000 : ℝ)*base72 + (148555351980081/15280000000000000000000000000 : ℝ)*base73 + (3161865968092305621/764000000000000000000000000000000 : ℝ)*base76 + (7764361511059694379/764000000000000000000000000000000 : ℝ)*base77 + (6520133663575694379/764000000000000000000000000000000 : ℝ)*base79 + (48448086492559/15280000000000000000000000000 : ℝ)*base82 + (1/100000000000000 : ℝ)*base85 + (1/100000000000000 : ℝ)*base88 + (13460053/1250000000000000000000 : ℝ)*base90 + (13460053/1250000000000000000000 : ℝ)*base92 + (13460053/1250000000000000000000 : ℝ)*base94 + hcertificate_margin
theorem rectangle_w1363_s2 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (9653/50000 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (3541/50000 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4993/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16023/100000 : ℝ)*pair X i i := by
  exact frame_interval_of_base (base_rectangle_w1363_s2 p A d hA hpa hpb) X hX hsign hratio hlower

end HlawkaSchatten.DiagonalCutoff4
set_option maxHeartbeats 8000000
set_option maxRecDepth 40000
namespace HlawkaSchatten.DiagonalCutoff4
open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff6
theorem rectangle_block_w1363_b0 (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4993/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16023/100000 : ℝ)*pair X i i := by
  have hmain (i : Fin 3) : 0 ≤ pair X i i := (abs_nonneg _).trans (hX.maximal i i)
  have h0 := rectangle_w1363_s0 p A d hA hpa hpb X hX hsign hratio hlower
  have h1 := rectangle_w1363_s1 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h0 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h0 i h hih).1; nlinarith only [hh,hmain i])
  have h2 := rectangle_w1363_s2 p A d hA hpa hpb X hX hsign
    (by intro i h hih; have hh := (h1 i h hih).2; nlinarith only [hh,hmain i])
    (by intro i h hih; have hh := (h1 i h hih).1; nlinarith only [hh,hmain i])
  exact h2
end HlawkaSchatten.DiagonalCutoff4

open HlawkaSchatten.DiagonalConstruction HlawkaSchatten.DiagonalCutoff4 HlawkaSchatten.DiagonalCutoff6

theorem solution (p A d : ℝ) (hA : A ≤ 3) (hpa : (2161/512 : ℝ) ≤ p) (hpb : p ≤ (4323/1024 : ℝ))
    (X : Fin 3 → Fin 3 → ℝ) (hX : Frame p (155556687/100000000 : ℝ) A d X)
    (hsign : ∀ i h, i ≠ h → 0 ≤ pair X i h)
    (hratio : ∀ i h, i ≠ h → |pair X i h| ≤ (2/5 : ℝ)*pair X i i)
    (hlower : ∀ i h, i ≠ h → (0 : ℝ)*pair X i i ≤ pair X i h) :
    ∀ i h, i ≠ h → (4993/50000 : ℝ)*pair X i i ≤ pair X i h ∧ |pair X i h| ≤ (16023/100000 : ℝ)*pair X i i := by
  exact HlawkaSchatten.DiagonalCutoff4.rectangle_block_w1363_b0 p A d hA hpa hpb X hX hsign hratio hlower

#print axioms solution
